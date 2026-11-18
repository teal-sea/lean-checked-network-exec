#!/usr/bin/env bash
# Gate 4, every row: kernel-check that the Lean model of the fixed-width transformer program
# (pilot/transformer-int/TransformerInt/Model.lean, which mirrors rust/transformer/src/lib.rs stage
# for stage) returns (a + b) % 113 on all 12,769 pairs, then replay the modules with leanchecker.
#
#   scripts/gate4.sh build     generate all 113 rows from a clean directory, build, print axioms
#   scripts/gate4.sh replay    replay every module of the built project with leanchecker
#   JOBS=2 ...                 how many modules build or replay at once (default 2)
#   PARENT=...                 the lean-checked-network checkout (default ../lean-checked-network)
#
# The Lake project is built in .work/gate4 (core Lean, no Mathlib). Evidence goes to evidence/gate4/.
# The theorem is about the Lean model. It says nothing about the Rust until gate 5 proves the Rust
# equal to that model.
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
need lake; need lean; need python3

PARENT="${PARENT:-$ROOT/../lean-checked-network}"
CKPT="$PARENT/transformer/runs/best.npz"
OUT="$WORK/gate4"
EV="$EVIDENCE/gate4"
JOBS="${JOBS:-2}"
G=TransformerInt.Gen
THEOREM="$G.adds_mod_113"
mkdir -p "$EV"

case "${1:-}" in
  build)
    [ -f "$CKPT" ] || die "checkpoint not found: $CKPT"
    rm -rf "$OUT"; mkdir -p "$OUT"
    {
      echo "date $(stamp)"
      (cd "$ROOT/pilot/transformer-int" && lean --version && lake --version)
      python3 --version
      echo "checkpoint sha256 $(sha256sum "$CKPT" | cut -d' ' -f1)"
      echo "repo commit $(git -C "$ROOT" rev-parse HEAD), $(git -C "$ROOT" status --porcelain | wc -l) uncommitted paths"
      for f in scripts/gen_transformer_lean.py scripts/gen_transformer_weights.py scripts/check_transformer_int.py \
               pilot/transformer-int/TransformerInt/Model.lean pilot/transformer-int/TransformerInt/Fast.lean \
               rust/transformer/src/lib.rs rust/transformer/src/weights.rs; do
        echo "sha256 $(sha256sum "$ROOT/$f" | cut -d' ' -f1) $f"
      done
      echo "jobs $JOBS of $(nproc) cores"
    } > "$EV/versions.txt"

    (cd "$ROOT" && python3 scripts/gen_transformer_lean.py "$CKPT" "$OUT" --rows all) > "$EV/generate.log" 2>&1 \
      || { tail -5 "$EV/generate.log" >&2; die "the generator failed"; }
    (cd "$OUT" && find TransformerInt TransformerInt.lean -name '*.lean' | LC_ALL=C sort | xargs sha256sum) \
      > "$EV/generated.sha256"

    if grep -rnwE 'sorry|native_decide' --include='*.lean' "$OUT/TransformerInt" "$OUT/TransformerInt.lean" > "$EV/forbidden-words.txt"; then
      die "sorry or native_decide in the generated project; see $EV/forbidden-words.txt"
    fi

    start=$(date +%s)
    (cd "$OUT" && LEAN_NUM_THREADS="$JOBS" lake build "$G.AllRows") > "$EV/build.log" 2>&1 \
      || { tail -30 "$EV/build.log" >&2; die "lake build failed; see $EV/build.log"; }
    echo "build_wall_seconds $(( $(date +%s) - start ))" > "$EV/timings.txt"

    cat > "$OUT/AxiomsAll.lean" <<EOF
import TransformerInt.Gen.AllRows

#print axioms $THEOREM
#print axioms TransformerInt.fastPredict_sound
#print axioms TransformerInt.Gen.static_ok
#print axioms TransformerInt.Gen.tables_ok
#check @$THEOREM
EOF
    (cd "$OUT" && lake env lean AxiomsAll.lean) > "$EV/axioms.txt" 2>&1 || { cat "$EV/axioms.txt" >&2; die "axiom print failed"; }
    # Every axiom named in the output must be on the allowlist (gates/allowlist, read only).
    bad=0
    for ax in $(grep -o '\[.*\]' "$EV/axioms.txt" | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | sort -u); do
      allowed_axioms | grep -qx "$ax" || { echo "NOT ALLOWED: $ax" >> "$EV/axioms.txt"; bad=1; }
    done
    [ "$bad" -eq 0 ] || die "an axiom outside gates/allowlist; see $EV/axioms.txt"
    grep -q "$THEOREM" "$EV/axioms.txt" || die "the theorem is missing from the axiom print"
    {
      echo "date $(stamp)"
      echo "theorem $THEOREM built by lake build (Lean kernel), 113 row modules"
      grep -c '' "$EV/generated.sha256" | sed 's/^/generated and hand-written Lean files: /'
      cat "$EV/timings.txt"
      echo "axioms:"; sed 's/^/  /' "$EV/axioms.txt"
      echo "replay: not run yet (scripts/gate4.sh replay)"
    } > "$EV/summary.txt"
    cat "$EV/summary.txt"
    ;;
  replay)
    [ -d "$OUT/.lake" ] || die "no built project in $OUT; run: scripts/gate4.sh build"
    mkdir -p "$EV/replay"; rm -f "$EV/replay"/*.log
    # Every module the theorem imports, directly or not: the model, the packed evaluator, the data,
    # the table checks, the 113 rows and the final theorem. Files the generator writes for timing
    # or testing only (Base, Eval, Axioms) are not imported by it, are never built, and are not here.
    python3 - "$OUT" "$G.AllRows" > "$EV/replay-modules.txt" <<'PYEOF_INNER'
import re, sys
from pathlib import Path
out, root = Path(sys.argv[1]), sys.argv[2]
seen, todo = set(), [root]
while todo:
    m = todo.pop()
    if m in seen:
        continue
    f = out / (m.replace(".", "/") + ".lean")
    if not f.exists():
        sys.exit(f"module {m} has no source file in {out}")
    seen.add(m)
    for line in f.read_text().splitlines():
        g = re.match(r"\s*(?:public\s+)?import\s+(TransformerInt[\w.]*)\s*$", line)
        if g:
            todo.append(g.group(1))
print("\n".join(sorted(seen)))
PYEOF_INNER
    start=$(date +%s)
    export OUT EV
    xargs -P "$JOBS" -I{} bash -c 'cd "$OUT" && if lake env leanchecker "$1" > "$EV/replay/$1.log" 2>&1; then echo "ok $1"; else echo "FAIL $1"; fi' _ {} \
        < "$EV/replay-modules.txt" > "$EV/replay-results.txt" || true
    wall=$(( $(date +%s) - start ))
    total=$(grep -c '' "$EV/replay-modules.txt"); ok=$(grep -c '^ok ' "$EV/replay-results.txt" || true)
    {
      echo "date $(stamp)"
      echo "leanchecker replayed $ok of $total modules, $wall wall seconds, $JOBS at once"
      grep '^FAIL ' "$EV/replay-results.txt" || true
    } > "$EV/replay-summary.txt"
    sed -i '/^replay: /d' "$EV/summary.txt"
    sed 's/^/replay: /' "$EV/replay-summary.txt" >> "$EV/summary.txt"
    cat "$EV/replay-summary.txt"
    [ "$ok" -eq "$total" ] || die "leanchecker rejected or could not replay some modules"
    ;;
  *)
    sed -n '2,13p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac
