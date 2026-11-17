#!/usr/bin/env bash
# The MLP of rust/mlp through Charon and Aeneas: a probe of the crate as it is, and a pilot on a
# variant of it. Not a gate. Everything runs in scratch trees under .work/mlp/pilot/; nothing is
# written to rust/ or lean/.
#
# 1. rust/mlp as it is (as-is/).
#    a. scripts/translate.sh mlp, unchanged command: Aeneas stops at the unsafe module
#       src/fast.rs. Its error is kept.
#    b. The same with EXTRA_CHARON_ARGS="--exclude crate::fast": Aeneas generates Mlp.lean. Lean
#       runs on the file as generated until its first error, which is kept with the time.
#    c. The first table of that file cut to 16 and to 32 of its 113 rows, with the heartbeat
#       limit lifted: time and peak memory of Lean on each.
# 2. The variant (variant/): scripts/mlp_row_consts.py writes the same tables with one `const`
#    per row. src/lib.rs, src/fast.rs and the tests are copied unchanged. Then: cargo test,
#    translate.sh, the nine function definitions compared with those of 1b, the build of the
#    translation and of the proofs in pilot/mlp-row-consts/, their statements and axioms, and
#    the nanoda recheck of the refinement theorems (recheck/). Set MLP_PILOT_RECHECK_COMPOSED=1
#    to recheck the theorem composed with adds_mod_113 as well (recheck-composed/).
#
# Needs toolchain/install.sh, scripts/build.sh (for lean/.lake/packages) and
# scripts/mlp_parent_theorem.sh: the proofs import LeanCheckedNetwork from its scratch project.
# Output: evidence/mlp/pilot/.
source "$(dirname "$0")/common.sh"
need cargo
need lake
need python3
need rsync

out="$EVIDENCE/mlp/pilot"
work="$WORK/mlp/pilot"
parent_project="$WORK/mlp/parent-theorem/project"
pilot_src="$ROOT/pilot/mlp-row-consts"
exclude="--exclude crate::fast"
generated="lean/LcnExec/Translated/Mlp.lean"
rm -rf "$out" "$work"
mkdir -p "$out/as-is" "$out/variant" "$work"
[ -d "$LEAN_DIR/.lake/packages" ] || die "run scripts/build.sh first: no lean/.lake/packages to share"
[ -d "$parent_project/.lake/build" ] || die "run scripts/mlp_parent_theorem.sh first: no $parent_project"

# timed_lean <log> <rss cap, MB> <time limit, s> <stop at first error: yes|no> <lean file>
# Runs Lean on a file in the environment of lean/ and prints "<seconds> s, peak RSS <MB> MB, <how
# it ended>". Lean is stopped at the cap, at the limit, or at the first error when asked to.
timed_lean() {
  local log="$1" cap="$2" limit="$3" first_error="$4" file="$5" start pid rss peak=0 how=""
  start=$(date +%s)
  (cd "$LEAN_DIR" && exec lake env lean "$file") > "$log" 2>&1 &
  pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    rss=$(ps -eo rss=,args= | awk -v f="$file" 'index($0, f) && /bin\/lean / {s += $1} END {print int(s / 1024)}')
    if [ "${rss:-0}" -gt "$peak" ]; then peak=$rss; fi
    if [ "${rss:-0}" -gt "$cap" ]; then how="stopped at the memory cap of $cap MB"
    elif [ $(( $(date +%s) - start )) -gt "$limit" ]; then how="stopped at the time limit of $limit s"
    elif [ "$first_error" = yes ] && grep -q 'error' "$log"; then how="stopped at its first error"
    fi
    if [ -n "$how" ]; then pkill -f "lean $file" || true; break; fi
    sleep 1
  done
  set +e
  wait "$pid"
  local status=$?
  set -e
  echo "$(( $(date +%s) - start )) s, peak RSS $peak MB, ${how:-exit $status}"
}

# A scratch root for scripts/translate.sh: rust/mlp from <crate source>, the pinned tools.
scratch_root() {
  local root="$1" weights="$2"
  mkdir -p "$root/rust/mlp/src" "$root/lean" "$root/toolchain/aeneas"
  cp "$ROOT/rust/rust-toolchain.toml" "$root/rust/"
  cp "$ROOT/rust/mlp/Cargo.toml" "$ROOT/rust/mlp/Cargo.lock" "$root/rust/mlp/"
  cp "$ROOT/rust/mlp/src/lib.rs" "$ROOT/rust/mlp/src/fast.rs" "$root/rust/mlp/src/"
  cp -r "$ROOT/rust/mlp/tests" "$root/rust/mlp/"
  cp "$weights" "$root/rust/mlp/src/weights.rs"
  ln -s "$ROOT/toolchain/bin" "$root/toolchain/bin"
  ln -s "$ROOT/toolchain/aeneas/charon" "$root/toolchain/aeneas/charon"
  cp "$ROOT/toolchain/aeneas/charon-pin" "$root/toolchain/aeneas/charon-pin"
}
translate() {  # translate <root> [extra charon args]: scripts/translate.sh mlp in a scratch root
  ROOT="$1" LEAN_DIR="$1/lean" EVIDENCE="$1/evidence" WORK="$1/.work" EXTRA_CHARON_ARGS="${2:-}" \
    bash "$ROOT/scripts/translate.sh" mlp
}

summary="$out/summary.txt"
{
  echo "date: $(stamp)"
  echo "machine: $(nproc) cores, $(awk '/MemTotal/ {printf "%.0f GiB RAM", $2 / 1048576}' /proc/meminfo)"
  echo "lean: $(cd "$LEAN_DIR" && lean --version)"
} > "$summary"

# 1. rust/mlp as it is.
asis="$work/as-is"
scratch_root "$asis" "$ROOT/rust/mlp/src/weights.rs"
if translate "$asis" > "$out/as-is/translate-without-exclude.log" 2>&1; then
  die "translate.sh mlp succeeded without an exclusion: the probe's premise no longer holds"
fi
tr '\r' '\n' < "$asis/evidence/translate/mlp/aeneas.log" | grep -A2 -m1 '\[Error\]' > "$out/as-is/aeneas-error.txt" \
  || die "no [Error] line in Aeneas's log for rust/mlp"
translate "$asis" "$exclude" > "$out/as-is/translate.log" 2>&1 \
  || die "translate.sh mlp failed with $exclude (evidence/mlp/pilot/as-is/translate.log)"
cp "$asis/$generated" "$work/MlpAsIs.lean"
first_error="$(timed_lean "$out/as-is/lean-as-generated.log" 6000 900 yes "$work/MlpAsIs.lean")"
grep -m1 -A3 'error' "$out/as-is/lean-as-generated.log" > "$out/as-is/lean-first-error.txt" \
  || die "Lean reported no error on the translation of rust/mlp as generated: the probe's premise no longer holds"
# The first table, cut to its first rows, with no heartbeat limit.
python3 - "$asis/$generated" "$work" <<'PY'
import re
import sys

source, dest = sys.argv[1:3]
text = open(source).read()
header = text[: text.index("namespace mlp")].replace("set_option maxHeartbeats 1000000", "set_option maxHeartbeats 0")
table = re.search(r"def weights\.(\w+) : Array \(Array Std\.I8 128#usize\) 113#usize :=\n  Array\.make 113#usize \[\n(.*?)\n    \]\n", text, re.S)
rows = re.findall(r"    Array\.make 128#usize \[\n.*?\n      \]", table.group(2), re.S)
assert len(rows) == 113, len(rows)
for n in (16, 32):
    body = ",\n".join(rows[:n])
    open(f"{dest}/Rows{n}.lean", "w").write(
        f"{header}namespace mlp\ndef rows{n} : Array (Array Std.I8 128#usize) {n}#usize :=\n"
        f"  Array.make {n}#usize [\n{body}\n    ]\nend mlp\n"
    )
PY
rows16="$(timed_lean "$out/as-is/lean-16-rows.log" 6000 900 no "$work/Rows16.lean")"
rows32="$(timed_lean "$out/as-is/lean-32-rows.log" 6000 900 no "$work/Rows32.lean")"
{
  echo
  echo "1. rust/mlp as it is"
  echo "translate.sh mlp, unchanged command: fails in Aeneas (as-is/aeneas-error.txt):"
  sed 's/^/  /' "$out/as-is/aeneas-error.txt"
  echo "translate.sh mlp with EXTRA_CHARON_ARGS=\"$exclude\": $(grep '^generated:' "$out/as-is/translate.log"), $(wc -l < "$asis/$generated") lines, $(grep -c '#i8' "$asis/$generated") lines of i8 literals"
  echo "Lean on that file as generated: $first_error (as-is/lean-first-error.txt):"
  sed 's/^/  /' "$out/as-is/lean-first-error.txt" | cut -c1-300
  echo "Lean on its first table cut to 16 of 113 rows, no heartbeat limit: $rows16"
  echo "Lean on its first table cut to 32 of 113 rows, no heartbeat limit: $rows32"
} >> "$summary"

# 2. The variant: one const per row.
tree="$work/tree"
python3 "$ROOT/scripts/mlp_row_consts.py" "$ROOT/rust/mlp/src/weights.rs" "$work/weights.rs"
scratch_root "$tree" "$work/weights.rs"
python3 - "$ROOT/rust/mlp/src/weights.rs" "$work/weights.rs" > "$out/variant/weights.txt" <<'PY'
import hashlib
import re
import sys

def entries(path):
    text = re.sub(r"//.*", "", open(path).read())
    rows = {m.group(1): m.group(2) for m in re.finditer(r"const (\w+_ROW_\d+): \[i8; HID\] = \[(.*?)\];", text)}
    tables = {}
    for m in re.finditer(r"pub static (\w+): \[\[i8; HID\]; P\] = \[\n(.*?)\n\];", text, re.S):
        body = m.group(2)
        for name, row in rows.items():
            body = re.sub(rf"\b{name}\b", "[" + row + "]", body)
        tables[m.group(1)] = [int(x) for x in re.findall(r"-?\d+", body)]
    return tables

original, variant = entries(sys.argv[1]), entries(sys.argv[2])
for label, path in (("rust/mlp/src/weights.rs", sys.argv[1]), ("the variant's src/weights.rs", sys.argv[2])):
    data = open(path, "rb").read()
    lines = data.count(b"\n")
    print(f"{label}: sha256 {hashlib.sha256(data).hexdigest()}, {lines} lines")
for name in sorted(original):
    same = original[name] == variant.get(name)
    print(f"{name}: {len(original[name])} entries, the variant's are {'the same, entry for entry' if same else 'DIFFERENT'}")
sys.exit(0 if original == variant and len(original) == 3 else 1)
PY
for f in src/lib.rs src/fast.rs Cargo.toml Cargo.lock tests/all_pairs.rs; do
  cmp -s "$ROOT/rust/mlp/$f" "$tree/rust/mlp/$f" || die "the variant's $f differs from rust/mlp/$f"
done
(cd "$tree/rust/mlp" && cargo test --release --locked) > "$out/variant/cargo-test.log" 2>&1 \
  || die "cargo test failed on the variant (evidence/mlp/pilot/variant/cargo-test.log)"
translate "$tree" "$exclude" > "$out/variant/translate.log" 2>&1 \
  || die "translate.sh mlp failed on the variant (evidence/mlp/pilot/variant/translate.log)"
python3 - "$asis/$generated" "$tree/$generated" > "$out/variant/functions.txt" <<'PY'
import re
import sys

def functions(path):
    blocks = [b for b in open(path).read().split("\n\n") if re.search(r"^def (?!weights\.)", b, re.M)]
    return {re.search(r"^def (\S+)", b, re.M).group(1): b for b in blocks}

original, variant = functions(sys.argv[1]), functions(sys.argv[2])
print("definitions other than the constants of weights.rs:", " ".join(original))
print("identical in the translation of the variant:", "yes" if original == variant else "NO")
sys.exit(0 if original == variant and len(original) == 9 else 1)
PY

# The Lake project of the scratch tree: Aeneas's library copied as scripts/plant_wrong_weight.sh
# does, Mathlib shared, LeanCheckedNetwork from the scratch project of mlp_parent_theorem.sh.
mkdir -p "$tree/toolchain/aeneas/backends" "$tree/lean/.lake" "$tree/lean/LcnExec/Mlp" "$tree/gates"
rsync -a "$ROOT/toolchain/aeneas/backends/lean/" "$tree/toolchain/aeneas/backends/lean/"
ln -s "$LEAN_DIR/.lake/packages" "$tree/lean/.lake/packages"
cp "$LEAN_DIR/lean-toolchain" "$tree/lean/"
cp "$GATES/allowlist" "$tree/gates/"
cp "$pilot_src/LcnExec/Mlp/Proofs.lean" "$pilot_src/LcnExec/Mlp/AddsMod113.lean" "$tree/lean/LcnExec/Mlp/"
cat > "$tree/lean/lakefile.lean" <<EOF
import Lake
open Lake DSL

package «lcn-exec-mlp-pilot» where

require aeneas from "../toolchain/aeneas/backends/lean"
require «mlp-parent-theorem» from "$parent_project"

@[default_target]
lean_lib LcnExec where
  globs := #[.submodules \`LcnExec]
EOF
python3 - "$LEAN_DIR/lake-manifest.json" "$tree/lean/lake-manifest.json" "$parent_project" <<'PY'
import json
import sys

manifest = json.load(open(sys.argv[1]))
manifest["name"] = "«lcn-exec-mlp-pilot»"
manifest["packages"].insert(1, {
    "type": "path", "scope": "", "name": "«mlp-parent-theorem»", "manifestFile": "lake-manifest.json",
    "inherited": False, "dir": sys.argv[3], "configFile": "lakefile.lean",
})
json.dump(manifest, open(sys.argv[2], "w"), indent=1)
PY
touch "$work/started"
cd "$tree/lean"
start=$(date +%s)
lake -R build --no-cache LcnExec.Translated.Mlp > "$out/variant/build-translation.log" 2>&1 \
  || die "the translation of the variant does not build (evidence/mlp/pilot/variant/build-translation.log)"
translation_seconds=$(( $(date +%s) - start ))
start=$(date +%s)
lake -R build --no-cache > "$out/variant/build-proofs.log" 2>&1 \
  || die "the pilot proofs do not build (evidence/mlp/pilot/variant/build-proofs.log)"
proofs_seconds=$(( $(date +%s) - start ))
grep -q "Build completed successfully" "$out/variant/build-proofs.log" \
  || die "lake build reported no success line (evidence/mlp/pilot/variant/build-proofs.log)"

cat > "$work/theorems.txt" <<'EOF'
LcnExec.Mlp.Proofs LcnExec.Mlp.E1_eq
LcnExec.Mlp.Proofs LcnExec.Mlp.E2_eq
LcnExec.Mlp.Proofs LcnExec.Mlp.W2_eq
LcnExec.Mlp.Proofs LcnExec.Mlp.predict_eq
LcnExec.Mlp.Proofs LcnExec.Mlp.predict_out_of_range
EOF
echo "LcnExec.Mlp.AddsMod113 LcnExec.Mlp.predict_adds_mod_113" > "$work/theorems-composed.txt"
{
  echo "import LcnExec.Mlp.AddsMod113"
  echo "open Aeneas Aeneas.Std Result"
  cat "$work/theorems.txt" "$work/theorems-composed.txt" | awk '{print "#check @" $2}'
} > "$out/variant/Statements.lean"
lake env lean "$out/variant/Statements.lean" > "$out/variant/statements.txt" 2>&1 \
  || die "lean failed on the statements probe (evidence/mlp/pilot/variant/statements.txt)"
cat "$work/theorems.txt" "$work/theorems-composed.txt" > "$work/theorems-all.txt"
ROOT="$tree" LEAN_DIR="$tree/lean" EVIDENCE="$tree/evidence" WORK="$tree/.work" THEOREMS="$work/theorems-all.txt" \
  bash "$ROOT/scripts/axioms.sh" > "$out/variant/axioms.txt" 2>&1 \
  || die "the axiom audit failed (evidence/mlp/pilot/variant/axioms.txt)"

start=$(date +%s)
ROOT="$tree" LEAN_DIR="$tree/lean" EVIDENCE="$tree/evidence" WORK="$tree/.work" THEOREMS="$work/theorems.txt" \
  RECHECK_OUT="$out/recheck" bash "$ROOT/scripts/recheck.sh" > "$out/variant/recheck.log" 2>&1 \
  || die "the nanoda recheck failed (evidence/mlp/pilot/variant/recheck.log)"
recheck_seconds=$(( $(date +%s) - start ))
composed="not run (set MLP_PILOT_RECHECK_COMPOSED=1)"
if [ "${MLP_PILOT_RECHECK_COMPOSED:-0}" = 1 ]; then
  start=$(date +%s)
  ROOT="$tree" LEAN_DIR="$tree/lean" EVIDENCE="$tree/evidence" WORK="$tree/.work" THEOREMS="$work/theorems-composed.txt" \
    RECHECK_OUT="$out/recheck-composed" bash "$ROOT/scripts/recheck.sh" > "$out/variant/recheck-composed.log" 2>&1 \
    || die "the nanoda recheck of the composed theorem failed (evidence/mlp/pilot/variant/recheck-composed.log)"
  composed="$(( $(date +%s) - start )) s: $(grep 'nanoda' "$out/recheck-composed/summary.txt" | tail -1 | sed 's/^ *//')"
fi
written="$(find "$LEAN_DIR/.lake/packages/" "$parent_project/.lake/build" -newer "$work/started" -type f | head -3)"
[ -z "$written" ] || die "the pilot wrote into shared build products: $written"

{
  echo
  echo "2. The variant: one const per table row (scripts/mlp_row_consts.py)"
  sed 's/^/  /' "$out/variant/weights.txt"
  echo "src/lib.rs, src/fast.rs, Cargo.toml, Cargo.lock, tests/all_pairs.rs: copied unchanged"
  echo "cargo test --release --locked: $(grep -E '^test result' "$out/variant/cargo-test.log" | grep -v ' 0 passed' | paste -sd';' -)"
  echo "translate.sh mlp with EXTRA_CHARON_ARGS=\"$exclude\": $(grep '^generated:' "$out/variant/translate.log"), $(wc -l < "$tree/$generated") lines"
  sed 's/^/  /' "$out/variant/functions.txt"
  echo "lake build LcnExec.Translated.Mlp: $translation_seconds s"
  echo "lake build of the proofs (pilot/mlp-row-consts/LcnExec/Mlp/Proofs.lean, AddsMod113.lean): $proofs_seconds s"
  echo "statements (variant/statements.txt):"
  sed 's/^/  /' "$out/variant/statements.txt"
  echo "axioms (scripts/axioms.sh, variant/axioms.txt):"
  sed 's/^/  /' "$out/variant/axioms.txt"
  echo "nanoda recheck of the five refinement theorems: $recheck_seconds s (recheck/summary.txt)"
  grep -A1 '^LcnExec' "$out/recheck/summary.txt" | grep -v '^--' | sed -E 's/: export.*//; s/^/  /'
  echo "nanoda recheck of predict_adds_mod_113: $composed"
  echo "pilot: ok"
} >> "$summary"
cat "$summary"
