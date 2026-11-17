#!/usr/bin/env bash
# Gate 1A, the recurrent adder: run every check on the theorems of
# lean/LcnExec/Adder/Proofs.lean and keep the outputs under evidence/gate1a/.
#
# gates/ needs the owner's review (README.md), so this script writes nothing there. The theorem
# list the gates would check, gates/theorems.txt plus the gate 1A theorems, goes to
# evidence/gate1a/proposed-theorems.txt and reaches the scripts through THEOREMS.
#
# Steps, in order. They are the steps of gates/ci.sh on the proposed list, with the adder's
# translation before them and its diff and its wrong-weight controls after them:
#   translate.sh adder       needs the pinned tools of toolchain/install.sh
#   translate-lib-only       the crate without src/bin/ translates to the same Lean file
#   lean-grep                the grep of gates/ci.sh for forbidden words in lean/
#   build.sh
#   statements               `#check` of every proposed theorem, as Lean prints it
#   axioms.sh, recheck.sh    on the proposed list
#   diff.sh adder
#   plant_wrong_weight.sh    smoke, adder, adder-off-by-one, adder-rust
#   gates/ci.sh              unmodified, on gates/theorems.txt, evidence in evidence/gate1a/ci/
#   files                    line counts and hashes of the files a reviewer reads
# Output: evidence/gate1a/; wall-clock seconds per step in evidence/gate1a/timings.txt.
source "$(dirname "$0")/common.sh"
need lake

export EVIDENCE="$ROOT/evidence/gate1a"
export THEOREMS="$EVIDENCE/proposed-theorems.txt"
mkdir -p "$EVIDENCE"

{
  cat "$GATES/theorems.txt"
  cat <<'EOF'
# Gate 1A (proposed, not yet in gates/theorems.txt): Aeneas's translation of rust/adder returns
# ok of what RnnAdder computes on RnnAdder.Trained.net, for every input.
# The translated constants of rust/adder/src/weights.rs are the entries of RnnAdder.Trained.net.
LcnExec.Adder.Proofs LcnExec.Adder.rustNet_eq
# step, out, carry.
LcnExec.Adder.Proofs LcnExec.Adder.step_eq
LcnExec.Adder.Proofs LcnExec.Adder.out_eq
LcnExec.Adder.Proofs LcnExec.Adder.carry_eq
# add_bits: equal lengths (any length), then differing lengths.
LcnExec.Adder.Proofs LcnExec.Adder.add_bits_eq
LcnExec.Adder.Proofs LcnExec.Adder.add_bits_len_ne
# add_bits composed with RnnAdder.Trained.sums_correct, carry_correct and adds.
LcnExec.Adder.Proofs LcnExec.Adder.add_bits_ripple
LcnExec.Adder.Proofs LcnExec.Adder.add_bits_adds
# add_u64: against RnnAdder, then as 64-bit addition with carry out.
LcnExec.Adder.Proofs LcnExec.Adder.add_u64_net_eq
LcnExec.Adder.Proofs LcnExec.Adder.add_u64_eq
EOF
} > "$THEOREMS"

timings="$EVIDENCE/timings.txt"
echo "date: $(stamp); machine: $(nproc) cores, $(awk '/MemTotal/ {printf "%.0f GiB RAM", $2 / 1048576}' /proc/meminfo); load average at the start (1, 5, 15 min): $(cut -d' ' -f1-3 /proc/loadavg)" > "$timings"
# step <name> <command...>: run one step and record its wall-clock time. A failing step stops
# the run (set -e), and the exit trap names it.
current=""
trap 'if [ -n "$current" ]; then echo "FAIL (gate1a.sh): step $current failed" >&2; fi' EXIT
step() {
  local start
  current="$1"
  shift
  start=$(date +%s)
  echo "== $current"
  "$@"
  echo "$current: $(( $(date +%s) - start )) s" >> "$timings"
  current=""
}

# rust/adder/src/bin/adder_eval.rs is the harness of the diff, not part of the library. Check
# that it does not change the translation: translate a copy of the crate without src/bin/ and
# compare the generated Lean file byte for byte. (The LLBC file embeds its own path, so its hash
# differs between two places and is not compared.)
translate_lib_only() {
  local out="$EVIDENCE/translate-lib-only" scratch="$WORK/gate1a/lib-only"
  local generated="lean/LcnExec/Translated/Adder.lean"
  rm -rf "$out" "$scratch"
  mkdir -p "$out" "$scratch/rust/adder" "$scratch/lean"
  cp "$ROOT/rust/rust-toolchain.toml" "$scratch/rust/"
  cp "$ROOT/rust/adder/Cargo.toml" "$ROOT/rust/adder/Cargo.lock" "$scratch/rust/adder/"
  mkdir "$scratch/rust/adder/src"
  cp "$ROOT"/rust/adder/src/*.rs "$scratch/rust/adder/src/"
  ln -s "$ROOT/toolchain" "$scratch/toolchain"
  echo "crate copied without src/bin/: $(cd "$scratch/rust/adder" && find . -type f | LC_ALL=C sort | tr '\n' ' ')" \
    > "$out/result.txt"
  ROOT="$scratch" LEAN_DIR="$scratch/lean" EVIDENCE="$scratch/evidence" WORK="$scratch/.work" \
    bash "$ROOT/scripts/translate.sh" adder > "$out/translate.log" 2>&1 \
    || die "translate.sh failed on the crate without src/bin/ (evidence/gate1a/translate-lib-only/translate.log)"
  {
    echo "with src/bin/:    $generated sha256 $(sha256sum < "$ROOT/$generated" | cut -c1-64)"
    echo "without src/bin/: $generated sha256 $(sha256sum < "$scratch/$generated" | cut -c1-64)"
  } >> "$out/result.txt"
  if cmp -s "$ROOT/$generated" "$scratch/$generated"; then
    echo "translate-lib-only: ok, the two files are identical" >> "$out/result.txt"
  else
    echo "translate-lib-only: FAIL, the two files differ" >> "$out/result.txt"
    cat "$out/result.txt"
    die "src/bin/ changes the translation of rust/adder"
  fi
  cat "$out/result.txt"
}

lean_grep() {
  local out="$EVIDENCE/lean-grep.txt"
  if grep -rnwE 'sorry|native_decide' --include='*.lean' --exclude-dir=.lake "$ROOT/lean" > "$out"; then
    die "sorry or native_decide in the Lean tree (evidence/gate1a/lean-grep.txt)"
  fi
  echo "grep -rnwE 'sorry|native_decide' over $(find "$ROOT/lean" -name '*.lean' -not -path '*/.lake/*' | wc -l) .lean files under lean/: no match" | tee "$out"
}

# The statement of every proposed theorem as Lean prints it. `↑x` is a coercion: `Array.val`
# and `Slice.val` (the list of entries), `UScalar.val` (the number).
statements() {
  local out="$EVIDENCE/statements"
  rm -rf "$out"
  mkdir -p "$out"
  {
    theorems | awk '{print "import " $1}' | sort -u
    echo "open Aeneas Aeneas.Std Result"
    theorems | awk '{print "#check @" $2}'
  } > "$out/Statements.lean"
  (cd "$LEAN_DIR" && lake env lean "$out/Statements.lean") > "$out/statements.txt" 2>&1 \
    || die "lean failed on the statements probe (evidence/gate1a/statements/statements.txt)"
  # One statement per theorem: its first line starts in column 0, the rest are indented.
  [ "$(grep -c '^[^ ]' "$out/statements.txt")" -eq "$(theorems | wc -l)" ] \
    || die "the statements probe did not print one statement per theorem"
  cat "$out/statements.txt"
}

# gates/ci.sh as it is, on its own theorem list: the gate sequence still passes on this tree.
gates_ci() {
  mkdir -p "$EVIDENCE/ci"
  env -u THEOREMS EVIDENCE="$EVIDENCE/ci" "$ROOT/gates/ci.sh" > "$EVIDENCE/ci/ci.log" 2>&1 \
    || die "gates/ci.sh failed (evidence/gate1a/ci/ci.log)"
  tail -1 "$EVIDENCE/ci/ci.log"
}

files() {
  local out="$EVIDENCE/files.txt" f
  {
    echo "# lines, sha256, path: the files a reviewer of gate 1A reads"
    for f in rust/adder/src/lib.rs rust/adder/src/weights.rs lean/LcnExec/Translated/Adder.lean \
      lean/LcnExec/Adder/Proofs.lean lean/RnnAdder/Network.lean lean/RnnAdder/Trained.lean; do
      echo "$(wc -l < "$ROOT/$f") $(sha256sum < "$ROOT/$f" | cut -c1-64) $f"
    done
    echo "# lines, sha256, path: the evaluators and the scripts of the checks"
    for f in rust/adder/src/bin/adder_eval.rs lean/LcnExec/Adder/Io.lean lean/LcnExec/Adder/Main.lean \
      lean/LcnExec/Adder/NetMain.lean lean/lakefile.lean scripts/inputs.py scripts/translate.sh \
      scripts/build.sh scripts/axioms.sh scripts/recheck.sh scripts/diff.sh \
      scripts/plant_wrong_weight.sh scripts/gate1a.sh scripts/common.sh; do
      echo "$(wc -l < "$ROOT/$f") $(sha256sum < "$ROOT/$f" | cut -c1-64) $f"
    done
  } > "$out"
  cat "$out"
}

step translate "$ROOT/scripts/translate.sh" adder
step translate-lib-only translate_lib_only
step lean-grep lean_grep
step build "$ROOT/scripts/build.sh"
step statements statements
step axioms "$ROOT/scripts/axioms.sh"
step recheck "$ROOT/scripts/recheck.sh"
step diff-adder "$ROOT/scripts/diff.sh" adder
step plant-smoke "$ROOT/scripts/plant_wrong_weight.sh"
step plant-adder "$ROOT/scripts/plant_wrong_weight.sh" adder
step plant-adder-off-by-one "$ROOT/scripts/plant_wrong_weight.sh" adder-off-by-one
step plant-adder-rust "$ROOT/scripts/plant_wrong_weight.sh" adder-rust
step ci gates_ci
step files files
echo "gate1a: ok" | tee -a "$timings"
