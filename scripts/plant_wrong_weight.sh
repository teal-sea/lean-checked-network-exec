#!/usr/bin/env bash
# Wrong-data control: copy the tree, perturb one weight constant, rerun build, axioms and diff
# on the copy. The script FAILS if the planted bug is NOT caught by at least one of them.
# Usage: scripts/plant_wrong_weight.sh [smoke|adder|adder-off-by-one|adder-rust]    (default: smoke)
#   smoke             The accumulator's initial value in the translated `smoke.sum`,
#                     0#u32 -> 1#u32.
#   adder             One weight in the translated `adder`, WOA: 125 -> 25 (a dropped digit).
#                     The proofs must fail, and the translation's evaluator must disagree with
#                     the Rust binary: the script fails unless build and diff both catch it.
#   adder-off-by-one  WOA: 125 -> 124. A change this small is not expected to flip a threshold
#                     (lean/RnnAdder/Trained.lean reports 27 as the smallest pre-activation on
#                     a reachable transition, in absolute value), so the diff may not see it;
#                     the proofs must still fail: the script fails unless build catches it.
#   adder-rust        The same weight in the Rust source, rust/adder/src/weights.rs of the copy,
#                     WOA: 125 -> 25; the copy's crate is then translated again with this
#                     checkout's pinned tools (toolchain/install.sh). The proofs must fail, and
#                     the Rust binary must disagree with the Lean network: the script fails
#                     unless build and diff both catch it.
# The copy gets its own copy of Aeneas's Lean library (builds there must not write into this
# checkout) and shares lean/.lake/packages (Mathlib) through a symlink; the script fails if
# anything under the shared packages is written during the run.
# Output: evidence/plant/ for smoke, evidence/plant-<target>/ otherwise: the planted change, each
# stage's log, the Lean errors of the build (build-errors.txt), and summary.txt.
source "$(dirname "$0")/common.sh"
need rsync

target="${1:-smoke}"
# must_catch: the stages that have to catch the planted bug, beyond "at least one".
# retranslate: the crate to translate again in the copy, when the planted file is Rust source.
must_catch=()
retranslate=""
case "$target" in
  smoke)
    PLANT_FILE="lean/LcnExec/Translated/Smoke.lean"
    PLANT_FROM="sum_loop xs 0#u32 0#usize"
    PLANT_TO="sum_loop xs 1#u32 0#usize"
    diff_target=smoke
    name=plant
    ;;
  adder)
    PLANT_FILE="lean/LcnExec/Translated/Adder.lean"
    PLANT_FROM="def weights.WOA : Std.I32 := 125#i32"
    PLANT_TO="def weights.WOA : Std.I32 := 25#i32"
    diff_target=adder
    name=plant-adder
    must_catch=(build diff)
    ;;
  adder-off-by-one)
    PLANT_FILE="lean/LcnExec/Translated/Adder.lean"
    PLANT_FROM="def weights.WOA : Std.I32 := 125#i32"
    PLANT_TO="def weights.WOA : Std.I32 := 124#i32"
    diff_target=adder
    name=plant-adder-off-by-one
    must_catch=(build)
    ;;
  adder-rust)
    PLANT_FILE="rust/adder/src/weights.rs"
    PLANT_FROM="pub const WOA: i32 = 125;"
    PLANT_TO="pub const WOA: i32 = 25;"
    diff_target=adder
    name=plant-adder-rust
    must_catch=(build diff)
    retranslate=adder
    ;;
  *) die "usage: plant_wrong_weight.sh [smoke|adder|adder-off-by-one|adder-rust]" ;;
esac

out="$EVIDENCE/$name"
copy="$WORK/$name/tree"
rm -rf "$out" "$WORK/$name"
mkdir -p "$out" "$copy"
[ -d "$LEAN_DIR/.lake/packages" ] || die "run scripts/build.sh first: no lean/.lake/packages to share"

rsync -a --exclude .git --exclude .work --exclude evidence --exclude toolchain \
  --exclude .lake --exclude target "$ROOT/" "$copy/"
mkdir -p "$copy/toolchain/aeneas/backends"
rsync -a "$ROOT/toolchain/aeneas/backends/lean/" "$copy/toolchain/aeneas/backends/lean/"
mkdir -p "$copy/lean/.lake"
ln -s "$LEAN_DIR/.lake/packages" "$copy/lean/.lake/packages"
touch "$WORK/$name/started"

planted="$copy/$PLANT_FILE"
count=$(grep -cF "$PLANT_FROM" "$planted" || true)
[ "$count" -eq 1 ] || die "expected exactly one '$PLANT_FROM' in $PLANT_FILE, found $count"
FROM="$PLANT_FROM" TO="$PLANT_TO" perl -0pi -e 's/\Q$ENV{FROM}\E/$ENV{TO}/' "$planted"
grep -qF "$PLANT_TO" "$planted" || die "the perturbation was not applied"
diff -u "$ROOT/$PLANT_FILE" "$planted" --label "original/$PLANT_FILE" --label "planted/$PLANT_FILE" \
  > "$out/planted.diff" || true

{ echo "date: $(stamp)"; echo "planted: $PLANT_FILE: '$PLANT_FROM' -> '$PLANT_TO'"; } > "$out/summary.txt"
if [ -n "$retranslate" ]; then
  generated="lean/LcnExec/Translated/${retranslate^}.lean"
  mkdir -p "$copy/toolchain/aeneas"
  ln -s "$ROOT/toolchain/bin" "$copy/toolchain/bin"
  ln -s "$ROOT/toolchain/aeneas/charon" "$copy/toolchain/aeneas/charon"
  cp "$ROOT/toolchain/aeneas/charon-pin" "$copy/toolchain/aeneas/charon-pin"
  ROOT="$copy" EVIDENCE="$copy/evidence" WORK="$copy/.work" bash "$copy/scripts/translate.sh" "$retranslate" \
    > "$out/translate.log" 2>&1 || die "translate.sh failed on the planted copy (${out#"$ROOT"/}/translate.log)"
  diff -u "$ROOT/$generated" "$copy/$generated" --label "original/$generated" --label "planted/$generated" \
    >> "$out/planted.diff" || true
  echo "translated again: $generated differs from the original in $(diff "$ROOT/$generated" "$copy/$generated" | grep -c '^[<>]') lines" >> "$out/summary.txt"
fi

caught=()
for stage in build axioms diff; do
  args=()
  if [ "$stage" = diff ]; then args=("$diff_target"); fi
  set +e
  ROOT="$copy" EVIDENCE="$copy/evidence" WORK="$copy/.work" bash "$copy/scripts/$stage.sh" "${args[@]}" \
    > "$out/$stage.log" 2>&1
  status=$?
  set -e
  # build.sh keeps Lake's log in the copy's own evidence: keep the failed jobs and their errors.
  if [ "$stage" = build ] && [ -f "$copy/evidence/build/build.log" ]; then
    sed -n '/^✖/,$p' "$copy/evidence/build/build.log" | grep -v '^trace: ' | head -200 \
      > "$out/build-errors.txt" || true
  fi
  if [ "$status" -ne 0 ]; then
    caught+=("$stage")
    echo "$stage: exit $status, caught: $(grep -E '^FAIL|error' "$out/$stage.log" | head -2 | tr '\n' ' ')" >> "$out/summary.txt"
  else
    echo "$stage: exit 0, not caught" >> "$out/summary.txt"
  fi
done
written="$(find "$LEAN_DIR/.lake/packages/" -newer "$WORK/$name/started" -type f | head -3)"
[ -z "$written" ] || die "the control wrote into the shared lean/.lake/packages: $written"
if [ "${#caught[@]}" -eq 0 ]; then
  echo "plant: FAIL, the planted wrong weight was NOT caught" >> "$out/summary.txt"
  cat "$out/summary.txt"
  die "the planted wrong weight was not caught by build, axioms or diff"
fi
for stage in "${must_catch[@]}"; do
  case " ${caught[*]} " in
    *" $stage "*) ;;
    *)
      echo "plant: FAIL, the planted wrong weight was not caught by $stage" >> "$out/summary.txt"
      cat "$out/summary.txt"
      die "the planted wrong weight was not caught by $stage"
      ;;
  esac
done
echo "plant: ok, caught by: ${caught[*]}" >> "$out/summary.txt"
cat "$out/summary.txt"
