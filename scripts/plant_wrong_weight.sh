#!/usr/bin/env bash
# Wrong-data control: copy the tree, perturb one weight constant, rerun build, axioms and diff
# on the copy. The script FAILS if the planted bug is NOT caught by at least one of them.
# Usage: scripts/plant_wrong_weight.sh [smoke|adder|adder-off-by-one]    (default: smoke)
#   smoke             The accumulator's initial value in the translated `smoke.sum`,
#                     0#u32 -> 1#u32.
#   adder             One weight in the translated `adder`, WOA: 125 -> 25 (a dropped digit).
#                     The proofs must fail, and the translation's evaluator must disagree with
#                     the Rust binary: the script fails unless build and diff both catch it.
#   adder-off-by-one  WOA: 125 -> 124. No output of the network changes (the smallest
#                     pre-activation on a reachable transition is 27 in absolute value), so
#                     the diff cannot see it; the proofs must still fail.
# The copy gets its own copy of Aeneas's Lean library (builds there must not write into this
# checkout) and shares lean/.lake/packages (Mathlib) through a symlink; the script fails if
# anything under the shared packages is written during the run.
# Output: evidence/plant/ for smoke, evidence/plant-<target>/ otherwise.
source "$(dirname "$0")/common.sh"
need rsync

target="${1:-smoke}"
# must_catch: the stages that have to catch the planted bug, beyond "at least one".
must_catch=()
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
  *) die "usage: plant_wrong_weight.sh [smoke|adder|adder-off-by-one]" ;;
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

caught=()
{ echo "date: $(stamp)"; echo "planted: $PLANT_FILE: '$PLANT_FROM' -> '$PLANT_TO'"; } > "$out/summary.txt"
for stage in build axioms diff; do
  args=()
  if [ "$stage" = diff ]; then args=("$diff_target"); fi
  set +e
  ROOT="$copy" EVIDENCE="$copy/evidence" WORK="$copy/.work" bash "$copy/scripts/$stage.sh" "${args[@]}" \
    > "$out/$stage.log" 2>&1
  status=$?
  set -e
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
