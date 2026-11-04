#!/usr/bin/env bash
# Wrong-data control: copy the tree, perturb one weight constant, rerun build, axioms and diff
# on the copy. The script FAILS if the planted bug is NOT caught by at least one of them.
#
# Smoke test target: the accumulator's initial value in the translated `smoke.sum`, 0#u32 -> 1#u32.
# The copy gets its own copy of Aeneas's Lean library (builds there must not write into this
# checkout) and shares lean/.lake/packages (Mathlib) through a symlink; the script fails if
# anything under the shared packages is written during the run. Output: evidence/plant/.
source "$(dirname "$0")/common.sh"
need rsync

PLANT_FILE="lean/LcnExec/Translated/Smoke.lean"
PLANT_FROM="sum_loop xs 0#u32 0#usize"
PLANT_TO="sum_loop xs 1#u32 0#usize"

out="$EVIDENCE/plant"
copy="$WORK/plant/tree"
rm -rf "$out" "$WORK/plant"
mkdir -p "$out" "$copy"
[ -d "$LEAN_DIR/.lake/packages" ] || die "run scripts/build.sh first: no lean/.lake/packages to share"

rsync -a --exclude .git --exclude .work --exclude evidence --exclude toolchain \
  --exclude .lake --exclude target "$ROOT/" "$copy/"
mkdir -p "$copy/toolchain/aeneas/backends"
rsync -a "$ROOT/toolchain/aeneas/backends/lean/" "$copy/toolchain/aeneas/backends/lean/"
mkdir -p "$copy/lean/.lake"
ln -s "$LEAN_DIR/.lake/packages" "$copy/lean/.lake/packages"
touch "$WORK/plant/started"

target="$copy/$PLANT_FILE"
count=$(grep -cF "$PLANT_FROM" "$target" || true)
[ "$count" -eq 1 ] || die "expected exactly one '$PLANT_FROM' in $PLANT_FILE, found $count"
FROM="$PLANT_FROM" TO="$PLANT_TO" perl -0pi -e 's/\Q$ENV{FROM}\E/$ENV{TO}/' "$target"
grep -qF "$PLANT_TO" "$target" || die "the perturbation was not applied"
diff -u "$ROOT/$PLANT_FILE" "$target" --label "original/$PLANT_FILE" --label "planted/$PLANT_FILE" \
  > "$out/planted.diff" || true

caught=()
{ echo "date: $(stamp)"; echo "planted: $PLANT_FILE: '$PLANT_FROM' -> '$PLANT_TO'"; } > "$out/summary.txt"
for stage in build axioms diff; do
  set +e
  ROOT="$copy" EVIDENCE="$copy/evidence" WORK="$copy/.work" bash "$copy/scripts/$stage.sh" \
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
written="$(find "$LEAN_DIR/.lake/packages/" -newer "$WORK/plant/started" -type f | head -3)"
[ -z "$written" ] || die "the control wrote into the shared lean/.lake/packages: $written"
if [ "${#caught[@]}" -eq 0 ]; then
  echo "plant: FAIL, the planted wrong weight was NOT caught" >> "$out/summary.txt"
  cat "$out/summary.txt"
  die "the planted wrong weight was not caught by build, axioms or diff"
fi
echo "plant: ok, caught by: ${caught[*]}" >> "$out/summary.txt"
cat "$out/summary.txt"
