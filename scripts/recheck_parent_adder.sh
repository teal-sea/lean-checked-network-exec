#!/usr/bin/env bash
# Gate 0(d): nanoda rechecks the existing adder theorem in lean-checked-network.
# Builds the parent's rnn/lean at the pinned commit with its own toolchain, then runs
# scripts/recheck.sh on RnnAdder.Trained.{sums_correct, carry_correct, adds} twice: with the
# nanoda_bin shipped in the parent's toolchain, and with the one shipped in this repo's
# toolchain (same export, so this also records whether that nanoda accepts it).
# Output: evidence/parent-adder/.
source "$(dirname "$0")/common.sh"
need git
need lake

out="$EVIDENCE/parent-adder"
work="$WORK/parent-adder"
rm -rf "$out" "$work"
mkdir -p "$out" "$work"

git clone --quiet --filter=blob:none "$PARENT_URL" "$work/parent"
git -C "$work/parent" checkout --quiet "$PARENT_REV"
project="$work/parent/rnn/lean"
{
  echo "date: $(stamp)"
  echo "parent: $PARENT_URL @ $PARENT_REV, rnn/lean, toolchain $(cat "$project/lean-toolchain")"
} > "$out/summary.txt"
(cd "$project" && lake build) > "$out/build.log" 2>&1 \
  || die "lake build of the parent's rnn/lean failed (evidence/parent-adder/build.log)"
grep -q "Build completed successfully" "$out/build.log" || die "no success line in the parent build"

printf '%s\n' \
  "RnnAdder.Trained RnnAdder.Trained.sums_correct" \
  "RnnAdder.Trained RnnAdder.Trained.carry_correct" \
  "RnnAdder.Trained RnnAdder.Trained.adds" > "$work/theorems.txt"

parent_prefix="$(cd "$project" && lean --print-prefix)"
our_prefix="$(cd "$ROOT/lean" && lean --print-prefix)"
for nanoda in "$parent_prefix/bin/nanoda_bin" "$our_prefix/bin/nanoda_bin"; do
  label="$(basename "$(dirname "$(dirname "$nanoda")")")"
  LEAN_DIR="$project" THEOREMS="$work/theorems.txt" NANODA="$nanoda" \
    RECHECK_OUT="$out/nanoda-from-$label" "$ROOT/scripts/recheck.sh" \
    > "$out/recheck-$label.log" 2>&1 \
    || die "recheck with $nanoda failed (evidence/parent-adder/recheck-$label.log)"
  echo "nanoda from $label ($("$nanoda" -h 2>&1 | head -1)): $(grep -c 'no typechecker errors' "$out/nanoda-from-$label/summary.txt") of 3 theorems, no typechecker errors" >> "$out/summary.txt"
done
cat "$out/summary.txt"
