#!/usr/bin/env bash
# Compile-and-diff: build the Lean evaluators as native binaries (lake) and the Rust binary
# (cargo, production toolchain from rust/rust-toolchain.toml), run them on the same seeded
# inputs, and fail on any difference.
# Usage: scripts/diff.sh [smoke|adder]    (default: smoke)
#   smoke  20 random u32 slices for each length 0..64. One Lean evaluator: the translated `sum`
#          (smoke_eval).
#   adder  The cases of `scripts/inputs.py adder`. Two Lean evaluators, each compared with the
#          Rust binary: the translated `add_bits` and `add_u64` (adder_eval), and the Lean
#          network RnnAdder.Trained.net (adder_net_eval).
# Output: evidence/diff/<target>/.
source "$(dirname "$0")/common.sh"
need cargo
need lake
need python3

target="${1:-smoke}"
case "$target" in
  smoke) lean_exes=(smoke_eval) ;;
  adder) lean_exes=(adder_eval adder_net_eval) ;;
  *) die "usage: diff.sh [smoke|adder]" ;;
esac
# With one Lean evaluator the summary lines carry no name; with several, each line names its own.
label() { if [ "${#lean_exes[@]}" -gt 1 ]; then echo " ($1)"; fi; }
suffix() { if [ "${#lean_exes[@]}" -gt 1 ]; then echo "-$1"; fi; }

SEED="${SEED:-20261104}"
out="$EVIDENCE/diff/$target"
work="$WORK/diff/$target"
rm -rf "$out" "$work"
mkdir -p "$out" "$work"

(cd "$ROOT/rust/$target" && cargo build --release --locked) > "$out/cargo-build.log" 2>&1 \
  || die "cargo build failed (evidence/diff/$target/cargo-build.log)"
rust_bin="$ROOT/rust/$target/target/release/${target}_eval"
(cd "$LEAN_DIR" && lake -R build --no-cache "${lean_exes[@]}") > "$out/lake-build.log" 2>&1 \
  || die "lake build ${lean_exes[*]} failed (evidence/diff/$target/lake-build.log)"
[ -x "$rust_bin" ] || die "no Rust binary at ${rust_bin#"$ROOT"/}"
for exe in "${lean_exes[@]}"; do
  [ -x "$LEAN_DIR/.lake/build/bin/$exe" ] || die "no Lean binary at ${LEAN_DIR#"$ROOT"/}/.lake/build/bin/$exe"
done

python3 "$ROOT/scripts/inputs.py" "$target" "$SEED" > "$work/inputs.txt"
lines=$(wc -l < "$work/inputs.txt")
[ "$lines" -gt 0 ] || die "the input generator produced nothing"
"$rust_bin" < "$work/inputs.txt" > "$work/rust.out" || die "the Rust binary exited nonzero"
got=$(wc -l < "$work/rust.out")
[ "$got" -eq "$lines" ] || die "rust binary printed $got lines for $lines inputs"
for exe in "${lean_exes[@]}"; do
  "$LEAN_DIR/.lake/build/bin/$exe" < "$work/inputs.txt" > "$work/$exe.out" \
    || die "the Lean binary$(label "$exe") exited nonzero"
  got=$(wc -l < "$work/$exe.out")
  [ "$got" -eq "$lines" ] || die "lean binary$(label "$exe") printed $got lines for $lines inputs"
done

{
  echo "date: $(stamp)"
  echo "seed: $SEED; inputs: $lines lines, sha256 $(sha256sum < "$work/inputs.txt" | cut -c1-64)"
  echo "rust: $(cd "$ROOT/rust/$target" && rustc --version), binary sha256 $(sha256sum < "$rust_bin" | cut -c1-64)"
  for exe in "${lean_exes[@]}"; do
    echo "lean$(label "$exe"): $(cd "$LEAN_DIR" && lean --version), binary sha256 $(sha256sum < "$LEAN_DIR/.lake/build/bin/$exe" | cut -c1-64)"
  done
  echo "outputs (rust): $(cut -d' ' -f1-2 "$work/rust.out" | sed -E 's/^(ok|some|none) .*/\1/' | sort | uniq -c | awk '{$1=$1};1' | paste -sd, -)"
} > "$out/summary.txt"

disagree=()
for exe in "${lean_exes[@]}"; do
  if cmp -s "$work/rust.out" "$work/$exe.out"; then
    echo "mismatches$(label "$exe"): 0 of $lines" >> "$out/summary.txt"
    continue
  fi
  mismatches="$out/mismatches$(suffix "$exe").txt"
  paste -d'|' "$work/inputs.txt" "$work/rust.out" "$work/$exe.out" \
    | awk -F'|' '$2 != $3 {print NR": input [" $1 "] rust [" $2 "] lean [" $3 "]"}' > "$mismatches"
  echo "mismatches$(label "$exe"): $(wc -l < "$mismatches") of $lines" >> "$out/summary.txt"
  disagree+=("$(wc -l < "$mismatches") of $lines inputs$(label "$exe")")
done
cat "$out/summary.txt"
if [ "${#disagree[@]}" -gt 0 ]; then
  head -5 "$out"/mismatches*.txt
  die "Rust and Lean binaries disagree on $(IFS=,; echo "${disagree[*]}" | sed 's/,/, on /g')"
fi
