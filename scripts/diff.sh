#!/usr/bin/env bash
# Compile-and-diff: build the Lean evaluator as a native binary (lake) and the Rust binary
# (cargo, production toolchain from rust/rust-toolchain.toml), run both on the same seeded
# inputs, and fail on any difference. Smoke test: 20 random u32 slices for each length 0..64.
# Output: evidence/diff/smoke/.
source "$(dirname "$0")/common.sh"
need cargo
need lake
need python3

SEED="${SEED:-20261104}"
out="$EVIDENCE/diff/smoke"
work="$WORK/diff/smoke"
rm -rf "$out" "$work"
mkdir -p "$out" "$work"

(cd "$ROOT/rust/smoke" && cargo build --release --locked) > "$out/cargo-build.log" 2>&1 \
  || die "cargo build failed (evidence/diff/smoke/cargo-build.log)"
rust_bin="$ROOT/rust/smoke/target/release/smoke_eval"
(cd "$LEAN_DIR" && lake -R build --no-cache smoke_eval) > "$out/lake-build.log" 2>&1 \
  || die "lake build smoke_eval failed (evidence/diff/smoke/lake-build.log)"
lean_bin="$LEAN_DIR/.lake/build/bin/smoke_eval"
[ -x "$rust_bin" ] || die "no Rust binary at ${rust_bin#"$ROOT"/}"
[ -x "$lean_bin" ] || die "no Lean binary at ${lean_bin#"$ROOT"/}"

python3 "$ROOT/scripts/inputs.py" smoke "$SEED" > "$work/inputs.txt"
lines=$(wc -l < "$work/inputs.txt")
[ "$lines" -gt 0 ] || die "the input generator produced nothing"
"$rust_bin" < "$work/inputs.txt" > "$work/rust.out" || die "the Rust binary exited nonzero"
"$lean_bin" < "$work/inputs.txt" > "$work/lean.out" || die "the Lean binary exited nonzero"
for side in rust lean; do
  got=$(wc -l < "$work/$side.out")
  [ "$got" -eq "$lines" ] || die "$side binary printed $got lines for $lines inputs"
done

{
  echo "date: $(stamp)"
  echo "seed: $SEED; inputs: $lines lines, sha256 $(sha256sum < "$work/inputs.txt" | cut -c1-64)"
  echo "rust: $(cd "$ROOT/rust/smoke" && rustc --version), binary sha256 $(sha256sum < "$rust_bin" | cut -c1-64)"
  echo "lean: $(cd "$LEAN_DIR" && lean --version), binary sha256 $(sha256sum < "$lean_bin" | cut -c1-64)"
  echo "outputs (rust): $(cut -d' ' -f1-2 "$work/rust.out" | sed -E 's/^ok .*/ok/' | sort | uniq -c | awk '{$1=$1};1' | paste -sd, -)"
} > "$out/summary.txt"

if ! cmp -s "$work/rust.out" "$work/lean.out"; then
  paste -d'|' "$work/inputs.txt" "$work/rust.out" "$work/lean.out" \
    | awk -F'|' '$2 != $3 {print NR": input [" $1 "] rust [" $2 "] lean [" $3 "]"}' > "$out/mismatches.txt"
  echo "mismatches: $(wc -l < "$out/mismatches.txt") of $lines" >> "$out/summary.txt"
  cat "$out/summary.txt"
  head -5 "$out/mismatches.txt"
  die "Rust and Lean binaries disagree on $(wc -l < "$out/mismatches.txt") of $lines inputs"
fi
echo "mismatches: 0 of $lines" >> "$out/summary.txt"
cat "$out/summary.txt"
