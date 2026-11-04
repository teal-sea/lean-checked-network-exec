#!/usr/bin/env bash
# Build the Lean project: fetch the Mathlib cache, `lake build` (LcnExec and the vendored
# RnnAdder), then the smoke evaluator as a native binary. `--no-cache` stops Lake from
# downloading Aeneas's prebuilt release objects: Aeneas's Lean library is built from the pinned
# source. `-R` re-elaborates the lakefiles so CI=1 (scripts/common.sh) takes effect. Mathlib
# comes from its cache (`lake exe cache get`). Output: evidence/build/.
source "$(dirname "$0")/common.sh"
need lake

out="$EVIDENCE/build"
rm -rf "$out"
mkdir -p "$out"
cd "$LEAN_DIR"
{
  echo "date: $(stamp)"
  echo "lean: $(lean --version)"
  echo "lake: $(lake --version)"
} > "$out/versions.txt"

lake exe cache get > "$out/cache-get.log" 2>&1 \
  || die "lake exe cache get failed (evidence/build/cache-get.log)"
lake -R build --no-cache > "$out/build.log" 2>&1 || die "lake build failed (evidence/build/build.log)"
grep -q "Build completed successfully" "$out/build.log" \
  || die "lake build reported no success line (evidence/build/build.log)"
lake -R build --no-cache smoke_eval > "$out/build-exe.log" 2>&1 \
  || die "lake build smoke_eval failed (evidence/build/build-exe.log)"
[ -x .lake/build/bin/smoke_eval ] || die "no smoke_eval binary after the build"
echo "build: ok (lake build; lake build smoke_eval)" | tee "$out/result.txt"
