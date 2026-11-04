#!/usr/bin/env bash
# The CI gate sequence; .github/workflows/ci.yml runs exactly this. Every step fails loudly.
set -euo pipefail
cd "$(dirname "$0")/.."

if grep -rnwE 'sorry|native_decide' --include='*.lean' --exclude-dir=.lake lean; then
  echo "FAIL (gates/ci.sh): sorry or native_decide in the Lean tree" >&2
  exit 1
fi
scripts/build.sh
scripts/axioms.sh
scripts/recheck.sh
scripts/diff.sh
echo "gates: ok"
