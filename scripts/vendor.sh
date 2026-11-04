#!/usr/bin/env bash
# Bring the adder evaluator definitions from lean-checked-network into lean/RnnAdder/.
#
# The brief: use a lake dependency if the pinned Lean versions match; otherwise vendor, with the
# textual diff against the original in evidence/vendored-diff.txt, and patch neither project.
# This script records both versions, attempts the dependency route in a scratch project and
# records what happens, then vendors (only when the versions differ).
source "$(dirname "$0")/common.sh"
need git
need lake

out="$EVIDENCE/vendor"
work="$WORK/vendor"
rm -rf "$work" "$out"
mkdir -p "$work" "$out"
FILES=(RnnAdder/Network.lean RnnAdder/Trained.lean)

git clone --quiet --filter=blob:none "$PARENT_URL" "$work/parent"
git -C "$work/parent" checkout --quiet "$PARENT_REV"
parent_toolchain="$(cat "$work/parent/rnn/lean/lean-toolchain")"
our_toolchain="$(cat "$LEAN_DIR/lean-toolchain")"
{
  echo "date: $(stamp)"
  echo "parent: $PARENT_URL @ $PARENT_REV, rnn/lean/lean-toolchain = $parent_toolchain"
  echo "this repo: lean/lean-toolchain (Aeneas's) = $our_toolchain"
} > "$out/versions.txt"
if [ "$parent_toolchain" = "$our_toolchain" ]; then
  die "the pinned Lean versions match ($our_toolchain): use the lake dependency, not vendoring"
fi

# The dependency route, in a scratch project on our toolchain. Recorded, never used.
scratch="$work/dependency-route"
mkdir -p "$scratch"
echo "$our_toolchain" > "$scratch/lean-toolchain"
cat > "$scratch/lakefile.lean" <<EOF
import Lake
open Lake DSL
package depcheck where
require «rnn-adder» from git "$PARENT_URL" @ "$PARENT_REV" / "rnn/lean"
lean_lib DepCheck where
EOF
echo "import RnnAdder.Trained" > "$scratch/DepCheck.lean"
set +e
(cd "$scratch" && lake update && lake build DepCheck) > "$out/dependency-route.log" 2>&1
dependency_status=$?
set -e
# A build that compiled nothing is not evidence either way.
if grep -q "Nothing to build" "$out/dependency-route.log"; then
  die "the dependency-route build compiled nothing (evidence/vendor/dependency-route.log)"
fi
echo "dependency route (scratch, $our_toolchain): lake update && lake build DepCheck exit $dependency_status" \
  >> "$out/versions.txt"

# The vendored route.
mkdir -p "$LEAN_DIR/RnnAdder"
{
  echo "# Vendored from $PARENT_URL @ $PARENT_REV (rnn/lean), by scripts/vendor.sh on $(stamp)."
  echo "# Pinned Lean versions differ: parent $parent_toolchain, this repo $our_toolchain."
  echo "# Dependency route in a scratch project: exit $dependency_status (evidence/vendor/dependency-route.log)."
  for f in "${FILES[@]}"; do
    cp "$work/parent/rnn/lean/$f" "$LEAN_DIR/$f"
    echo "# $f sha256 original $(sha256sum < "$work/parent/rnn/lean/$f" | cut -c1-64) vendored $(sha256sum < "$LEAN_DIR/$f" | cut -c1-64)"
  done
  echo "# Textual diff, original -> vendored (empty means byte-identical):"
  for f in "${FILES[@]}"; do
    diff -u --label "original/$f" --label "vendored/$f" \
      "$work/parent/rnn/lean/$f" "$LEAN_DIR/$f" || true
  done
} > "$EVIDENCE/vendored-diff.txt"
echo "vendored ${FILES[*]} into lean/; versions and diff in evidence/"
