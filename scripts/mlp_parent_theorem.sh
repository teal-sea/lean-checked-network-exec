#!/usr/bin/env bash
# Measure what the MLP theorem of lean-checked-network costs on this repository's Lean toolchain.
#
# The theorem is LeanCheckedNetwork.Trained.adds_mod_113 (lean/LeanCheckedNetwork/Trained/ in
# lean-checked-network): the trained two-layer network answers (a + b) % 113 on all 12,769
# inputs, by 113 kernel evaluations (`decide +kernel`). Gate 1A's sibling for the MLP would
# compose a refinement theorem about rust/mlp with it, so its files would be vendored as
# scripts/vendor.sh vendors RnnAdder. This script vendors nothing into lean/: it copies the
# files, byte for byte, into a scratch Lake project under .work/ on this repository's toolchain,
# builds them, and records the time, the axioms and the diff of every copied file.
# Output: evidence/mlp/parent-theorem/.
source "$(dirname "$0")/common.sh"
need git
need lake

out="$EVIDENCE/mlp/parent-theorem"
work="$WORK/mlp/parent-theorem"
rm -rf "$out" "$work"
mkdir -p "$out" "$work/project"

git clone --quiet --filter=blob:none "$PARENT_URL" "$work/parent"
git -C "$work/parent" checkout --quiet "$PARENT_REV"
parent_toolchain="$(cat "$work/parent/lean/lean-toolchain")"
our_toolchain="$(cat "$LEAN_DIR/lean-toolchain")"

# The modules adds_mod_113 needs: the network, the fast evaluator, the tables, the 113 rows.
mapfile -t FILES < <(cd "$work/parent/lean" && {
  echo LeanCheckedNetwork/Network.lean
  echo LeanCheckedNetwork/Fast.lean
  ls LeanCheckedNetwork/Trained/*.lean
} | LC_ALL=C sort)
project="$work/project"
echo "$our_toolchain" > "$project/lean-toolchain"
cat > "$project/lakefile.lean" <<'EOF'
import Lake
open Lake DSL
package «mlp-parent-theorem» where
@[default_target]
lean_lib LeanCheckedNetwork where
  globs := #[.submodules `LeanCheckedNetwork]
EOF
{
  echo "# Copied from $PARENT_URL @ $PARENT_REV (lean/), by scripts/mlp_parent_theorem.sh on $(stamp)."
  echo "# Pinned Lean versions: parent $parent_toolchain, this repo $our_toolchain."
  for f in "${FILES[@]}"; do
    mkdir -p "$project/$(dirname "$f")"
    cp "$work/parent/lean/$f" "$project/$f"
    echo "# $f sha256 original $(sha256sum < "$work/parent/lean/$f" | cut -c1-64) copied $(sha256sum < "$project/$f" | cut -c1-64), $(wc -l < "$project/$f") lines"
  done
  echo "# Textual diff, original -> copied (empty means byte-identical):"
  for f in "${FILES[@]}"; do
    diff -u --label "original/$f" --label "copied/$f" "$work/parent/lean/$f" "$project/$f" || true
  done
} > "$out/copied-diff.txt"

cd "$project"
start=$(date +%s)
set +e
lake build > "$out/build.log" 2>&1
status=$?
set -e
seconds=$(( $(date +%s) - start ))
{
  echo "date: $(stamp)"
  echo "parent: $PARENT_URL @ $PARENT_REV, lean/lean-toolchain = $parent_toolchain"
  echo "built on: $(lean --version)"
  echo "machine: $(nproc) cores, $(awk '/MemTotal/ {printf "%.0f GiB RAM", $2 / 1048576}' /proc/meminfo)"
  echo "files: ${#FILES[@]} copied byte for byte ($(cat "${FILES[@]/#/$project/}" | wc -c) bytes); diff in copied-diff.txt"
  echo "lake build (the ${#FILES[@]} modules): exit $status, $seconds s wall"
  echo "modules, as Lake reports them:"
  grep -E 'Built ' "$out/build.log" | sed -E 's/^[^B]*Built /  /' || true
} > "$out/summary.txt"
[ "$status" -eq 0 ] || { cat "$out/summary.txt"; die "lake build failed (evidence/mlp/parent-theorem/build.log)"; }

echo "import LeanCheckedNetwork.Trained.AllInputs
#check @LeanCheckedNetwork.Trained.adds_mod_113
#print axioms LeanCheckedNetwork.Trained.adds_mod_113" > "$work/Probe.lean"
lake env lean "$work/Probe.lean" > "$out/probe.out" 2>&1 || die "lean failed on the probe (evidence/mlp/parent-theorem/probe.out)"
{
  echo "statement and axioms (probe.out):"
  sed 's/^/  /' "$out/probe.out"
} >> "$out/summary.txt"
cat "$out/summary.txt"
