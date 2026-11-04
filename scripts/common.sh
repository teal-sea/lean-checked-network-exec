# Shared setup for scripts/*.sh and gates/ci.sh. Sourced, never executed.
# Every script fails loudly: set -euo pipefail, and `die` for every unmet condition.
set -euo pipefail

ROOT="${ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
LEAN_DIR="${LEAN_DIR:-$ROOT/lean}"
EVIDENCE="${EVIDENCE:-$ROOT/evidence}"
WORK="${WORK:-$ROOT/.work}"
GATES="$ROOT/gates"
THEOREMS="${THEOREMS:-$GATES/theorems.txt}"
ALLOWLIST="$GATES/allowlist"

# Pinned in toolchain/PINS.md.
PARENT_URL="https://github.com/teal-sea/lean-checked-network"
PARENT_REV="0214aa3bcee37c9c1f7f6db220c3223375e0c459"

if [ -d "$HOME/.elan/bin" ]; then PATH="$HOME/.elan/bin:$PATH"; fi
# Aeneas's lakefile precompiles AeneasMeta unless CI is set. Builds here never precompile, so
# local and CI builds of the Aeneas library are the same. Lake caches each elaborated lakefile,
# environment included, so the scripts that build pass -R (reconfigure).
export CI="${CI:-1}"

die() { echo "FAIL ($(basename "$0")): $*" >&2; exit 1; }
need() { command -v "$1" >/dev/null 2>&1 || die "required tool '$1' not found on PATH"; }
stamp() { date -u +%FT%TZ; }
# The named theorems: "module constant" pairs, comments and blank lines skipped.
theorems() { grep -vE '^[[:space:]]*(#|$)' "$THEOREMS"; }
allowed_axioms() { grep -vE '^[[:space:]]*(#|$)' "$ALLOWLIST"; }
