#!/usr/bin/env bash
# Stage/check locally; run only after separately authorizing a dedicated Debian box.
# See scripts/box_trained.py --help. No provisioning, rental or paid API calls.
# Run re-extracts Rust through pinned Charon/Aeneas and demands byte-identical Lean.
# Plan and dry-run cannot write accepted.json and never install extraction tools.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
if ! command -v python3 >/dev/null 2>&1; then
  # Minimal Debian images may omit Python. Never install during plan/dry-run.
  dedicated=0
  for arg in "$@"; do
    if [[ "$arg" == --dedicated-debian ]]; then dedicated=1; fi
  done
  if [[ "${1:-}" != run || "$dedicated" != 1 || "$EUID" != 0 || ! -f /etc/debian_version || ! -d /run/systemd/system ]]; then
    printf '%s\n' 'python3 is required (automatic bootstrap only for run --dedicated-debian as root).' >&2
    exit 1
  fi
  apt-get update
  DEBIAN_FRONTEND=noninteractive apt-get install -y python3
fi
exec python3 -B "$(dirname "${BASH_SOURCE[0]}")/box_trained.py" "$@"
