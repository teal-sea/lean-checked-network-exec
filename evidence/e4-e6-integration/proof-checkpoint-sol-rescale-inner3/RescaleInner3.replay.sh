#!/usr/bin/env bash
set -euo pipefail
source_file=$1
log_file=$2
payload=$(base64 -w0 "$source_file")
remote=$(cat <<'REMOTE'
set -eu
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=2
cd "$HOME/e4/repo/lean"
scratch=$(mktemp -d "$HOME/e4/qa-rescale-sol-XXXXXX")
printf '%s' '@PAYLOAD@' | base64 -d > "$scratch/Candidate.lean"
set +e
timeout 44s flock -w 12 "$HOME/e4/locks/build.lock" bash -c '
  set -eu
  awk "\$1 == \"MemAvailable:\" { found=1; if (\$2 < 10485760) exit 1 } END { if (!found) exit 1 }" /proc/meminfo
  version=$(timeout 5s lean --version)
  case "$version" in *"version 4.35.0"*) ;; *) exit 65;; esac
  timeout 30s lake env lean -j 2 "$1"
' bash "$scratch/Candidate.lean" > "$scratch/lean.log" 2>&1
rc=$?
cat "$scratch/lean.log"
exit "$rc"
REMOTE
)
remote=${remote/@PAYLOAD@/$payload}
timeout 52s /home/thomas/bin/boat-run ssh bx_9m9mrg3q -- "$remote" > "$log_file" 2> "$log_file.stderr"
