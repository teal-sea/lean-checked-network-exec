#!/usr/bin/env bash
# The Aeneas invocation is expected to fail. Preserve both producer exits.
set -eu
root="$(cd "$(dirname "$0")/.." && pwd)"
repro="$root/pilot/engine/failures/nested-return/repro"
llbc="$root/.work/engine-nested-return.llbc"
mkdir -p "$root/.work"
export CARGO_BUILD_JOBS=4
(cd "$repro" && nice -n 10 "$root/toolchain/aeneas/charon/bin/charon" cargo --preset=aeneas --dest-file "$llbc" --abort-on-error --error-on-warnings -- --lib) > "$repro/charon.log" 2>&1
set +e
"$root/toolchain/bin/aeneas" -backend lean -abort-on-error -warnings-as-errors -dest "$root/.work" "$llbc" > "$repro/aeneas.log" 2>&1
result=$?
printf 'aeneas_exit=%s\n' "$result" > "$repro/result.txt"
# Only the known diagnostic counts as reproduction; other failures are failures of this script.
test "$result" -ne 0 && grep -q 'Returns inside of nested loops are not supported yet' "$repro/aeneas.log"
