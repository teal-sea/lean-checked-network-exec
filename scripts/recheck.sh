#!/usr/bin/env bash
# Independent recheck with nanoda, following lean-checked-network's nanoda driver
# (acas/gen/nanoda.py; its verify.sh does not run nanoda). For each theorem in the theorems file:
# export its dependency closure with the toolchain's leanexport, then run nanoda_bin with the
# axiom allowlist enforced as a hard error. Fails unless nanoda reports no typechecker errors
# for every theorem, and fails if any object file on the search path changes meanwhile.
#
# Uses the leanexport and nanoda_bin shipped in the project's Lean toolchain; set NANODA to use
# another nanoda_bin. Large files (exports, object manifest) go to .work/; evidence/recheck/
# (or $RECHECK_OUT) gets logs, versions and hashes.
source "$(dirname "$0")/common.sh"
need lake
need python3

out="${RECHECK_OUT:-$EVIDENCE/recheck}"
work="$WORK/recheck/$(basename "$out")"
rm -rf "$out" "$work"
mkdir -p "$out" "$work"
cd "$LEAN_DIR"

prefix="$(lean --print-prefix)"
leanexport="$prefix/bin/leanexport"
nanoda="${NANODA:-$prefix/bin/nanoda_bin}"
[ -x "$leanexport" ] || die "no leanexport in the Lean toolchain at $prefix"
[ -x "$nanoda" ] || die "no nanoda_bin at $nanoda"
lean_path="$(lake env printenv LEAN_PATH)"
[ -n "$lean_path" ] || die "lake env gave no LEAN_PATH"
[ -n "$(theorems)" ] || die "no theorems listed in $THEOREMS"

manifest() {
  local IFS=:
  for dir in $lean_path; do
    [ -d "$dir" ] && find "$dir" -name '*.olean*' -type f
  done | LC_ALL=C sort | xargs -r sha256sum
}
manifest > "$work/objects.before"
[ -s "$work/objects.before" ] || die "no .olean files on LEAN_PATH"

{
  echo "date: $(stamp)"
  echo "project: ${LEAN_DIR#"$ROOT"/}, toolchain $(lean --version)"
  echo "leanexport: $leanexport"
  echo "nanoda: $nanoda, $("$nanoda" -h 2>&1 | head -1)"
  echo "objects on LEAN_PATH: $(wc -l < "$work/objects.before") files, manifest sha256 $(sha256sum < "$work/objects.before" | cut -c1-64)"
  echo "allowlist: $(allowed_axioms | tr '\n' ' ')"
} > "$out/summary.txt"

while read -r module theorem; do
  export_file="$work/$theorem.ndjson"
  config="$out/$theorem.nanoda.json"
  log="$out/$theorem.nanoda.log"
  lake env "$leanexport" "$module" -- "$theorem" > "$export_file" 2> "$out/$theorem.leanexport.err" \
    || die "leanexport failed for $theorem (${out#"$ROOT"/}/$theorem.leanexport.err)"
  [ -s "$export_file" ] || die "empty export for $theorem"
  python3 - "$export_file" "$config" "$ALLOWLIST" <<'PY'
import json
import sys

export_file, config, allowlist = sys.argv[1:4]
axioms = [l.split()[0] for l in open(allowlist) if l.strip() and not l.lstrip().startswith("#")]
json.dump(
    {
        "export_file_path": export_file,
        "use_stdin": False,
        "permitted_axioms": axioms,
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "pp_declars": [],
        "pp_to_stdout": False,
        "print_success_message": True,
    },
    open(config, "w"),
    indent=2,
)
PY
  start=$(date +%s)
  set +e
  "$nanoda" "$config" > "$log" 2>&1
  status=$?
  set -e
  seconds=$(( $(date +%s) - start ))
  # The result line and whatever follows it (nanoda lists pretty printer errors over several lines).
  checked="$(sed -n '/Checked [0-9,]* declarations/,$p' "$log" | tr -s ' \n' ' ' | sed 's/ $//')"
  [ "$status" -eq 0 ] || die "nanoda exited $status on $theorem (${log#"$ROOT"/})"
  [ -n "$checked" ] || die "nanoda printed no 'Checked N declarations' line for $theorem"
  case "$checked" in
    *"no typechecker errors"*) ;;
    *) die "nanoda reported typechecker errors for $theorem: $checked" ;;
  esac
  {
    echo "$theorem ($module): export $(wc -c < "$export_file") bytes, sha256 $(sha256sum < "$export_file" | cut -c1-64), format $(head -c 200 "$export_file" | grep -oE '"exporter":\{[^}]*\}' || echo unknown)"
    echo "  nanoda ${seconds}s: $checked"
  } >> "$out/summary.txt"
done < <(theorems)

manifest > "$work/objects.after"
cmp -s "$work/objects.before" "$work/objects.after" \
  || die "object files on LEAN_PATH changed during the recheck"
echo "recheck: ok" >> "$out/summary.txt"
cat "$out/summary.txt"
