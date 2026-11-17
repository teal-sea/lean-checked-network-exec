#!/usr/bin/env bash
# Translate a Rust crate to Lean: Charon (rustc MIR to LLBC), then Aeneas (LLBC to Lean).
# Usage: scripts/translate.sh [crate]    (default: smoke; the crate lives in rust/<crate>)
# Output: lean/LcnExec/Translated/<Crate>.lean, logs and hashes in evidence/translate/<crate>/.
# Needs the pinned tools from toolchain/install.sh; refuses any other version.
# EXTRA_CHARON_ARGS adds options to the Charon command, for example "--exclude crate::fast" to
# leave a module out of the translation. They are recorded in summary.txt with the rest of the
# command. (Charon itself reads a variable named CHARON_ARGS, so that name is not used here.)
source "$(dirname "$0")/common.sh"

crate="${1:-smoke}"
crate_dir="$ROOT/rust/$crate"
CHARON="$ROOT/toolchain/aeneas/charon/bin/charon"
AENEAS="$ROOT/toolchain/bin/aeneas"
CHARON_COMMIT="$(tail -1 "$ROOT/toolchain/aeneas/charon-pin")"
AENEAS_TAG="nightly-2026.11.04-d1e177b"

[ -f "$crate_dir/Cargo.toml" ] || die "no crate at rust/$crate"
[ -x "$CHARON" ] || die "charon not installed (run toolchain/install.sh)"
[ -x "$AENEAS" ] || die "aeneas not installed (run toolchain/install.sh)"
charon_version="$("$CHARON" version)"
case "$charon_version" in *"($CHARON_COMMIT)"*) ;; *) die "charon is '$charon_version', pin is $CHARON_COMMIT" ;; esac
[ "$("$AENEAS" -version)" = "aeneas $AENEAS_TAG" ] || die "aeneas is '$("$AENEAS" -version)', pin is $AENEAS_TAG"

out="$EVIDENCE/translate/$crate"
llbc="$WORK/translate/$crate.llbc"
dest="$LEAN_DIR/LcnExec/Translated"
rm -rf "$out"
mkdir -p "$out" "$(dirname "$llbc")" "$dest"
rm -f "$llbc"

read -r -a charon_extra <<< "${EXTRA_CHARON_ARGS:-}"
charon_cmd=("$CHARON" cargo --preset=aeneas "${charon_extra[@]}" --dest-file "$llbc" --abort-on-error --error-on-warnings -- --lib)
(cd "$crate_dir" && "${charon_cmd[@]}") > "$out/charon.log" 2>&1 \
  || die "charon failed on rust/$crate (evidence/translate/$crate/charon.log)"
[ -s "$llbc" ] || die "charon wrote no LLBC file"

aeneas_cmd=("$AENEAS" -backend lean -abort-on-error -warnings-as-errors -dest "$dest" "$llbc")
"${aeneas_cmd[@]}" 2>&1 | sed -E 's/\x1b\[[0-9;?]*[A-Za-z]//g' > "$out/aeneas.log" \
  || die "aeneas failed on rust/$crate (evidence/translate/$crate/aeneas.log)"
generated="$dest/${crate^}.lean"
[ -s "$generated" ] || die "aeneas did not generate ${generated#"$ROOT"/}"
if grep -nwE 'axiom|sorry|native_decide|opaque|implemented_by|extern' "$generated" > "$out/forbidden.txt"; then
  die "the translation contains forbidden declarations (evidence/translate/$crate/forbidden.txt)"
fi
rm -f "$out/forbidden.txt"

{
  echo "date: $(stamp)"
  echo "crate: rust/$crate"
  echo "charon: $charon_version, toolchain $("$CHARON" toolchain-version)"
  echo "aeneas: $("$AENEAS" -version)"
  echo "charon command (in rust/$crate): ${charon_cmd[*]/#$ROOT\//}"
  echo "aeneas command: ${aeneas_cmd[*]/#$ROOT\//}"
  echo "llbc sha256: $(sha256sum < "$llbc" | cut -c1-64)"
  echo "generated: ${generated#"$ROOT"/}, sha256 $(sha256sum < "$generated" | cut -c1-64)"
  # Every file of the library: src/lib.rs and its modules (src/bin/ is not translated).
  for source in "$crate_dir"/src/*.rs; do
    echo "source sha256: $(sha256sum < "$source" | cut -c1-64) (src/$(basename "$source"))"
  done
} > "$out/summary.txt"
cat "$out/summary.txt"
