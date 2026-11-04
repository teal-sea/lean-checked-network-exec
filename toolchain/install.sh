#!/usr/bin/env bash
# Install the pinned translation tools (toolchain/PINS.md) into toolchain/:
#   - Aeneas: the official nightly binary built from the pinned commit, checked by SHA-256;
#   - Charon: built from the commit in aeneas/charon-pin by `make setup-charon` (needs rustup).
# Lean comes from elan through lean/lean-toolchain; the production Rust toolchain through
# rust/rust-toolchain.toml.
set -euo pipefail
cd "$(dirname "$0")"

AENEAS_COMMIT=d1e177bb9fdc17fa62e730d524ac905ba19776ed
AENEAS_TAG=nightly-2026.11.04-d1e177b
AENEAS_TARBALL_SHA256=955928facac9853047edee5c68dd35bb40840955e1a5ddda66668dcb3198d72e
CHARON_COMMIT=a58d159210b3a36fedeaba4437bda896a8b12f0d

die() { echo "FAIL (toolchain/install.sh): $*" >&2; exit 1; }

[ "$(git -C aeneas rev-parse HEAD)" = "$AENEAS_COMMIT" ] \
  || die "submodule toolchain/aeneas is not at $AENEAS_COMMIT (run: git submodule update --init)"
[ "$(tail -1 aeneas/charon-pin)" = "$CHARON_COMMIT" ] || die "aeneas/charon-pin is not $CHARON_COMMIT"

mkdir -p bin
tarball="bin/.aeneas-linux-x86_64.tar.gz"
curl -fsSL "https://github.com/AeneasVerif/aeneas/releases/download/$AENEAS_TAG/aeneas-linux-x86_64.tar.gz" \
  -o "$tarball"
echo "$AENEAS_TARBALL_SHA256  $tarball" | sha256sum -c - >/dev/null || die "Aeneas tarball checksum mismatch"
tar -xzf "$tarball" -C bin aeneas
rm -f "$tarball"
[ "$(bin/aeneas -version)" = "aeneas $AENEAS_TAG" ] || die "bin/aeneas reports '$(bin/aeneas -version)'"

# Note: `make setup-charon` exits 0 even when Charon's own `make test` fails (its script runs
# `exit 0` after the build chain), so the result is checked here instead.
(cd aeneas && make setup-charon)
[ -x aeneas/charon/bin/charon ] || die "make setup-charon did not produce aeneas/charon/bin/charon"
version="$(aeneas/charon/bin/charon version)"
case "$version" in
  *"($CHARON_COMMIT)"*) ;;
  *) die "aeneas/charon/bin/charon reports '$version', expected commit $CHARON_COMMIT" ;;
esac
echo "installed: $(bin/aeneas -version); charon $version"
