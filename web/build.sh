#!/bin/sh
# Rebuild the private page's Wasm from the pinned E4 crate in a fresh target.
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CRATE="$ROOT/rust/general_engine_wasm"
RUST_TOOLCHAIN_BIN="${RUST_TOOLCHAIN_BIN:-$HOME/.rustup/toolchains/1.99.1-$(uname -m)-unknown-linux-gnu/bin}"
export PATH="$RUST_TOOLCHAIN_BIN:/usr/bin:/bin"
export RUSTC="$RUST_TOOLCHAIN_BIN/rustc"
case "$("$RUSTC" --version)" in
  "rustc 1.99.1 (58cf8f9c3 "*) ;;
  *) echo "Expected pinned rustc 1.99.1 (58cf8f9c3)" >&2; exit 1 ;;
esac
printf '%s  %s\n' 3fafdba15648738c43e1aa6893eccfcd73e4a1474352ba356a4e02ff31dff6e4 \
  "$ROOT/rust/general_engine/src/lib.rs" | sha256sum --check --status
mkdir -p "$CRATE/target"
TARGET="$(mktemp -d "$CRATE/target/e6-exact-XXXXXX")"
printf 'Clean target: %s\n' "$TARGET"
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER
export CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
"$RUST_TOOLCHAIN_BIN/cargo" build --manifest-path "$CRATE/Cargo.toml" \
  --release --target wasm32-unknown-unknown --offline --locked -j 2 --target-dir "$TARGET" -vv
cp "$TARGET/wasm32-unknown-unknown/release/general_engine_wasm.wasm" "$ROOT/web/general_engine_wasm.wasm"
sha256sum "$ROOT/web/general_engine_wasm.wasm"
