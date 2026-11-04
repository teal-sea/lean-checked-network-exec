# Toolchain pins

Read from the installed tools and pinned files on 2026-11-04. The commands that print each
version are in [evidence/step0.md](../evidence/step0.md).

## Rust to Lean

| Tool | Pin | Set by |
| --- | --- | --- |
| Aeneas | commit `d1e177bb9fdc17fa62e730d524ac905ba19776ed` (2026-11-03, "Bump Charon (#1474)") | git submodule `toolchain/aeneas` |
| Aeneas binary | release `nightly-2026.11.04-d1e177b`, built by Aeneas's CI from that commit. Asset `aeneas-linux-x86_64.tar.gz`, sha256 `955928facac9853047edee5c68dd35bb40840955e1a5ddda66668dcb3198d72e`. `aeneas -version` prints `aeneas nightly-2026.11.04-d1e177b` | `toolchain/install.sh` |
| Charon | commit `a58d159210b3a36fedeaba4437bda896a8b12f0d` (from `toolchain/aeneas/charon-pin`); `charon version` prints `0.1.308 (a58d159210b3a36fedeaba4437bda896a8b12f0d)` | `toolchain/install.sh` (`make setup-charon`) |
| Rust toolchain Charon requires | `nightly-2026-09-17`, components `rustc-dev`, `llvm-tools`, `rust-src`, `miri` | `toolchain/aeneas/charon/rust-toolchain` |

## Lean

| Tool | Pin | Set by |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. This is the `lean-toolchain` Aeneas ships in `backends/lean` | `lean/lean-toolchain` (a copy of Aeneas's) |
| Lake | `5.0.0-src+eb6cafb` | the Lean toolchain |
| Mathlib | `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (Aeneas's dependency) | `lean/lake-manifest.json` |
| elan | `4.2.4`; CI checks the release tarball, sha256 `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63` | `.github/workflows/ci.yml` |

## Independent recheck

| Tool | Pin | Set by |
| --- | --- | --- |
| nanoda_bin | `0.4.19`, shipped in the Lean v4.35.0 toolchain as `bin/nanoda_bin`, sha256 `cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5` | the Lean toolchain |
| leanexport | lean4export `3.1.0`, export format `3.1.0`, shipped in the Lean v4.35.0 toolchain, sha256 `f6a6483d518a11b323c28b9bac176d2220df0e9fc3230833815db9586669c074` | the Lean toolchain |

The same two files, by sha256, are the ones lean-checked-network's ACAS release used
(`acas/evidence/release/toolchain-binaries.json` in that repository).

## Production binary

| Tool | Pin | Set by |
| --- | --- | --- |
| Rust | `1.99.1` (`rustc 1.99.1 (58cf8f9c3 2026-10-13)`), profile `minimal` | `rust/rust-toolchain.toml` |

## lean-checked-network

Pinned at commit `0214aa3bcee37c9c1f7f6db220c3223375e0c459` (`scripts/common.sh`). Its
`rnn/lean` uses `leanprover/lean4:v4.35.0-rc2`, which ships nanoda_bin `0.4.17`.

The export step nanoda consumes there (`acas/gen/nanoda.py`, the only nanoda driver in that
repository) has two parts:

1. `leanexport <Module> -- <theorem> > final.ndjson` exports the named theorem's dependency
   closure.
2. `nanoda_bin <config.json>` checks it. The config sets `permitted_axioms` [`propext`,
   `Classical.choice`, `Quot.sound`], `unpermitted_axiom_hard_error`, `nat_extension` and
   `string_extension`.

Its `verify.sh` (`transformer/verify-release.sh`, shipped as `verify.sh` in release r2) does not
run nanoda (`transformer/RECHECK.md`: "Neither this verifier nor its repair adds a nanoda
invocation"). `scripts/recheck.sh` follows `acas/gen/nanoda.py`.

## How the tools were installed

- Charon: `make setup-charon`, run by `toolchain/install.sh`. Nix is not installed on the
  machine, so the script took its rustup route and built Charon in the dev profile. Its
  OCaml half then failed (`/bin/sh: 1: dune: not found`) and the script still exited 0, so
  `install.sh` checks the binary and its version itself. Charon's test suite was not run.
- Aeneas: neither Nix nor `make setup-charon` (that target installs only Charon).
  `toolchain/install.sh` downloads the official nightly binary for the pinned commit and checks
  its sha256. Building Aeneas from source needs OCaml, opam, dune and the GMP headers, and none
  of them are on the machine. Installing Nix would mean a root install on a shared machine.
- Aeneas's Lean library: built from the pinned source by `scripts/build.sh`
  (`lake build --no-cache`). Lake would otherwise download prebuilt objects from the release,
  because Aeneas's lakefile sets `preferReleaseBuild`.
- Mathlib: prebuilt objects from `lake exe cache get`, as in lean-checked-network.
