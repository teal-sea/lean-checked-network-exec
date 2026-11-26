# A verified Rust transformer engine, checked by Lean

A universal integer transformer inference engine in safe Rust (`578` lines), translated to Lean 4 via Charon and Aeneas, proved in Lean 4 to match its mathematical specification without panics or integer overflow for every weights file passing its bounds check, independently rechecked by `nanoda_bin`, and compiled unchanged to native and WebAssembly.

Link 2 of [teal-sea/lean-checked-network](https://github.com/teal-sea/lean-checked-network): carrying kernel-checked neural network theorems from abstract Lean specifications to executable Rust code running outside Lean.

![End-to-end verification chain: 578 lines of safe Rust translated through Charon and Aeneas, proved in Lean 4.35.0, independently rechecked across 9,261 declarations by nanoda_bin, and compiled unchanged to native and 29.8 KB WebAssembly with zero logit mismatches.](docs/figures/verification-chain.svg)

## What is proved

| Result | Theorem | Scope |
| --- | --- | --- |
| Every valid 1- or 2-layer causal transformer checkpoint (`vocab <= 256`, `ctx <= 32`) runs `predict_next` in translated safe Rust with no panics, overflow, or out-of-bounds access and matches `GeneralModel.predictNext` | `LcnExec.GeneralEngine.general_engine_correct` | Any `Weights` accepted by translated `load_check`, any token array and length. Proved once for the engine ([E4](E4-REPORT.md)) |
| All 256 ordered `i64` logits returned by `forward_logits` equal the Lean specification on every valid checkpoint and input | `LcnExec.GeneralEngine.forward_logits_spec` | Translated `rust/general_engine/src/lib.rs` under Aeneas semantics ([E4](E4-REPORT.md)) |
| Independent kernel recheck and mutation controls | `nanoda_bin` 0.4.19 (`9,261` declarations, `0` errors) | Fresh Charon/Aeneas extraction matched byte for byte; three isolated Rust bugs (`shift` 15 vs 16, attention scale `2^23` vs `2^24`, last-on-tie argmax) changed native output and were rejected by the unchanged Lean proofs |
| Earlier verified gates: Rust RNN binary adder (`10` theorems, `14/14` in `nanoda_bin`, `3,535` compile-and-diff inputs) and fixed-width mod-113 transformer (`12,769` pairs, `135/135` modules replayed) | `LcnExec.Adder.Proofs`, `TransformerInt.Gen.adds_mod_113` | Preserved in this repository; see [STATUS.md](STATUS.md) |

No `sorry`. No `native_decide`. Every theorem uses Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) or fewer. The 55.7 MB `general_engine_correct.ndjson` dependency closure checked by `nanoda_bin` is attached to the [e4-general-engine-evidence release](https://github.com/teal-sea/lean-checked-network-exec/releases/tag/e4-general-engine-evidence).

## Checkpoints run on the proved crate

- **`weights/mod113_v1.bin` (1-layer transformer, GLMW v1, 479,504 bytes):** `12,769 / 12,769` exact in stdlib Python (`python/bytelm/ref_engine.py`), native Rust, and browser WebAssembly (`66.70 s` in Chromium with 2 workers and checked arithmetic; logit FNV-1a hash `6cb24f7670e8562e` matches the pinned fixture). See [E5](E5-REPORT.md).
- **`weights/tiny_bytelm_v1.bin` (2-layer byte LM, 464,128 params, 479,504 bytes):** `1.3866` bits/byte (exact integer matches float QAT to 4 decimals; logit correlation `1.000000`), `0` mismatches across `51,200` logits between native Rust and Python and all `256` browser Wasm logits. Corrupt 1-byte weight uploads fail `load_check` and disable generation until restored. See [E5](E5-REPORT.md) and [E6](E6-REPORT.md).

## What is checked outside the kernel

The Lean proof covers the translated safe Rust engine (`rust/general_engine/src/lib.rs`) under Aeneas semantics against the frozen Lean specification. It does **not** verify `rustc`, LLVM, the WebAssembly wrapper (`rust/general_engine_wasm`), the `GLMW v1` binary file parser, the browser runtime, or model text quality. Those layers are checked by compile-and-diff parity harnesses and browser integration receipts (`evidence/e5-bytelm/`, `evidence/e6-wasm/`). The original under-1-second stretch target for the browser mod-113 sweep was not met (`66.70 s` with checked arithmetic; no unchecked or lookup shortcut was substituted).

Full reports: [E4 (engine proof)](E4-REPORT.md) · [E5 (reference, byte LM, parity)](E5-REPORT.md) · [E6 (Wasm browser demo)](E6-REPORT.md) · [STATUS.md](STATUS.md) · [PLAN.md](PLAN.md).

## Audit surface (E4 general engine)

Exact line counts of the verified crate, its Aeneas translation, and the Lean 4 proof modules ([E4 receipt](evidence/e4-general-engine/RECEIPT.json) binds every file by SHA-256):

| Component | Path | Files | Lines | Role |
| --- | --- | ---: | ---: | --- |
| Safe Rust inference engine | `rust/general_engine/src/lib.rs` | 1 | 578 | Checked `i64` causal transformer + `load_check` |
| Charon + Aeneas translation | `lean/LcnExec/Translated/GeneralEngine.lean` | 1 | 2,019 | Generated pure-functional Lean model of the Rust crate |
| Specification & proofs | `lean/LcnExec/GeneralEngine/*.lean` | 32 | 6,472 | `Model.lean` (285), `Load.lean` (703), `Primitives.lean` (602), `Softmax.lean` (575), layer/attention/MLP/unembed/argmax/entrypoint proofs (`Correct.lean`: 202) |
| **Total** | | **34** | **9,069** | |

## Trusted tools

All pins are recorded in [toolchain/PINS.md](toolchain/PINS.md) and bound by SHA-256 in the gate receipts:

| Tool | Pinned version / commit | Role |
| --- | --- | --- |
| Lean 4 | `leanprover/lean4:v4.35.0` (`eb6cafb7`) | Primary theorem prover and kernel (`leanchecker --fresh`) |
| Mathlib | `v4.35.0` (`56a00585`) | Proof library (`lean/lake-manifest.json`) |
| `nanoda_bin` | `0.4.19` (sha256 `cbf13950...`) | Independent Rust Lean typechecker (`9,261` decls checked for E4) |
| `leanexport` | `3.1.0` (sha256 `f6a6483d...`) | Theorem dependency-closure exporter for `nanoda_bin` |
| Charon | `0.1.308` (`a58d1592`) | Rust MIR-to-LLBC extractor |
| Aeneas | `nightly-2026.11.04-d1e177b` (`d1e177bb`) | LLBC-to-Lean 4 functional translator |
| Rust (`rustc`) | `1.99.1` (`rust/rust-toolchain.toml`) | Production native & WebAssembly compiler (`overflow-checks = true`) |
| Chromium | `156.0.8078.79` | Browser Wasm integration verification (`evidence/e6-wasm/ACCEPTANCE.json`) |

## Run the WebAssembly demo locally

The self-contained browser bundle (`evidence/e6-wasm/private-local-page.zip`, pinned by `evidence/e6-wasm/package.sha256`) runs both checkpoints offline on the proved `29,755`-byte Wasm engine with no remote dependencies or API keys:

```sh
unzip evidence/e6-wasm/private-local-page.zip -d /tmp/lcn-demo
cd /tmp/lcn-demo
node scripts/e6_browser_replay.js --serve 8765
# Open http://127.0.0.1:8765/web/index.html
```

Browser acceptance captures and logs live under [evidence/e6-wasm/](evidence/e6-wasm/) (see [E6-REPORT.md](E6-REPORT.md) for the generation, corruption-rejection, and 12,769-pair sweep captures).

## Layout

| Path | Contents |
| --- | --- |
| `rust/general_engine/` | The proved safe Rust inference engine (`lib.rs`, tests, Cargo pins) |
| `rust/{smoke,adder,mlp,transformer}/` | Earlier gate crates |
| `lean/LcnExec/GeneralEngine/` | Specification and proofs for `general_engine_correct` and `forward_logits_spec` |
| `lean/LcnExec/Translated/` | Charon + Aeneas generated Lean translations |
| `python/bytelm/` | Exact stdlib Python reference (`ref_engine.py`), QAT trainer, mod-113 serializer, parity harness |
| `weights/` | `tiny_bytelm_v1.bin` and `mod113_v1.bin` (`479,504` bytes each, GLMW v1) |
| `web/` | Browser WebAssembly demo UI and worker code |
| `gates/` & `scripts/` | CI gates (`sorry`/`native_decide` ban, build, axioms, nanoda recheck, diff, fault injection) |
| `toolchain/` | Pinned Aeneas submodule, `install.sh`, `PINS.md` |
| `evidence/` | Receipts, logs, mutation controls, browser captures, and local demo ZIP |

## License

MIT, see [LICENSE](LICENSE).
