# lean-checked-network-exec

[teal-sea/lean-checked-network](https://github.com/teal-sea/lean-checked-network) holds two
kernel-checked theorems about trained networks with exact integer weights: a 4-unit recurrent
adder (`rnn/`, `RnnAdder`) and a transformer (`transformer/`,
`TransformerBridge.FinalRaw.raw_model_adds_mod_113`). This repository carries those theorems
to code that runs outside Lean. It is link 2 of the chain: each evaluator is rewritten in safe
Rust, translated to Lean with Charon and Aeneas, and proved inside this repository's Lean
project to return `ok` of exactly what the original evaluator computes, for every input.

The sentence this repository is meant to support:

> one theorem about the Rust source under Aeneas's semantics, with the binary trusted through
> rustc

[STATUS.md](STATUS.md) tracks the gates. Every number in it comes from `evidence/`.

## Method

The method is copied from lean-checked-network:

- Lean's kernel is the referee.
- Agents do not edit the gate scripts: `gates/` and `.github/` need @TeaLynx's review.
- Every named theorem's axioms are audited against `gates/allowlist`.
- nanoda rechecks the theorems independently.
- A planted wrong weight must be caught.
- The Rust binary and the Lean evaluator, compiled natively, must agree on the same inputs.

## Layout

| Path | Contents |
| --- | --- |
| `lean/` | Lake project on Aeneas's Lean toolchain: Aeneas translations (`LcnExec/Translated/`), proofs, native Lean evaluators, and the adder vendored from lean-checked-network (`RnnAdder/`) |
| `rust/` | Safe Rust crates: `smoke` (Step 0), `adder` (gate 1A), `transformer` (gate 5) |
| `c/adder/` | The Aristotle submission (gate 1B) |
| `scripts/` | `translate.sh`, `build.sh`, `axioms.sh`, `recheck.sh`, `diff.sh`, `plant_wrong_weight.sh`, and helpers |
| `gates/` | The axiom allowlist, the theorems the gates check, and `ci.sh`, which CI runs |
| `toolchain/` | The pinned Aeneas submodule (Charon is built inside it), `install.sh`, [`PINS.md`](toolchain/PINS.md) |
| `evidence/` | Written only by the scripts, plus `step0.md` |

## Running

The scripts need elan, rustup, Python 3, git, curl, make, a C compiler and linker, rsync and
perl.

```sh
git clone --recurse-submodules https://github.com/teal-sea/lean-checked-network-exec
cd lean-checked-network-exec
toolchain/install.sh            # pinned Aeneas binary; Charon via make setup-charon
scripts/translate.sh smoke      # Charon, then Aeneas: lean/LcnExec/Translated/Smoke.lean
gates/ci.sh                     # what CI runs: sorry/native_decide grep, build, axioms, recheck, diff
scripts/plant_wrong_weight.sh   # wrong-data control
```

## Audit surface

What a reviewer reads, by file, with line counts. Filled from `evidence/` logs only.

## Trusted tools

By name and version. Filled from `evidence/` logs only.
