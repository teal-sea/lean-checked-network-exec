# E4: checked integer next-token engine

Lean proves that for every `Weights` accepted by the translated Rust `load_check` and every token array and length, `predict_next` returns `ok` and agrees exactly with `GeneralModel.predictNext`. Invalid inputs return `none`. For valid inputs, `forward_logits_spec` additionally establishes exact equality of the 256 ordered logits. The proof permits either one or two active layers and every supported vocabulary size. Returning `ok` excludes the failure and divergence cases in the translated semantics. The `generate_greedy` wrapper is not part of this theorem.

- Lean 4.35.0 build, direct elaboration, typed import, and `leanchecker --fresh` passed. The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- A separate kernel, nanoda 0.4.19, checked 9,261 declarations with zero typechecker errors. Its axiom pretty-printer reported one error; the axiom allowlist was a hard gate.
- Fresh Charon/Aeneas extraction of the unmodified Rust matched the frozen Lean translation byte for byte. Each of three isolated Rust mutations compiled natively with overflow checks and changed the intended output. After re-extraction, the unchanged Lean proofs rejected all three: shift by 15 rather than 16, attention scale 2^23 rather than 2^24, and taking the last token on ties rather than the first.
- [Receipt](evidence/e4-general-engine/RECEIPT.json) binds the source, compiled checks, export and exact control artifacts. Rust version 1.99.1, native target x86_64-unknown-linux-gnu. The production source, arithmetic checks, frozen model and theorem gates were not changed.

The proof depends on translation fidelity and on the frozen specification. It does not certify the compiler, browser or WebAssembly wrapper. The separate browser acceptance must use this exact crate and the trained E5 weights.
