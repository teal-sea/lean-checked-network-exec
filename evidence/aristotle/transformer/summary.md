All three properties in `SPEC.md` are proved for `pub fn predict(a: usize, b: usize) -> Option<usize>` in `src/lib.rs`. The proofs cover the crate's actual code, built in release with `overflow-checks = true`. The public contracts are in `Spec/Transformer.lean`, and each is marked proved in the Properties table:

1. **`predict-in-range`:** if `a < 113` and `b < 113`, `predict(a, b)` returns `Some((a + b) % 113)`. This was checked for each of the 12,769 input pairs.
2. **`predict-out-of-range`:** if `a >= 113` or `b >= 113`, `predict(a, b)` returns `None`.
3. **`predict-no-panic`:** for every pair of `usize` values, `predict(a, b)` never panics. No out-of-bounds index, division by zero, arithmetic overflow or other undefined behaviour can occur.

Each contract admits only a normal return, so properties 1 and 2 also rule out panics in their own cases. All three are partial-correctness claims: they say what holds if the call returns, and termination is not claimed.

**Verified:** `predict` and every function it reaches, each proved against its actual code:
- `forward`
- `embed`
- `attention`, `head_scores`, `project`, `softmax_weights`, `exp_fix`, `head_output`
- `residual`
- `mlp_hidden`, `mlp_output`
- `final_stream`
- `unembed`
- `argmax`

The crate has no dependencies, and no external function is assumed.

**Not verified:** functions of `src/lib.rs` that `predict` does not call, such as `logits`. They are outside these claims.

**Assumed:**
- **Weight tables.** Each contract has the premise `Spec.weightsStored` (`Spec/Weights.lean`, registered as a definition). It says the 15 `static` tables of `src/weights.rs` hold exactly their source entries; `Spec/Weights/*.lean` restates those tables entry for entry. I proved separately that the compiled statics contain exactly these bytes from the program's start. So this is a fact about read-only data, not an extra condition on callers.
- **Object size.** As standard for these Rust results, every Rust object is assumed to occupy fewer than \(2^{56}\) bytes.

**Delivered:** `Spec/Transformer.lean`, `Spec/Weights.lean`, `Spec/Weights/*.lean`, `Spec/Rust.lean`, `lean-toolchain` and `README.md`. The original sources and `Cargo` files are unchanged.
