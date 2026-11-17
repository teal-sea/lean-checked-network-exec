I proved all five properties from `SPEC.md` for the `mlp` crate as submitted, built with the release profile and `overflow-checks = true`. The proofs are machine-checked against the compiled code of `src/lib.rs` and `src/fast.rs`. They contain no `sorry` and use only Lean's standard axioms. I did not change any Rust or Cargo file.

The public contracts are in `Spec/Mlp.lean`. They are built on the model in `Spec/Model.lean`: `hidden`, `score`, `firstArgmax`, `answer` and `predictModel`, written directly from `SPEC.md`. The tables' bytes are in `Spec/Weights.lean`. All five rows in the Properties table are marked proved:

1. **The network adds modulo 113** (`Spec.predict_adds_mod_spec`): for every `a < 113` and `b < 113`, `predict(a, b)` returns `Some((a + b) % 113)`. The check covers all 12,769 pairs on the actual tables.
2. **Out of range** (`Spec.predict_out_of_range_spec`): if `a >= 113` or `b >= 113`, `predict(a, b)` returns `None`, whatever the statics hold.
3. **No panics** (`Spec.predict_spec`): for every `a: usize` and `b: usize`, `predict(a, b)` does not panic: no checked operation overflows and no index is out of bounds. It returns the first index of the largest score. This holds for any `i8` tables of the right shape, not just the shipped ones.
4. **`predict_fast` has no UB and no panics** (`Spec.predict_fast_spec`): every raw-pointer read and write in `predict_fast` and `score_fast` stays inside the table rows and `h`. `predict_fast` also returns the same model answer as `predict`.
5. **Same function** (`Spec.predict_fast_eq_predict_spec`): for every `a` and `b`, calling `predict_fast(a, b)` and then `predict(a, b)`, neither panics and the two results are equal.

**Verified:** `predict`, `hidden`, `score`, `predict_fast` and `score_fast`, against their compiled code. The core-library functions they reach were also proved from their compiled code:
- `get_unchecked` on `[[i8; 128]]`, with its internal `check_language_ub`, slice-length and `metadata` calls;
- `as_ptr` on `[i8]` and `[i32]`, and `as_mut_ptr` on `[i32]`;
- `add` on `*const i8`, `*const i32` and `*mut i32`.

No external guarantee is assumed: every function the properties reach is verified.

**Conditions:**
- **Partial correctness.** Each result says what holds if the call returns. Termination is not proved.
- **Table contents.** The contracts take as a premise that the read-only statics `E1`, `E2` and `W2` hold their table bytes (`Spec.tablesStored`). I proved separately that the compiled crate's statics hold exactly the bytes of `src/weights.rs` from program start, so this premise is not an extra assumption about the data.
- **Object size.** As usual for Rust results, every object is assumed to be smaller than \(2^{56}\) bytes.

**A note on `SPEC.md`:** its bounds (`hidden[k] <= 65025`, `|score[c]| <= 1065369600`) are not quite right for arbitrary entries in `[-128, 127]`: \((-128 - 128)^2 = 65536\). They do hold for the shipped tables, whose entries lie in `[-127, 127]`. The correct general bounds still fit easily in `i32` and `i64`, so the no-overflow results hold for any `i8` tables.
