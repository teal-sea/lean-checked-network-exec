# Follow-up: verify the unsafe version

`src/fast.rs` evaluates the same network as `predict` in `src/lib.rs`, through raw pointers and
with no bounds checks. Verify these two further properties of the crate as submitted.

4. **The unsafe version has no undefined behavior and no panics.** For every `a: usize` and
   `b: usize`, `fast::predict_fast(a, b)` executes without undefined behavior and does not panic.

5. **The unsafe version computes the same function.** For every `a: usize` and `b: usize`,
   `fast::predict_fast(a, b) == predict(a, b)`.

Neither property depends on the table contents, only on the table shapes: 113 rows of 128
entries. `score_fast` is an `unsafe fn`; its contract is in its doc comment, and `predict_fast`
is its only caller.
