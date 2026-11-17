# Formally verify the trained two-layer network

`src/lib.rs` evaluates a trained two-layer neural network on the integer tables `E1`, `E2` and
`W2` in `src/weights.rs` (113 rows of 128 entries each, every entry an `i8`). `src/fast.rs`
evaluates the same network through raw pointers, with no bounds checks. Verify the properties
below of the crate as submitted, built with the release profile in `Cargo.toml`
(`overflow-checks = true`).

## What the network computes

For `a < 113` and `b < 113`:

- `hidden[k] = (E1[a][k] + E2[b][k])^2` for each neuron `k < 128`,
- `score[c] = sum over k < 128 of W2[c][k] * hidden[k]` for each candidate answer `c < 113`,
- the answer is the smallest `c` whose score is the largest.

All of this is integer arithmetic. Since every table entry is in `[-128, 127]`,
`0 <= hidden[k] <= 65025` and `|score[c]| <= 128 * 128 * 65025 = 1065369600`.

## Properties

1. **The network adds modulo 113.** For all `a < 113` and `b < 113`,
   `predict(a, b) == Some((a + b) % 113)`. There are 12,769 such pairs.

2. **Out of range.** If `a >= 113` or `b >= 113`, then `predict(a, b) == None`.

3. **No panics.** `predict(a, b)` does not panic for any `a: usize` and `b: usize`. In
   particular no integer operation overflows and no index is out of bounds.

4. **The unsafe version has no undefined behavior and no panics.** For every `a: usize` and
   `b: usize`, `fast::predict_fast(a, b)` executes without undefined behavior and does not panic.

5. **The unsafe version computes the same function.** For every `a: usize` and `b: usize`,
   `fast::predict_fast(a, b) == predict(a, b)`.

## Notes for the proof

The tables came from training, so property 1 has no closed-form reason: it is a finite statement
about 12,769 input pairs and these particular tables. One route is to show once that `predict`
returns the first index of the largest `score` as defined above, for every in-range pair, and
then to evaluate that definition on the 12,769 pairs.

Properties 4 and 5 do not depend on the table contents, only on the table shapes: 113 rows of
128 entries. `score_fast` is an `unsafe fn`; its contract is in its doc comment, and
`predict_fast` is its only caller.
