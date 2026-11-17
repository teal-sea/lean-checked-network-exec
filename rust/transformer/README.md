# transformer

The trained one-layer, four-head transformer on addition mod 113, as a fixed-width integer
program in safe Rust (gate 5, the Rust side). No dependencies, `#![no_std]`,
`#![forbid(unsafe_code)]`, `i64` arithmetic, no floating point.

`predict(a, b)` returns `Some((a + b) % 113)` for all 12,769 pairs with `a, b < 113` and `None`
for any other input. This is tested on every pair. It is not proved. No Lean, Aeneas or
Aristotle result exists for this crate yet.

The numbers below are in [`evidence/transformer-int/summary.txt`](../../evidence/transformer-int/summary.txt),
written by `scripts/check_transformer_int.py`, unless the line names another source.

## What it is

- The weights are lean-checked-network's `transformer/runs/best.npz`, sha256
  `7cea95ed6771691dfe8a29bedfdae72d9a62c8947c25b1bca2c56919c0ff0f9e`, quantised at `S = 256` by
  the rule of that repository's `int_transformer.py quantise(W, 8)`. All 226,688 integers equal
  the ones that function returns. They are the weights of the model behind
  `TransformerBridge.FinalRaw.raw_model_adds_mod_113`.
- The program is not the integer program of that theorem. That one carries the softmax
  denominators through the network on unbounded integers and never divides. This one divides in
  the softmax and rescales by shifts, so that every number fits an `i64`. The attention scores
  are the same integers in both: all 908 agree with `int_transformer.py build_tables`.
- No proof relates this program to the real-softmax model. Measured over all pairs, its logits
  divided by 2^32 differ from a float64 forward pass of that model by at most 1.08097e-05. The
  smallest margin is 14.655480 logit units here and 14.655483 there.

## The stages

| Stage | Value | Scale |
| --- | --- | --- |
| `embed` | `x = TOK[tok] + POS[pos]` | 2^8 |
| `project` | query, key and value vectors, `x` times `WQ`, `WK`, `WV` | 2^16 |
| `head_scores` | `s = q . k`, exact | 2^32 |
| `exp_fix` | `e` for `2^30 * exp(-(max(s) - s) / 2^32)`, from tables | 2^30 |
| `softmax_weights` | `alpha = e * 2^24 / (e0 + e1 + e2)` | 2^24 |
| `head_output` | `z = (alpha0 * v0 + alpha1 * v1 + alpha2 * v2) >> 16`, then `z` times `WO` | 2^24, then 2^32 |
| `residual` | `r = x2 * 2^24 + att` | 2^32 |
| `mlp_hidden` | `m = relu(r * WIN + BIN * 2^8) >> 8` | 2^32 |
| `mlp_output` | `o = m * WOUT + BOUT` | 2^40 |
| `final_stream` | `fin = (r * 2^8 + o) >> 16` | 2^24 |
| `unembed` | `logits = fin * U` | 2^32 |
| `argmax` | the largest logit, the first index on a tie | |

- Three shifts rescale: `>> 16` after the attention mix, `>> 8` after the ReLU, `>> 16` before
  the unembedding. A shift on an `i64` rounds toward minus infinity.
- One division, in the softmax. Its numerator is not negative and its denominator is at least
  2^30, so it rounds down and cannot divide by zero.
- `exp_fix(d)` cuts `d` to 24 fractional bits and multiplies four table entries, each
  `round(2^30 * exp(-y))`: 32 entries for the whole part and three tables of 256 for the
  fraction. `tests/all_pairs.rs` checks that it is within 72 units of 2^-30 of the real
  exponential on 200,000 seeded inputs. It is not monotone: where the result is small, the next
  table entry can add one unit.
- The nine matrices are stored as `i8` and the two bias vectors as `i64`.

One call of `predict` does 277,376 multiply-adds in its matrix products, counted from the loop
bounds. The projections and the scores depend only on the head, the position and the token:
908 scores and 908 value vectors over all inputs.

## Widths

- Input-independent bound: at most 61 bits, in `exp_fix`, where a table product can reach 2^60.
  Outside the softmax the largest bound is 54 bits, in `mlp_output` and `final_stream`. An
  `i64` holds 63.
- Measured on all 12,769 pairs, with every product and partial sum: at most 61 bits in
  `exp_fix`, 55 in `softmax_weights`, and 46 elsewhere.
- Both `Cargo.toml` profiles set `overflow-checks = true`, so an overflow is a panic and the
  test would fail on it.

## Results

- 12,769 pairs, 0 wrong, 0 ties.
- Smallest margin: 62,944,808,481 at scale 2^32, at the pair (21, 56).
- Rust against the Python reference: 1,442,897 logits compared, 0 differ.
- `cargo test --release`, run by hand on 2026-11-17 and not in the evidence file: 4 tests pass
  on rustc 1.99.1, the pin in `rust/rust-toolchain.toml`, and on rustc 1.97.0-nightly
  (f53b654a8 2026-04-30), installed as `nightly-2026-05-01`. Aristotle's Rust documentation, read
  the same day, names rustc 1.97.0-nightly from 2026-05-01 as its compiler.

## Files

| Path | Contents |
| --- | --- |
| `src/lib.rs` | The program |
| `src/weights.rs` | Generated: the weights and the exponential tables. Do not edit |
| `SPEC.md` | The properties to verify, in the crate's own names |
| `tests/all_pairs.rs` | Every pair, inputs out of range, the exponential, the softmax weights |
| `tests/fixtures/python_reference.txt` | Written by the Python reference: a hash of all logits, the smallest margin |
| `examples/dump_logits.rs` | Prints every logit, for the comparison with the Python reference |
| `../../scripts/gen_transformer_weights.py` | Checkpoint in, `src/weights.rs` out. Standard library only |
| `../../scripts/check_transformer_int.py` | The same program on Python integers, the bounds, the comparisons, the evidence |

## Running

```sh
CKPT=path/to/lean-checked-network/transformer/runs/best.npz
python3 scripts/gen_transformer_weights.py "$CKPT" --check   # weights.rs is what the generator emits
(cd rust/transformer && cargo test --release)               # about 6 s
python3 scripts/check_transformer_int.py "$CKPT"             # about 6 minutes; writes the evidence
```

`check_transformer_int.py --parent path/to/lean-checked-network` adds the three comparisons with
that repository's `int_transformer.py`. They need numpy. Nothing else here does.
