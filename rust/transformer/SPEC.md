# Formally verify the transformer evaluator

The crate `transformer` evaluates a trained one-layer, four-head transformer on one task: add
two numbers modulo 113. It uses integer arithmetic only. `predict(a, b)` runs the network on the
token sequence `[a, b, =]` and returns the index of the largest of its 113 logits.

The code to verify is `src/lib.rs`. `src/weights.rs` holds the network's weights and four
exponential tables as `static` arrays of constants. The files under `tests/` and `examples/`
are test harnesses and are not targets.

The crate is `#![no_std]`, has no dependencies and has no `unsafe`. Verify it as `Cargo.toml`
builds it: the release profile with `overflow-checks = true`.

## Properties

Properties 1 to 3 are the result. Properties 4 to 6 are stronger forms of them.

1. **The network adds modulo 113 on every input.** For every `a: usize` and `b: usize` with
   `a < 113` and `b < 113`, `predict(a, b)` returns `Some((a + b) % 113)`.
2. **Inputs out of range are rejected.** For every `a: usize` and `b: usize` with `a >= 113` or
   `b >= 113`, `predict(a, b)` returns `None` and `logits(a, b)` returns `None`.
3. **No panic.** `predict` and `logits` return without panicking for every `a: usize` and
   `b: usize`. No array index is out of bounds, no division has a zero divisor, and no integer
   operation overflows.
4. **No arithmetic overflow, whatever the build flag.** For every `a < 113` and `b < 113`,
   every `+`, `-` and `*` on `i64` that `predict(a, b)` executes has its exact result in the
   `i64` range.
5. **The right answer wins strictly.** For every `a < 113` and `b < 113`, `logits(a, b)`
   returns `Some(l)`, and `l[(a + b) % 113] > l[c]` for every `c < 113` other than
   `(a + b) % 113`.
6. **The margin.** In property 5, `l[(a + b) % 113] - l[c] >= 62944808481` for every such `c`.
   The bound is attained at `a = 21`, `b = 56`.

The inputs of properties 1, 4, 5 and 6 are the 12,769 pairs `(a, b)` with `a, b < 113`. A proof
may enumerate them.

## The program

`predict(a, b)` and `logits(a, b)` return `None` unless `a < 113` and `b < 113`. Otherwise both
call `forward(a, b)`, and `predict` returns `Some(argmax(&l))` of its logits `l`. `forward` runs
these stages. Every value is an `i64` at one fixed scale.

| Function | Computes | Scale |
| --- | --- | --- |
| `embed(tok, pos)` | `x[k] = TOK[tok][k] + POS[pos][k]`, for the tokens `a`, `b`, `113` at positions 0, 1, 2 | 2^8 |
| `project(x, w)` | `out[i] = sum over k of x[k] * w[k][i]`: the query, key and value vectors | 2^16 |
| `head_scores(h, x)` | `s[j] = (x[2] * WQ[h]) . (x[j] * WK[h])` for the positions `j = 0, 1, 2` | 2^32 |
| `exp_fix(d)` | the product of four table entries, standing in for `2^30 * exp(-d / 2^32)` | 2^30 |
| `softmax_weights(s)` | `alpha[j] = e[j] * 2^24 / (e[0] + e[1] + e[2])`, `e[j] = exp_fix(max(s) - s[j])` | 2^24 |
| `head_output(h, x, alpha)` | `z[i] = (alpha[0] * v0[i] + alpha[1] * v1[i] + alpha[2] * v2[i]) >> 16`, then `out[k] = sum over i of z[i] * WO[h][i][k]` | 2^32 |
| `attention(x)` | the sum of `head_output` over the four heads | 2^32 |
| `residual(x2, att)` | `r[k] = x2[k] * 2^24 + att[k]` | 2^32 |
| `mlp_hidden(r)` | `pre = sum over k of r[k] * WIN[k][i] + BIN[i] * 256`; `m[i] = pre >> 8` if `pre > 0`, else `0` | 2^32 |
| `mlp_output(m)` | `o[k] = sum over i of m[i] * WOUT[i][k] + BOUT[k]` | 2^40 |
| `final_stream(r, o)` | `fin[k] = (r[k] * 256 + o[k]) >> 16` | 2^24 |
| `unembed(fin)` | `l[c] = sum over k of fin[k] * U[k][c]` | 2^32 |
| `argmax(l)` | the index of the largest entry, the smallest such index on a tie | |

Rounding: `>>` on an `i64` is the arithmetic shift, which rounds toward minus infinity. The one
division, in `softmax_weights`, has a numerator that is not negative and a positive denominator.

Every loop is a `while` loop with a constant number of iterations, at most 512.

`project` and `head_scores` depend only on the head, the position and the token, not on the pair:
over all inputs there are 4 query vectors, 908 key vectors, 908 value vectors and 908 scores
(4 heads times 113 tokens at position 0, 113 tokens at position 1 and the token 113 at
position 2).

## Preconditions of the stage functions

The stage functions are public and index tables with their arguments. `predict` and `logits`
call them only inside these ranges.

- `embed(tok, pos)`: `tok < 114` and `pos < 3`.
- `head_scores(h, x)` and `head_output(h, x, alpha)`: `h < 4`.
- `forward(a, b)`: `a < 113` and `b < 113`.
- `exp_fix(d)`: none. It returns for every `d: i64`.

## Facts that may serve as invariants

These are not verified facts. `scripts/check_transformer_int.py` checks the tables, computes the
bounds from the weights, and measures the program on all 12,769 pairs.

- Every entry of `EXP_N`, `EXP_2`, `EXP_1` and `EXP_0` is between `0` and `2^30`, and entry `0` of
  each is `2^30`. So `exp_fix(d)` is between `0` and `2^30` for every `d`, each of its products
  is at most `2^60`, `exp_fix(d) == 2^30` when `d <= 0`, and `exp_fix(d) == 0` when
  `d >= 32 * 2^32`.
- In `softmax_weights`, the position with the largest score has `e == 2^30`. So the denominator
  is between `2^30` and `3 * 2^30`, each `alpha[j]` is between `0` and `2^24`, and
  `alpha[0] + alpha[1] + alpha[2] <= 2^24`.
- For `a, b < 113`, every value a stage computes, with every product and every partial sum
  inside it, has absolute value at most:

| Stage | Bound | Bits |
| --- | --- | --- |
| `embed` | 117 | 7 |
| `project` | 252131 | 18 |
| `head_scores` | 38072233599 | 36 |
| `exp_fix` (`max(s) - s[j]`, table products) | 1152921504606846976 | 61 |
| `softmax_weights` (`e[j] * 2^24`, the denominator) | 18014398509481984 | 55 |
| `head_output`, the mix before `>> 16` | 4230056247296 | 42 |
| `head_output`, the product with `WO` | 68590555392 | 36 |
| `attention` | 219396556032 | 38 |
| `residual` | 219950204160 | 38 |
| `mlp_hidden` | 570593785990656 | 50 |
| `mlp_output` | 11627504833770005 | 54 |
| `final_stream` | 11668949407347221 | 54 |
| `unembed` | 311355550586446 | 49 |

  Each bound is a sum of absolute values pushed through the stages: the largest `|x[k]|` over
  the tokens a position can hold, then `sum over k of bound[k] * |w[k][i]|` for each matrix. An
  `i64` holds 63 bits.

## Not claimed

- Nothing here is about the floating-point checkpoint or about a real-valued softmax. The object
  is this integer program.
- This program is not the integer program of lean-checked-network's
  `TransformerBridge.FinalRaw.raw_model_adds_mod_113`. It uses the same integer weights. Its
  softmax and its rescaling differ, and no proof relates the two.
- Termination is not a property to verify. Every loop bound is a constant.
