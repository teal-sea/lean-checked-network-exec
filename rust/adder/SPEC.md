# Formally verify the recurrent adder

`src/lib.rs` evaluates a small trained recurrent neural network. Its integer weights are the
constants in `src/weights.rs`. Verify the properties below of the crate as submitted, built with
the release profile in `Cargo.toml` (`overflow-checks = true`).

## Definitions

For a slice `xs` of `n` bit pairs `(a_i, b_i)`, the ripple-carry adder defines

- carries: `c_0 = false` and `c_{i+1} = (a_i && b_i) || (a_i && c_i) || (b_i && c_i)`,
- sum bits: `s_i = a_i ^ b_i ^ c_i`, for `i < n`.

For a slice of bits `v`, `val(v)` is the natural number `sum over i of bit(v[i]) * 2^i`, where
`bit(true) = 1` and `bit(false) = 0`. It is a mathematical integer, least significant bit first,
with no bound on its size.

## Properties

1. **No panics.** No call to `step`, `out`, `carry`, `add_bits` or `add_u64` panics, for any
   arguments. In particular no integer operation overflows and no index is out of bounds.

2. **`add_bits` checks the lengths.** If `sum.len() != xs.len()`, then `add_bits(xs, sum)`
   returns `None` and leaves every element of `sum` unchanged.

3. **`add_bits` is the ripple-carry adder, for every length.** If `sum.len() == xs.len()`, with
   `n = xs.len()` any length, then `add_bits(xs, sum)` returns `Some(c_n)`, and on return
   `sum[i] == s_i` for every `i < n`.

4. **`add_bits` adds, for every length.** Under the condition of property 3, let `A` be `val` of
   the first components of `xs` and `B` be `val` of the second components. On return,
   `val(sum) + 2^n * bit(c) == A + B`, where `Some(c)` is the returned value.

5. **`add_u64` is 64-bit addition.** For all `a: u64` and `b: u64`,
   `add_u64(a, b) == a.overflowing_add(b)`. That is, the first component is `a + b` modulo `2^64`
   and the second is `true` exactly when `a + b >= 2^64` as mathematical integers.

## A hint, not an assumption

Prove this or ignore it; nothing may be assumed from it.

Starting from `H0`, the state stays inside the five states listed in `REACH`. For every `h` in
`REACH` and each of the four pairs `(a, b)`:

- `step(h, a, b)` is in `REACH`,
- `carry(step(h, a, b)) == (a && b) || (a && carry(h)) || (b && carry(h))`,
- `out(h, a, b) == a ^ b ^ carry(h)`,

and `carry(H0) == false`. These are 20 finite cases. With "the state is in `REACH` and
`carry(state)` is the ripple carry so far" as the loop invariant, properties 3, 4 and 5 follow by
induction over the loop.
