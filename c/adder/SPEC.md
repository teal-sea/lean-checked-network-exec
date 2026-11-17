# Follow-up: the C original of this crate

The files `c/adder.c`, `c/adder.h` and `c/weights.h` are added to this project with this
message. They are the same trained recurrent network as the Rust crate you already verified,
written in C11, function for function. The integer weights in `c/weights.h` are the same numbers
as in `src/weights.rs`.

Verify the properties below of the C sources as submitted, and relate them to the Rust.

## Caller obligations for the C functions

- `adder_step(h, a, b, next)`: `h` points to 4 readable `bool` objects, `next` points to 4
  writable `bool` objects, and the two arrays do not overlap.
- `adder_out(h, a, b)` and `adder_carry(h)`: `h` points to 4 readable `bool` objects.
- `adder_add_bits(xs, n, sum, sum_len)`: `xs` points to `n` readable `adder_bit_pair` objects
  (it may be any pointer when `n == 0`); `sum` points to `sum_len` writable `bool` objects (it may
  be any pointer when `sum_len == 0`); the two arrays do not overlap.
- `adder_add_u64(a, b, carry)`: `carry` points to one writable `bool`.

Every `bool` object read holds a valid `bool`, 0 or 1.

## Properties

C1. **Memory safety.** Under the caller obligations, every function in `c/adder.c` executes
    without undefined behavior. In particular no signed arithmetic overflows.

C2. **`adder_add_u64` behaves the same as the Rust `add_u64`.** For all 64-bit unsigned `a` and
    `b`: `adder_add_u64(a, b, &carry)` returns `s` and stores `c` in `carry` exactly when the
    Rust `add_u64(a, b)` returns `(s, c)`. So the C also returns `(a + b) mod 2^64` and stores
    whether `a + b >= 2^64`.

C3. **`adder_add_bits` behaves the same as the Rust `add_bits`.** Let the Rust slice `xs` hold
    the same `n` pairs as the C array `xs`, and let the Rust `sum` and the C `sum` have the same
    length `sum_len` and the same initial contents.
    - If `sum_len != n`: the C returns `-1` and leaves `sum` unchanged, and the Rust returns
      `None` and leaves `sum` unchanged.
    - If `sum_len == n`: the C returns `1` when the Rust returns `Some(true)` and `0` when the
      Rust returns `Some(false)`, and on return the two `sum` arrays hold the same bits.

C4. **The step functions behave the same.** For every state `h` (4 bits) and all bits `a`, `b`:
    `adder_step` writes to `next` the state the Rust `step(h, a, b)` returns;
    `adder_out(h, a, b)` equals the Rust `out(h, a, b)`; `adder_carry(h)` equals the Rust
    `carry(h)`.

Termination is not requested: each property is about calls that return.
