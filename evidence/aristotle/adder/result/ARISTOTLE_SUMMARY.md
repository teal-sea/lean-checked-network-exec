# Summary of changes for run 8c9b7aea-f9a9-47a8-ac2e-3073a347acb2
I proved all five properties in SPEC.md about the `adder` crate as submitted, built with the release profile and `overflow-checks = true`. The proofs are machine-checked against the compiled code of `src/lib.rs`, use only Lean's standard axioms, and contain no `sorry`. I did not change any Rust source or Cargo file.

The public contracts are in `Spec/Adder.lean`, built on the model in `Spec/Model.lean`. The Properties table lists each one, marked proved:

1. **No panics** (`Spec.no_panics_spec`): no call to `step`, `out`, `carry`, `add_bits` or `add_u64` panics, for any arguments. That covers every 4-unit state `h`, all bits, all `u64` pairs and every slice length, including empty ones. Every checked addition, shift and index is shown never to reach its panic branch.
2. **Length mismatch** (`Spec.add_bits_length_mismatch_spec`): if `sum.len() != xs.len()`, `add_bits` returns `None` and leaves `sum` unchanged.
3. **Ripple-carry adder** (`Spec.add_bits_ripple_spec`): if the lengths are equal, `add_bits` returns `Some(c_n)` and `sum[i] == s_i` for every `i`, for any length.
4. **It adds** (`Spec.add_bits_adds_spec`): under the same condition, `val(sum) + 2^n * bit(c) == A + B`, as unbounded natural numbers.
5. **64-bit addition** (`Spec.add_u64_spec`): `add_u64(a, b) == a.overflowing_add(b)`.

I also proved the hint from SPEC.md rather than assuming it: the 20-case `REACH` certificate, and the loop invariant that the state stays in `REACH` and its carry is the ripple carry so far.

**Verified:** `step`, `out`, `carry`, `add_bits`, `add_u64` and the private helpers `dot_b` and `thr` they call, against their actual compiled code. The two `slice::len` calls `add_bits` makes, and the `ptr::metadata` calls inside them, were also proved from their compiled code. No external dependency is assumed.

**Conditions on these results:**
- **Partial correctness.** Each result says what holds if the call returns. Termination is not proved. These are fixed-bound loops, so this is a limitation of the method rather than a concern about the code.
- **Valid references.** Callers must pass valid slice references and own the memory behind them: a share of the `xs` pairs, a share of `h`, and the elements of `sum`. Every safe Rust caller meets this.
- **Weight constants.** The contracts assume the read-only constants for `WH`, `WO` and `WC` hold the little-endian bytes of `weights.rs`. A separate proof shows this holds from program start-up, so it is not an added assumption about the data.
- **Object size.** As usual for Rust results, every object is assumed to be smaller than \(2^{56}\) bytes. The slice-size bounds the proofs need actually come from the validity of the slice references themselves.

**Not verified:** nothing among the requested claims remains open. The `REACH` constant itself is not read by the evaluator, so it is outside the scope.