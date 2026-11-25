# Runtime-weights Rust engine: pilot scope

## What exists today

The base is commit `41c25c1` on `origin/claude/ecstatic-turing-axe4ir`.
`rust/transformer/src/lib.rs` uses fixed trained constants. It evaluates the last token of
`[a, b, =]` with integer attention, two residuals, a ReLU MLP and a first-on-ties argmax.
`pilot/transformer-int/TransformerInt/Model.lean` instead already takes `Weights` at runtime.
Its arithmetic is unbounded `Int`, not Rust machine arithmetic. The gate 4 result is recorded
in `evidence/gate4/summary.txt`. Its generated `TransformerInt.Gen` sources and objects are not
in this checkout. This pilot does not rebuild that proof.

This branch adds `rust/engine`. Its library has no trained constants or dependency on the
old transformer. A fixed-array `Weights` struct carries every matrix, bias and exponential
table. The trained constants enter only through the integration tests' development dependency.
The original transformer, gate scripts and workflows are unchanged.

## Idea and exact claim

Check the dimensions by Rust types and the magnitudes once with `load_check`. Evaluate with
an immutable weights reference. Prove the Rust-to-model relation for every accepted value,
then instantiate it at the trained weights. No enumeration over weights is involved.

The exact universal goal is `LcnExec.Engine.EngineCorrect` in
`lean/LcnExec/Engine/Contract.lean`. It requires the **translated Rust** load check to return
`ok true`, both input bounds, and an `ok (some r)` prediction whose natural value is exactly
`TransformerInt.predict (toModel W) a b`. The existential only exposes the machine scalar;
it does not allow wrapping or an arbitrary relation. `toModel` reads all runtime fields.
`lean/LcnExec/Engine/Correct.lean` proves this universal goal.
`pilot/engine/Statement.lean` retains the historical draft and gives the exact trained
end-to-end target. All draft holes are outside the Lake library.

The trained target uses `ofModel TransformerInt.Gen.weights`. That total encoding wraps
out-of-range entries, so **both** `trained_load_ok` and `trained_weights_eq` are explicit,
currently open obligations. Do not silently assume the encoding is faithful. The checked
`compose` lemma shows the precise implication from engine correctness, those obligations,
and the gate 4 theorem to the trained end-to-end equality.

## Accepted load box and overflow argument

`Weights` fixes every array dimension. The checker enforces these absolute entry bounds:
`tok` 68, `pos` 59, `wq` 5, `wk` 22, `wv` 106, `wo` 93, `win` 82,
`wout` 74, `u` 37, `bin` 2^30 and `bout` 2^37. Every exponential table entry is in
[0, 2^30]. These are sufficient bounds, not a characterization of every safe weights value.
The trained weights pass the real checker (`pilot/engine/rust-tests.log`).

`scripts/engine_bounds.py` records the integer calculations in `pilot/engine/bounds.json`.
The following explains the integer envelopes. Package 2 now proves load-check soundness
and the stage propagation in Lean; the executable integer arithmetic remains supporting
evidence. At a maximal score, `exp_fix(0)` is 2^30 regardless of table contents.
All other exponentials stay in [0, 2^30], so the denominator is positive. The three softmax
coefficients are nonnegative and their sum is at most 2^24, since the sum of the floored
quotients is at most the unfloored sum. Thus the signed weighted value sum has magnitude
at most `V * 2^24`, including each partial sum. Its arithmetic right shift has magnitude
at most `V * 256`, since that endpoint is an integer. Do not replace this reasoning by
three independent coefficient maxima, which would lose the useful bound.

For other contractions, the sum of absolute term bounds bounds every prefix, not just the
final sum. ReLU is nonnegative. For the final signed shift use a ceiling of the absolute
numerator divided by 2^16. The largest derived pre-shift magnitude is
8,161,836,649,496,444,928, below the `i64` maximum 9,223,372,036,854,775,807.
Exponent table products are at most 2^60; softmax numerators at most 2^54. All counters are
bounded by their fixed array sizes. Formal propagation is now proved in the stage modules
listed below.

## Forward stages and proof obligations

Every row below is proved for the translated fixed-array engine.
Generated code: `lean/LcnExec/Translated/Engine.lean`.
The shared stage statements and envelopes were frozen in commit `d02b3df` before proof work.
Unproved draft statements remain only under `pilot/`; the accepted theorem is in `Correct.lean`.

| Stage | Required proof obligation | Aeneas result | Current proof |
| --- | --- | --- | --- |
| Load check | Accepted values imply entry bounds; loop indices safe | Yes after control-flow repair | Proved: `LcnExec.Engine.Load` |
| Embedding | Pointwise sum; magnitude at most 127 | Yes | Proved: `LcnExec.Engine.Projection` |
| Q/K/V projections | Ordered matrix-vector loops equal model `lincomb`; prefix bounds | Yes | Proved: `LcnExec.Engine.Projection` |
| Score dot | Loop equals `TransformerInt.dot`; multiplication and accumulation safe | Yes | Proved: `LcnExec.Engine.Dot`, applied by `Projection` |
| Score assembly | Projection results satisfy the dot bound and select correct head/position | Yes | Proved: `LcnExec.Engine.Projection` |
| Exponential lookup | Shift, cast and mask agree with model quotient/remainder; table indices safe | Yes | Proved: `LcnExec.Engine.Exponential` |
| Softmax | Max exists, denominator positive, truncating division, coefficient-sum bound | Yes | Proved: `LcnExec.Engine.Softmax` |
| Value mixing | Signed shifts agree; preserve the joint coefficient bound | Yes | Proved: `LcnExec.Engine.Mixing` |
| Output projection | Model `lincomb`, bounded signed partial sums | Yes | Proved: `LcnExec.Engine.Mixing` |
| Attention sum | Four head outputs match model addition order | Yes | Proved: `LcnExec.Engine.Attention`, discharged in `Correct` |
| First residual | Scale 2^24 and sum match model, no overflow | Yes | Proved: `LcnExec.Engine.Downstream` |
| MLP input and ReLU | Dot, bias scaling, branch and shift agree | Yes | Proved: `LcnExec.Engine.Downstream` |
| MLP output | Dot plus bias; prefix bounds below machine limit | Yes | Proved: `LcnExec.Engine.Downstream` |
| Final residual | Signed shift by 16 agrees with `Int.shiftRight` | Yes | Proved: `LcnExec.Engine.Downstream` |
| Unembedding | Model `lincomb` and all logit prefix bounds | Yes | Proved: `LcnExec.Engine.Downstream` |
| Argmax | First index wins ties; result in range | Yes | Proved: `LcnExec.Engine.Argmax` |
| Forward/predict | Compose stages, input guard and `Option` representation | Yes | Proved: `LcnExec.Engine.Correct` |

## Measurements and evidence

- Package 2: the exact universal theorem compiled in 10.723 s with peak RSS 2725392 KiB
  (`pilot/engine/correct2-03.json`). Its separate leanchecker replay passed in 13.602 s
  with peak RSS 2288860 KiB (`pilot/engine/correct2-replay.json`). The axiom report uses
  only the standard three.
- Per-module build/replay measurements, 91 new proved declarations, complete source/object
  hashes and the passing changed-index control are in `pilot/engine/package2-ACCEPTED.json`
  and the current section of `pilot/engine/REPORT.md`.

The following measurements are retained from package 1:

- Rust: all 12,769 input pairs, all 1,442,897 logits and every prediction agree with the
  unchanged transformer. Three integration tests passed. Command wall time 22.884 s,
  peak RSS 152380 KiB. See `pilot/engine/rust-tests.log` and `.json`.
- Real dot lemma: successful single-module build 14.291 s wall,
  peak RSS 2735620 KiB. See `pilot/engine/dot-02.json` and `.log`.
- Its transitive axiom audit lists only `propext`, `Classical.choice`, `Quot.sound` in that log.
- A separate `leanchecker` replay of the dot module passed in 18.832 s,
  peak RSS 2266928 KiB. See `pilot/engine/dot-replay.json` and `.log`.
  This is not a nanoda check or a fresh replay of the full Mathlib closure.
- Translation pins and input/output hashes: `evidence/translate/engine/summary.txt`.

The Lean checks used two threads under `MemoryMax=6G`, `CPUQuota=200%`, after checking host
headroom. Existing Mathlib and Aeneas objects were reused. No full Lake build was run.

## Risks

The joint softmax bound and signed rounding are now proved, not assumed.
The translation and Rust compiler remain trust boundaries; neither is certified here.
The scalar load box intentionally has little headroom at the MLP output. Larger load bounds
need a new derivation. In-memory Rust types enforce shape; no byte-file parser is provided.
Calling public forward helpers on unchecked or out-of-range values is outside the contract.
`predict` checks input range, but callers must establish `load_check` before using arbitrary
weights. Safe Rust's immutable reference prevents mutation during that call.

The original nested early-return load checker hit an Aeneas limitation. A validity accumulator
removes the outer-loop exit. The minimal reproduction and its observed diagnostic live under
`pilot/engine/failures/nested-return/repro`; the original full failed source and logs are also
retained. No slices or flat-vector fallback was needed.

## Numbered plan and measurable stop gates

Package 2 has completed steps 2 through 6. The final theorem, each new module replay,
standard-axiom audit and planted Rust indexing fault control passed. Detailed evidence and
per-module measurements are in `pilot/engine/REPORT.md`. Step 7 is not part of package 2.

1. **Pilot acceptance, this branch.** Stop gate: trained load succeeds; every old/new logit and
   prediction agrees; the full library translates; the numeric dot proof builds and its axiom
   list has only the standard axioms. These gates passed in package 1.
2. Prove load-check soundness, table bounds and generic interval lemmas. Stop gate: one checked
   module proves each accepted entry bound and every bound in `bounds.json`; rejected-load
   controls remain rejected. Do not start the remaining forward proof before this gate passes.
3. Prove projections and score assembly. Stop gate: all Q/K/V coordinates and scores match the
   unchanged model for arbitrary accepted runtime weights, with ordinary success equations.
4. Prove exponentiation and softmax. Stop gate: quotient/remainder and signed-shift identities,
   positive denominator and the coefficient-sum inequality compile; test ties and zero tables.
5. Prove mixing, attention, both residuals and the MLP. Stop gate: every stage has an `ok`
   equivalence, including no-overflow for every accumulator prefix.
6. Prove unembedding, tie-breaking and the universal `EngineCorrect` target. Stop gate: no
   placeholders, complete axiom audit, independent kernel recheck, and a genuine changed
   arithmetic control rejected for the intended semantic reason.
7. Restore authenticated gate 4 generated artifacts, prove the trained load/encoding facts,
   compose the final target and run the repository's release gates on approved build compute.
   Stop gate: final theorem checked, full closure rechecked, pinned Rust/Lean differential
   tests and remote branch receipt retained. Gate registration requires Thomas's review.

## Out of scope and build machine

Package 2 proves the full universal engine theorem, exactly as stated in `Contract.lean`.
It does not change the model or requantize weights, prove a byte parser, certify rustc or
the binary, add SIMD/GPU operations,
edit gates/workflows, merge, or publish anything publicly. Gate 4 was not independently
rechecked here. The draft file's generated gate 4 import is absent locally, so that full
file was not elaborated; its universal contract and generic composition were checked.

The measured two-thread, 6 GiB envelope was sufficient for every package 2 module.
All kernel operations were serialized through the shared host lock. No rental or paid
service was launched. Gate 4 restoration and trained-instance work need a separate package.
