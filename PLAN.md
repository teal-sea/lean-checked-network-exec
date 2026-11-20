# Plan: prove the engine, not the network

Set by Thomas on 2026-11-18. His words, after the plan was put to him: "yeah so document that as
the plan". It replaces gate 5 of the first plan. [STATUS.md](STATUS.md) tracks the gates below.
Numbers come from `evidence/` unless a line says otherwise.

## Why the first plan stopped

The first plan proved one network at a time. Gate 1A did the adder. Gate 5 was the same job for
one transformer.

- **A proof about a small Rust program can now be rented.** Harmonic released its Rust prover on
  2026-11-16. On 2026-11-17 it proved the adder in 71 minutes and the MLP in 63, each from one
  page of English (STATUS rows 1R and MLP-R).
- **Both routes stall on the weights written into the code.** `rust/transformer` holds 226,688
  weights as constants in a 1.1 MB file. Aristotle spent 207.6 credits on that crate, took
  2 h 17 min to state three properties and proved none (STATUS row 5R). Aeneas's translation of
  a table of 14,464 literals does not elaborate in Lean (`evidence/mlp`).
  *Corrected 2026-11-20: Aristotle did not stall. The run finished 51 minutes after stating the
  properties, 3 h 8 min in all, with all three proved (STATUS row 5R). It had been read while
  still in progress on a zero balance. The Aeneas half of this bullet stands.*
- **The code is small.** `rust/transformer/src/lib.rs` is 339 lines.
- **One proof per network repeats the whole job for the next network.**

## The change

The weights become an input. One theorem then covers every weights file:

> For every weights file that passes the load check, the Rust forward pass returns exactly what
> the Lean model returns. It does not panic, overflow or index out of range.

No table enters that proof. A trained network then needs only its own check on the Lean model,
which gate 4 already does in the kernel. The mod 113 transformer is the first network on the
engine, not the product.

## Where this ends

A small language model that answers in a browser, running on a Rust engine whose every
arithmetic step is covered by that theorem. The engine uses integers only, so the same input
gives the same bits on every machine.

On 2026-11-17 two web searches found no Rust transformer engine proved against a Lean
specification. The nearest were TorchLean (a Lean framework, no Rust engine) and int-llm
(TinyLlama in integer-only C, no proof). That is two searches, not a survey. Search again
before any public sentence says "first".

## The gates

Caps are proposed, in agent-days, as in the first plan.

### E0. The weights become an input

The one-hour test. Everything after it depends on it.

Work:

1. A new crate `rust/engine`, `#![no_std]`, `#![forbid(unsafe_code)]`, `overflow-checks = true`
   in both profiles. It holds a `Weights` struct with the fifteen tables of
   `TransformerInt.Weights` as fixed-size arrays (eleven weight tables, four exponential tables)
   and the sixteen functions of `rust/transformer/src/lib.rs`, each taking `w: &Weights`. Nothing
   else changes. The crate contains no weights.
2. `rust/transformer` keeps its public functions. It builds one `static` of type
   `engine::Weights` from its generated tables and calls the engine.
3. `scripts/translate.sh engine`, then `scripts/build.sh`.

Passes when all four hold:

- `rust/transformer`'s tests pass unchanged: all 12,769 pairs, and the logits hash
  `6cb24f7670e8562e` in `tests/fixtures/python_reference.txt`.
- The translation succeeds, with the script's own check for `axiom`, `opaque` and `sorry`.
- `lean/LcnExec/Translated/Engine.lean` contains no weights table. Record its size and line
  count.
- Lean builds it. Record the seconds and the peak memory.

If it fails: write what failed under `evidence/engine/e0/` and stop. Thomas decides what next.

Cap: half an agent-day.

### E1. The load check

The Rust panics on overflow. Aeneas models that as failure. So the theorem needs every
intermediate value to fit in an `i64`, and that depends on the weights.

- For arbitrary `i8` tables the worst case does not fit. A hand estimate on 2026-11-18 puts the
  sums of `mlp_output` near 2^68. Redo the estimate before relying on it.
- `scripts/check_transformer_int.py` (`static_bounds`) already computes one bound per stage from
  the weights alone. Each bound covers every product and partial sum of its stage. For the
  trained weights the largest is 61 bits (`evidence/transformer-int/summary.txt`).

Work: the same computation as a Lean function `Bounds.ok : TransformerInt.Weights → Bool`, in
core Lean. It also checks the shape of every table, that the exponential tables lie in
`[0, 2^30]`, and the ranges of `bin` and `bout`.

Passes when:

- `Bounds.ok` reproduces the thirteen static bounds of the Python script on the trained weights.
- `Bounds.ok` of gate 4's `Gen.weights` is `true` by `decide +kernel`. Record the time.
- Control: a weights file built to overflow is rejected by `Bounds.ok`, and the Rust really
  panics on it.

Cap: one agent-day.

### E2. The engine theorem

The statement. Names may change. The meaning may not.

```lean
/-- The arrays of the translated `Weights`, read as the lists of the model. -/
def spec : engine.Weights → TransformerInt.Weights

theorem engine.logits_eq (W : engine.Weights) (h : Bounds.ok (spec W) = true) (a b : Usize) :
    engine.logits W a b = ok ((TransformerInt.logits (spec W) a.val b.val).map toArray)

theorem engine.predict_eq (W : engine.Weights) (h : Bounds.ok (spec W) = true) (a b : Usize) :
    engine.predict W a b = ok ((TransformerInt.predict (spec W) a.val b.val).map toUsize)
```

`ok` is Aeneas's result for a run with no panic, no overflow and no index out of range. The
theorem holds for every `a` and `b`, in range or not.

`TransformerInt/Model.lean` moves from `pilot/transformer-int` into `lean/`. It is core Lean and
210 lines.

The repository's method applies unchanged:

- Axioms on the allowlist only.
- nanoda rechecks the theorems.
- A planted fault must be caught. Here the fault goes into the code, since the weights are no
  longer in it: change one shift amount, one scale constant, and `>` to `>=` in `argmax`.
  Retranslate each. The proof must fail to build.
- Compile-and-diff: the Rust binary against the Lean evaluator compiled natively, on the trained
  weights and on at least one random weights file that passes the check.

What the proof needs, as read on 2026-11-17 in `toolchain/aeneas/backends/lean`:
`IScalar.ShiftRight_spec` gives `z.val = x.val >>> y.val`, and the division spec gives
`Int.tdiv`. Both match the model. `LcnExec/Adder/Proofs.lean` is the pattern for loop invariants.
More in `notes/2026-11-17-aeneas-lane.md`.

Cap: five agent-days.

### E3. The first network: mod 113, end to end

1. The static in `rust/transformer` equals gate 4's `Gen.weights`. Translate the weights with
   one constant per row (`scripts/mlp_row_consts.py` is the pattern; 339 rows elaborated in 134
   to 181 s for the MLP) and prove the equality row by row with `decide +kernel`.
2. `Bounds.ok Gen.weights = true`, from E1.
3. Compose with gate 4's `adds_mod_113`:

```lean
theorem transformer.adds_mod_113 (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    transformer.predict a b = ok (some ((a.val + b.val) % 113))
```

4. A second weights file of the same shape, any other checkpoint. It gets its theorem by
   rerunning `scripts/gate4.sh` and the check of E1. The gate passes only if no file of E2
   changes between the first network and the second.

To decide inside this gate: how gate 4's project joins the build. It is 136 modules and 44
minutes at two jobs, and CI's limit is 180 minutes.

Cap: three agent-days.

### E4. The general engine

Layers, context length, attention over every position with a causal mask, a generation loop.
The Lean model grows the same way. The load check becomes a Rust function proved to imply
`Bounds.ok`, so `predict` needs no hypothesis after a successful load.

Four decisions, each settled by a small test before any proof:

1. Const generics or slices, whichever Aeneas at this pin translates.
2. Overflow for long inputs: clamp at stage boundaries, or bounds from absolute row sums.
3. Normalisation: none, or an integer one.
4. Tokens: bytes or a small fixed vocabulary. Greedy decoding first. Sampling takes its seed as
   an input.

Passes when E2's theorem holds for the general engine and the mod 113 network gives the same
answers on it for all 12,769 pairs.

Cap: six agent-days.

### E5. A small language model

Trained for the engine's shape, quantised, measured against its floating-point original, run
natively. It must pass the load check. Evidence: sizes, tokens per second, the quality numbers.
The theorem is about the engine. Nothing is proved about what the model says.

Cap: three agent-days.

### E6. The browser

The same crate compiled to WebAssembly, and a page where a person types and the model answers.
The page states what the proof covers: the Rust source under Aeneas's semantics. The wasm binary
is trusted through rustc and the wasm toolchain, as the native binary is trusted through rustc.

Cap: two agent-days.

### E7. Write-up

The first plan's gate 6: audit surface as line counts, trusted tools by name and version, all
from `evidence/`.

### E8. Publish

The first plan's gate 7. On Thomas's separate yes.

## What stops

| First plan | Now |
| --- | --- |
| Gate 5, the transformer in Rust proved like 1A | Replaced by E0 to E3 |
| Gate 1B, the adder in C to Aristotle | Dropped. His words on 2026-11-17: Rust is the target. `c/adder` stays in the tree, written and tested, never submitted |
| `rust/mlp` | Stays as Aristotle proved it (row MLP-R). No further work. The route through Aeneas is recorded in `evidence/mlp` and `pilot/mlp-row-consts` |
| Gates 6 and 7 | Carried as E7 and E8 |

## What is already proved, and stays

| What | Where |
| --- | --- |
| The adder in Rust equals RnnAdder for every input: ten theorems, nanoda, planted faults, diff | Gate 1A, `lean/LcnExec/Adder/Proofs.lean`, `evidence/gate1a` |
| The same adder file proved by Aristotle, 5 of 5 | Row 1R, `evidence/aristotle/adder` |
| The MLP in Rust proved by Aristotle, 5 of 5, with its `unsafe` twin | Row MLP-R, `evidence/aristotle/mlp` |
| The transformer as an `i64`-only program, right on all 12,769 pairs by test | Gate 3, `evidence/transformer-int` |
| The Lean model of that program, kernel-checked on every pair, replayed 135 of 135 | Gate 4, `pilot/transformer-int`, `evidence/gate4` |

One item is still open from gate 1A. Its ten theorem names are in
`evidence/gate1a/proposed-theorems.txt` and not in `gates/theorems.txt`, so CI does not check
them. Agents do not edit `gates/`. It is Thomas's edit.

## What the theorem will not say

- Nothing about rustc or LLVM. The binary is trusted through them.
- Nothing about Charon or Aeneas. The translation is trusted.
- Nothing about the floating-point model. The integer program is the object. Tests compare the
  two; no proof does.
- Until step 1 of E3, the weights in the Rust and in Lean agree only because the same scripts
  generate both from one checkpoint.

## Side lanes, each Thomas's call

None of these blocks a gate.

- **Aristotle on `rust/engine`.** After E0 the engine is about 339 lines with no table. The two
  crates Aristotle finished in about an hour each were smaller, and neither carried a 1.1 MB
  table. The account balance is 0. Buying credits is his call.
  *Corrected 2026-11-20: Aristotle also finished `rust/transformer`, table included, in 3 h 8 min.*
- **Schematic.** Its founder offered credits. `super link` uploads the repository's committed
  source, so it waits for his word. A repository holding only `rust/engine` would upload nothing
  else.
- **The Lean kernel finding.** The kernel hashes a number literal by its value mod 2^64. Packing
  14,464 entries took 28.5 s at base 2^64 and 2.47 s at an odd base. The source lines and the
  measurements are in `notes/2026-11-17-gate4-pilot.md`. The two benchmark files were not kept;
  rebuild them from `pkI` in `pilot/transformer-int/TransformerInt/Fast.lean`. Search Lean's
  issue tracker before writing: nobody here has checked whether it is known. Sending it is his.
- **A note on Aristotle's first week on Rust.** The numbers are STATUS rows 1R, MLP-R and 5R.
  Writing and sending it is his.
- **Later, not scheduled.** Aristotle proved that the trained adder's `add_u64` equals
  `u64::overflowing_add`. Read the other way, that is a network turned back into one line of code
  with a proof. A tool that finds the line by itself would be a separate project.

## Picking this up on another machine

The scripts need elan, rustup, Python 3, git, curl, make, a C compiler and linker, rsync and
perl. About 12 GB of disk.

```sh
git clone --recurse-submodules https://github.com/teal-sea/lean-checked-network-exec
cd lean-checked-network-exec
toolchain/install.sh          # pinned Aeneas binary, Charon built from its pinned commit
scripts/gate1a.sh             # optional: replays gate 1A, about 20 minutes on 4 cores
```

Then start at E0.

What went wrong on the last machine, a Linux container, on 2026-11-17:

- With `nix` on `PATH`, Charon's installer takes the Nix route and can fail on a download. The
  run that worked had `PATH` without it.
- `rsync` was missing. `scripts/plant_wrong_weight.sh` needs it.
- Charon's build directory (`toolchain/aeneas/charon/charon/target`) is 11 GB. It can be deleted
  after the install; the binaries are copies.
- A cold `scripts/build.sh` took 10 to 13 minutes on 4 cores. `lake exe cache get` took 82 s.
- Lean reserves 5 to 9 GB of virtual memory. A `ulimit -v` below that stops it from starting.
- Gate 4 does not need Aeneas. `scripts/gate4.sh build` regenerates and builds it: 44 minutes at
  two jobs.

The Aristotle key is not needed for E0 to E7. It is a network secret on Thomas's Default cloud
environment and exists nowhere in this repository.
