# The trained runtime-weight engine theorem

## Current status

For the pinned quantised trained constants, Lean proves that this fixed-size integer-transformer engine's Charon/Aeneas-translated computation returns `(a + b) % 113` for every input pair below 113, without an accuracy hypothesis, with fresh Lean replay and nanoda checking of the final theorem's exported dependency closure, while checkpoint interpretation, extraction and compiled Rust or Wasm execution remain outside the proof.

Accepted run: producer `0c346acb76b568249a41f46c39ff56caf33442ab`, 2026-11-18. `pilot/engine/final-run-20261118/attempt-3/VERDICT.json` authenticates the run, exact theorem type, byte-identical fresh extraction, standard-three axiom audit, fresh whole-closure replay, nanoda verdict and planted-axiom rejection. Nanoda reported 31,942 declarations with no typechecker errors and one axiom pretty-printer error. This is a private artifact, not a public release. Earlier package sections below retain dated historical results.

## The problem

The existing theorem `engine_correct : EngineCorrect` proves that the translated Rust engine succeeds and agrees with the mathematical integer transformer for every accepted weight value and valid input. It does not prove that any weights are accepted, or that a particular trained checkpoint has useful answers. Gate 4 separately proves modular addition for the trained mathematical weights. This package connects those claims without rebuilding gate 4's input rows on the shared host.

## The idea

Generate a value of the translated Rust `engine.Weights` type from the same hash-pinned checkpoint and quantisation as gate 4. Reuse gate 4's generated integer rows, wrap them as machine scalars, and kernel-check each row's decoding and bounds. Assemble the rows with ordinary list lemmas. A generic completeness proof shows that these bounds make the actual translated load checker terminate and accept. Compose the accepted engine theorem with exact weight equality and an explicit hypothesis containing gate 4's accuracy statement. The separate unconditional final module has now passed the dedicated build and final checks.

## The exact statement

The checked module is `LcnExec.Engine.Trained`. Its main theorem is:

```lean
theorem trained_engine_adds_of
    (gate4 : ∀ a, a < 113 → ∀ b, b < 113 →
      TransformerInt.predict TransformerInt.Gen.weights a b = some ((a + b) % 113))
    (a b : Usize) (ha : a.val < 113) (hb : b.val < 113) :
    engine.predict trainedRust a b =
      ok (some (Usize.ofNat ((a.val + b.val) % 113) (by scalar_tac)))
```

The same module proves:

```lean
trained_load_ok : engine.load_check trainedRust = ok true
trained_view : toModel trainedRust = TransformerInt.Gen.weights
accepted_weights_nonempty : ∃ W, engine.load_check W = ok true
```

`trained_engine_adds_of` uses `compose engine_correct`, not a new evaluator. The checked module `LcnExec.Engine.TrainedFinal` imports `TransformerInt.Gen.AllRows` and supplies `TransformerInt.Gen.adds_mod_113` to obtain `trained_engine_adds`, with no accuracy hypothesis. **That final module passed the dedicated package 6 run.** Its type has only `a b : Usize`, `a.val < 113` and `b.val < 113` as arguments; it has no accuracy premise. The exact fully explicit type is authenticated in `final-run-20261118/attempt-3/receipts/theorem-statement.log`.

## Exact accepted domain and success guarantee

`EngineCorrect` says that for every `W` with `engine.load_check W = ok true` and every `a b : Usize` with `a.val < 113` and `b.val < 113`, there is one `r` such that `engine.predict W a b = ok (some r)` and `TransformerInt.predict (toModel W) a.val b.val = some r.val`. It proves successful return, not just correctness if the call returns. The same answer appears on both sides. It does not prove task accuracy for every accepted `W`.

The following coordinate bounds are **inclusive**. Shapes come from the in-memory `Weights` type, not a binary-file parser. The nine matrix/tensor fields store signed `i8`; biases and tables store signed `i64`.

| Field | Exact shape | Accepted coordinate interval |
| --- | --- | --- |
| `tok` | 114 × 128 | [-68, 68] |
| `pos` | 3 × 128 | [-59, 59] |
| `wq` | 4 × 128 × 32 | [-5, 5] |
| `wk` | 4 × 128 × 32 | [-22, 22] |
| `wv` | 4 × 128 × 32 | [-106, 106] |
| `wo` | 4 × 32 × 128 | [-93, 93] |
| `win` | 128 × 512 | [-82, 82] |
| `wout` | 512 × 128 | [-74, 74] |
| `u` | 128 × 113 | [-37, 37] |
| `bin` | 512 | [-2^30, 2^30] |
| `bout` | 128 | [-2^37, 2^37] |
| `exp_n` | 32 | [0, 2^30] |
| `exp_2`, `exp_1`, `exp_0` | 256 each | [0, 2^30] |

The load check is the translated executable function, not a caller-supplied predicate. `LoadStage` proves soundness and `load_complete` proves termination and acceptance from `LoadBounds`. The trained certificates establish every stored-coordinate bound before applying completeness. This accepts an entire box, including zero matrices and zero tables. It checks no exponential approximation, monotonicity, special table entry, task accuracy, training provenance, checkpoint identity or relationships between matrices. At a maximum score, `expFix` uses its special `d ≤ 0` branch, so even zero tables give a positive softmax denominator. These are sufficient bounds, not the largest safe domain. Training alone does not imply them. The pinned quantised instance passes; some other checkpoints do not. The original float64 checkpoint is not itself a `Weights` value.

`toModel` copies every stored coordinate through nested list maps and signed `.val`, preserving signs, dimensions and index order for all matrices, biases and tables. It does not transpose, pad, drop, rescale or clip. It erases the proof-carrying array and scalar types, not their decoded values or list lengths. In contrast, `ofModel` fixes dimensions, defaults missing coordinates to zero, ignores extras and may wrap through `encode8`/`encode64`. No inverse for arbitrary malformed model lists is claimed; the trained decoding proofs establish the exact equality needed here.

### Architecture, scales and every rounding convention

This is a specified fixed-point transformer variant, not a generic transformer forward API. It has one layer, four attention heads of width 32, residual width 128, a biased ReLU MLP of hidden width 512, and 113 output logits. It embeds exactly three tokens `[a,b,=]` and predicts only the final position. It has no layer norm, dropout, KV cache, sampling, training or multi-layer semantics. Its readable unbounded-integer list algebra is separate from the translated mutable machine loops. Equality therefore establishes a substantive implementation refinement, not a definition of the model as the program.

The numerical rules in `pilot/transformer-int/TransformerInt/Model.lean` are:

- Embeddings have scale 2^8. Q/K/V projections have scale 2^16 and attention scores scale 2^32. The bridge folds `1/sqrt(32)` into quantised WQ; the forward function does not compute it.
- `expFix(d)` returns `EXP_ONE = 2^30` when `d ≤ 0`. Otherwise `u = d >> 8` drops low score bits and `n = u >> 24` selects the integer part. If `n ≥ 32`, the result is clipped to zero.
- Fractional indices are `(u >> 16) % 256`, `(u >> 8) % 256` and `u % 256`. The integer index and these byte indices use `Int.toNat`; they are nonnegative on this branch. The three successive table products are each shifted right by 30. The tables are parameters, not the mathematical exponential function.
- Softmax subtracts the maximum score and divides each of three `e * ALPHA_ONE` numerators by their sum using `Int.tdiv`, which truncates toward zero. `ALPHA_ONE = 2^24`; accepted values make the quotients nonnegative. Their sum need not equal 2^24.
- Value mixing shifts the weighted sum right by 16, giving scale 2^24. Output projections and the sum of four heads have scale 2^32. The attention residual is `x2 * 2^24 + attention`, with no rounding at that addition.
- The MLP preactivation is `lincomb(r, win) + bin * 256`. ReLU maps nonpositive values to zero and shifts positive values right by 8, giving hidden scale 2^32. MLP output adds `bout` without a shift, at scale 2^40.
- The final residual is `(r * 256 + mlpOutput) >> 16`, at scale 2^24. Unembedding gives logits at scale 2^32 without a further shift. Signed right shifts round toward minus infinity, including negative mixed values and final residuals.
- Strict `>` argmax selects the first maximum. An empty model list defaults to answer 0, but the actual engine has 113 logits. Outside `a,b < 113`, mathematical `predict` and `logits` return `none`.
- Missing mathematical list indices use defaults. Vector combinations stop at the shorter list; `lincomb` and `dot` stop at an exhausted argument. These totalisation conventions do not truncate the well-shaped runtime arrays in this theorem.

There is no general machine-range saturation. The forward clips are the exponential cutoff and ReLU, not saturating `i64` operations. Checkpoint quantisation is a separate rounding step before the model. No error bound against float64, exact real softmax or the original trained network is proved.

### Rust caller protocol and target

The Rust comments saying “Never panics” need qualification: the proved valid-input guarantee requires weights accepted by `load_check` and inputs below 113. `predict` and `logits` do not call `load_check` themselves. All weight fields are public. A client must check the same unmodified value before evaluation; no checked-loader capability type enforces that protocol. Unchecked `bin = i64::MAX` can overflow at `bin * 256` under the enabled overflow checks. This is the review's static counterexample, not a test run here. Invalid inputs return before forward evaluation even for rejected weights, but `EngineCorrect` itself only quantifies over valid inputs. **Open for the next retranslation:** qualify both Rust doc comments without changing Rust or translated source in this package.

The translated operations retain checked scalar arithmetic, signed shifts, sign-extending i8-to-i64 casts, bitvector casts to usize, array indexing/update checks and modeled failures. There are no wrapping, saturating or floating-point operations in the reviewed forward path. Equality to `ok` excludes modeled arithmetic, indexing and divergence failures. References, borrows, moves, concrete copies, addresses, stack layout and allocation/resource behaviour are abstracted as pure values/functions. `no_std` and `forbid(unsafe_code)` do not prove stack capacity, machine fault freedom or compiler correctness. A modeled error is not an execution of real unwind/abort behaviour.

Aeneas `Usize`/`Isize` use `System.Platform.numBits`. The dedicated runner is restricted to x86_64 Linux, hence the intended checked platform is 64-bit. This is not a theorem quantified over arbitrary Rust target widths, Wasm32 or cross-target execution.

## What is proved and what is trusted

The retained local receipts report compiler acceptance of all required new modules and ordinary `leanchecker` replay of the final conditional theorem. Its transitive axioms, and those of the load, view and non-emptiness theorems, are exactly `propext`, `Classical.choice`, and `Quot.sound`. See `pilot/engine/trained3-final.log` and `trained3-final-replay.json`. No new axiom or native proof tactic is used in that checked project closure. These are historical results, not checks rerun for this documentation repair.

The trust inventory has separate levels:

| Level | Trusted component or adequacy obligation |
| --- | --- |
| Statement and model | The intended theorem, exact load box, valid domain, fixed architecture, integer scales, table semantics, tie-breaking and list totalisation must describe the intended problem. A correct proof can still prove the wrong specification. |
| Logical checking | Lean kernel implementation and its execution, with `propext`, `Classical.choice`, `Quot.sound`. Mathlib/Aeneas lemmas, tactics, generated row proofs, packing helpers and AI proof authors are not extra logical oracles once their complete closure is checked under this policy. Their definitions still need semantic review. |
| Rust semantics | Pinned Aeneas scalar, array, failure and divergence definitions must adequately model Rust, including checked arithmetic and the host-width choice. Their proved library lemmas are checked dependencies, not extra axioms. |
| Source association | Rust source → rustc MIR → Charon LLBC → Aeneas Lean fidelity; exact flags, versions, source/output association and extraction tooling remain outside the Lean proof. Matching a fresh output proves byte reproducibility, not extractor correctness. |
| Checkpoint interpretation | Checkpoint identity and intended training provenance; NPZ/NPY parsing, little-endian float64, C-order and shape interpretation; float64 operations, sqrt, half-up quantisation and exponential-table generation. Lean proves equality of emitted constants, not correctness of this external interpretation. |
| Provenance machinery | Python interpreter/stdlib, generators, byte-comparison code and frozen gate manifest select and label artifacts. They are trusted for provenance, not as logical oracles for arithmetic results whose certificates Lean checks. |
| Artifact binding | Exact checkout, dependency/configuration selection, filesystem/search paths, source/object correspondence, receipts, SHA-256 assumptions and honest evidence collection. Receipts are not tamper-proof remote attestation. |
| Replay and independent checking | `leanchecker`, Lean object loading, `leanexport`, export-format interpretation, nanoda with its enabled Nat/String extensions, axiom allowlist/configuration and the exact checker/exporter binaries. Nanoda reduces dependence on Lean's checker, not source/model trust. |
| Concrete checker execution | OS, loader, native runtime, CPU/hardware and storage executing the proof tools. These can fail independently of the formal statements. |
| Actual executable, not established here | Rust codegen/optimizer, compiler profile/target/ABI, linker, libraries/host or Wasm engine, stack/resource sufficiency, runtime ingestion and unchanged-weight protocol. No verified loader/compiler/binary connection is supplied. |

The checkpoint generator checks SHA-256 `7cea95ed6771691dfe8a29bedfdae72d9a62c8947c25b1bca2c56919c0ff0f9e` and reads eleven named little-endian float64 C-order arrays with exact shapes. Matrix quantisation uses scale 256 and `floor(v + 0.5)`; WQ is divided by `sqrt(32)` before rounding, `bin` uses 256^4 and `bout` uses 256^5. Matrix values outside i8 are rejected. These are computational float64 rules, not formally proved real-number rounding. The tables use rational exponential brackets and half-up rounding to scale 2^30; their approximation property is not in `EngineCorrect`.

Before emitting runtime references, the generator regenerates and byte-compares the gate weight modules and `Weights.lean`. Lean then checks decoding equality to those exact constants. This generator alone does not check the entire all-row theorem manifest, and a manually chosen `--gate-weights` directory need not be the later import root. The dedicated runner uses one isolated root and checks the complete frozen gate manifest to close that operational ambiguity. A user who skips regeneration can still prove a theorem about the constants actually imported, not about an NPZ hash encoded in the proposition. Hash and parse reopen the file separately, so hostile concurrent input replacement needs immutable/frozen bytes or a single-read parser. The dedicated runner copies its supplied checkpoint once; that does not formally verify the parser. Hashes identify bytes, not scientific interpretation. The checkpoint is external to this repository.

### Historical extraction versus fresh reproduction

`evidence/translate/engine/summary.txt` records Charon `a58d159210b3a36fedeaba4437bda896a8b12f0d`, Rust `nightly-2026-09-17`, and Aeneas `nightly-2026.11.04-d1e177b` at commit `d1e177bb9fdc17fa62e730d524ac905ba19776ed`. It associates Rust source SHA-256 `0cd80fc51e0dbc5c428d00820bcd14143439d8f1ddd5d9b88fee77d94b8988ed` with translated Lean SHA-256 `4c5c4e64a3817a59c739fbc628064f8b2c0c7711b6ef2ccff44d7d9bd6b5788d`. The historical commands use Charon `cargo --preset=aeneas --dest-file <llbc> --abort-on-error --error-on-warnings -- --lib` in `rust/engine`, then Aeneas `-backend lean -abort-on-error -warnings-as-errors -dest <output> <llbc>`, with no exclude flag. See `toolchain/PINS.md` for Lean, library and checker pins.

The package 3 runner only compiled the committed translation; it did not rerun Rust extraction. Package 4 stages a stronger run-mode gate: install pinned Rust, build pinned Charon from source and download the checksum-pinned Aeneas release binary, extract from `rust/engine` using the historical flags into isolated output, then require exact byte equality with committed `lean/LcnExec/Translated/Engine.lean`. Package 6 executed that bootstrap and fresh extraction successfully; its authenticated receipt is `pilot/engine/final-run-20261118/attempt-3/receipts/extraction.json`. The gate checks source/output reproducibility, not translation fidelity. It adds no Cargo test, compiled-Rust, runtime checkpoint-file loader, browser or Wasm guarantee.

## Stage table

| Stage | Statement or artifact | Evidence and status |
| --- | --- | --- |
| Universal engine | `engine_correct : EngineCorrect` | Previously accepted, `pilot/engine/package2-ACCEPTED.json`; unchanged source |
| Generic load acceptance | `load_complete w : LoadBounds w → engine.load_check w = ok true` | Compiled, `trained3-loadcomplete-7.json` |
| Runtime trained arrays | `TrainedData.trainedRust` and per-row bounds/decoding | Compiled, `trained3-LOCAL-VERIFIED.json` |
| Exact trained model view | `trained_view` | Compiled and final-module replay passed |
| Actual load acceptance | `trained_load_ok` | Compiled and final-module replay passed |
| Accepted-weight existence | `accepted_weights_nonempty` | Compiled and final-module replay passed |
| Conditional end to end | `trained_engine_adds_of` | Compiled, standard axiom audit, ordinary replay passed |
| Trained accuracy | `TransformerInt.Gen.adds_mod_113` | Fresh dedicated build passed, `final-run-20261118/attempt-3/receipts/build-gate4.json` |
| Unconditional end to end | `trained_engine_adds` | Dedicated build and exact type/axiom verification passed, `final-run-20261118/attempt-3/VERDICT.json` |
| Fresh final closure and independent kernel | `leanchecker --fresh`, nanoda, planted axiom rejection | All passed in the same run, `final-run-20261118/attempt-3/VERDICT.json` |

The historical local receipt inventories 12 required new modules and a 36-module local project source/object closure. The historical gate 4 generator determinism check matched all 139 frozen source hashes. Its actual all-row import closure contains 135 modules, not the 136 stated in the brief. These counts are in `trained3-LOCAL-VERIFIED.json` and `box3-dry-final/dry-run.json`; they are not new package 4 checks.

## Measured costs

All times in the table below are historical observed command wall times, not predictions or new runs for this repair. The host checks used the shared lock, two Lean threads, the prescribed memory and CPU caps, and individual module targets. The wrapper's `getrusage(RUSAGE_CHILDREN)` RSS method is recorded in every receipt. Wall time can include lock waiting and Lake startup; it is not isolated elaboration time.

| Successful module check | Wall seconds | Peak RSS KiB | Receipt under `pilot/engine/` |
| --- | ---: | ---: | --- |
| Generic load completeness | 24.64 | 2795464 | `trained3-loadcomplete-7.json` |
| Embeddings, real-size pilot | 91.92 | 2769932 | `trained3-pilot-emb-5.json` |
| Query weights | 334.67 | 2966924 | `trained3-wq.json` |
| Key weights | 349.98 | 2963728 | `trained3-wk.json` |
| Value weights | 358.90 | 2972852 | `trained3-wv.json` |
| Attention output weights | 65.54 | 2766688 | `trained3-wo.json` |
| MLP input weights | 222.04 | 2818120 | `trained3-win.json` |
| MLP output weights, explicit list assembly | 264.34 | 3016936 | `trained3-wout-structural.json` |
| Unembedding | 112.54 | 2781708 | `trained3-u-2.json` |
| Biases and softmax tables | 14.10 | 2751528 | `trained3-vectors-2.json` |
| Weight assembly and view | 9.83 | 2742840 | `trained3-weights.json` |
| Conditional theorem assembly | 9.43 | 2767756 | `trained3-final.json` |
| Ordinary final-module replay | 337.25 | 5703888 | `trained3-final-replay.json` |

A tactic-heavy output-table assembly was deliberately stopped after 662.87 seconds, exit 143, without memory exhaustion. Its authentic failed receipt is `trained3-wout-retry.json`. Replacing the large case split and simplifier search with explicit `List.forall_mem_cons.mpr` and `congrArg₂ List.cons` terms passed. Earlier elaboration failures and an interrupted foreground attempt are retained, not counted as successful evidence. The local inventory records 34 attempts with receipts: 24 successful and 10 failed. Two additional interrupted logs lack process receipts; see `trained3-NOTES.md`.

Historical gate 4 costs are 2638 seconds for the build and 2254 wall seconds for replay, from `evidence/gate4/timings.txt` and `replay-summary.txt`. The historical `trained3-estimate.json` combines those figures with successful package 3 command costs, giving 19021.31 seconds. Package 4 adds an explicitly unmeasured 1800-second extraction/bootstrap allowance: 19021.31 + 1800 = 20821.31 seconds, about 5.78 hours. This is a planning estimate, not a new timing. The plan recommends 4 cores, 16 GiB machine RAM and 40 GiB free disk, with a 12 GiB worker cap and two Lean jobs. The worker deadline remains 21600 seconds. At the time of that plan, full fresh-closure replay, export, nanoda, clean bootstrap and fresh extraction had not been measured end to end. The historical estimate was not a completion guarantee. Package 6 actual run timings are retained under `pilot/engine/final-run-20261118/attempt-3/receipts/`.

At the explicitly illustrative assumption of USD 1 per machine-hour, the revised estimate is USD 5.78 and the worker deadline represents USD 6.00 of runtime. This is not a vendor quote or a total billing cap. Obtain a live price and authorization before renting. No rental, paid API, installation or external spend was made for this repair.

## The fault control

The generator test changes actual checkpoint bytes and requires rejection at the hash pin. Both generator tests passed historically in `trained3-generator-tests-final.log`. This is an input-provenance control, not a Lean semantic rejection test or a new test run for this repair.

The dedicated script stages a separate Lean module with an unpermitted axiom proving `False`. It must compile under Lean, export successfully, then fail nanoda specifically for `BoxTrainedFault.bad`. This tests the independent checker's hard axiom allowlist. It does not test weight sensitivity, arithmetic-error sensitivity, extraction or Rust execution. Package 6 ran this control against the real independent checker: Lean compilation and export passed, then nanoda exited 1 specifically for `BoxTrainedFault.bad`. See `final-run-20261118/attempt-3/receipts/fault-nanoda.log`. The harness's 14 lightweight tests passed historically, including bad audit records, object mutation, run guards and the nanoda configuration. See `box3-light-tests-final-pass.log`; this is not a new package 4 test result.

The prior real Rust mutation control is retained in `pilot/engine/fault2/attempt-02/RESULT.json`. It addresses the dot proof only, not a whole final-binary or checkpoint-sensitivity test. That is prior evidence, not a rerun on the package's final closure.

## Package 4 lightweight verification

The final runner regression suite passed 23 tests in `pilot/engine/package4-tests-final.log`. The two existing real-checkpoint generator tests passed in `pilot/engine/package4-generator-tests.log`, including rejection of changed checkpoint bytes. The extraction regressions use explicitly synthetic executable fixtures: identical bytes pass; a newline-only byte change, subprocess failures and missing output fail. They do not run Charon or Aeneas. Acceptance regressions exercise plan, dry-run, worker guards and incomplete final gates, including an inherited worker environment marker.

The real dry run passed in `pilot/engine/package4-dry-final/dry-run.json`, matching 139 frozen sources and a 135-module gate import closure. It reports `accepted: false`, `proof_checks_run: false` and `network_used: false`. There is no acceptance file. All these checks ran in the foreground under the shared flock and prescribed systemd memory/CPU limits. No Lean build, installation, extraction replay or run mode was executed. Earlier successful pre-hardening light tests and dry-run receipts are retained separately under the package 4 filenames without `-final`.

## How to re-check

Supply the pinned checkpoint explicitly. From the repository root:

```sh
python3 -B scripts/gen_engine_trained.py /path/best.npz
python3 -B scripts/gen_engine_trained.py /path/best.npz --check
TRAINED_CHECKPOINT=/path/best.npz python3 -B scripts/test_engine_trained.py
python3 -B scripts/box_trained_test.py
scripts/box_trained.sh dry-run --checkpoint /path/best.npz --out /path/new-dry-run
scripts/box_trained.sh plan
```

On this shared host, never run a full `lake build` or build `TrainedFinal`. Build the gate 4 weight data modules individually, then the generated runtime modules individually, using the mandated lock/resource wrapper `scripts/check_engine_module.py`. Finish with the `LcnExec.Engine.Trained` module target. `python3 -B scripts/audit_engine_trained.py` authenticates retained local receipts and current local source/object hashes without launching a checker.

For an already authorized, dedicated Debian machine, the run-mode entry point is:

```sh
sudo scripts/box_trained.sh run --dedicated-debian \
  --repo <private-repository-url-or-accessible-local-repository> \
  --commit <full-commit-sha> --checkpoint /path/best.npz --out /srv/new-trained-run
```

The staged package 4 run path installs the pinned toolchain, including pinned Rust, source-built Charon and the checksum-pinned Aeneas release binary, and requires fresh isolated Rust extraction to match the committed translation byte for byte. It verifies independent binaries against gate 0(b), checks the selected full repository commit and Aeneas pin, generates gate 4 sources and checks their complete manifest, verifies runtime-source regeneration, and builds gate 4 and the engine closure in an isolated project. It prints and audits final axioms, records the theorem type, hashes proof objects, performs fresh replay, exports to nanoda, and requires the planted fault rejection. Nanoda enables the standard axiom allowlist with `unpermitted_axiom_hard_error: true`. The required `accepted.json` is run-only: neither plan nor dry-run may produce it. Package 6 executed this acceptance path successfully at the producer revision named above. The script does not provision a machine or authorize spending. Private repository access must already work on that machine.

A zero exit alone is not final acceptance: plan and dry-run may both exit 0 without proving anything. Acceptance requires an authentic `accepted.json` from `run --dedicated-debian`, independently adjudicated against the intended exact revision, source/object/export bytes and real checker/control logs. The runner prints the theorem type. Package 6 additionally compared its complete fully explicit output byte for byte with the retained expected type, and authenticated the exact committed `TrainedFinal.lean` source. The accepted run closes the accuracy premise for the pinned constants and checks the final exported closure; it does not verify extraction fidelity, the parser or a compiled executable.

## Scope and limits

The retained package 3 proofs establish trained load acceptance, exact decoding, non-emptiness and conditional correctness. Package 4 changed only documents, the build harness and lightweight tests/evidence. Package 6 now adds a freshly rebuilt unconditional result and independent final-checker acceptance, but no proof about a compiled executable. The branch is private. No public release was made. The model, contract, view, Rust engine and translated engine were left unchanged. The package 3 Lake library configuration discovers generated weight modules; package 4 does not change that configuration or the mathematical model.

The architecture and bounded input domain are deliberately small. The proof is not evidence that the approach scales to general language models or floating-point inference. Accuracy for a frozen trained checkpoint is distinct from generic functional correctness for every accepted weight value.

## Relation to prior work

The supplied review, `docs/ENGINE-PRIOR-ART.md`, is a source-reading review, not an independent artifact reproduction. SONNX is a serious unresolved comparison: its reported Why3 tensor refinement, flat-array implementations and C extraction are related work, not grounds for a priority claim. The complete SONNX proof chain still needs inspection. See [SONNX graph work](https://ceur-ws.org/Vol-4324/paper4.pdf) and [tensor paper](https://link.springer.com/chapter/10.1007/978-3-032-32357-6_2). The external project descriptions below retain that review's source-reading or abstract-only grades; they are not independent proof audits.

[TorchLean](https://github.com/lean-dojo/TorchLean) already provides generic Lean neural semantics and execution theorems, with documented foreign runtime boundaries. [lean4-mlir](https://github.com/brettkoonce/lean4-mlir) connects rich neural mathematics to generated graphs while retaining numerical and printing assumptions. The [Rust-to-Lean pipeline](https://arxiv.org/html/2605.30106) is direct methodological precedent for extraction followed by specification proofs. [QNNVerifier](https://arxiv.org/html/2111.13110v1) is genuine finite-word-length implementation-verification prior art. [FlashProve](https://www.anthropic.com/research/provable-inference) certifies execution claims cryptographically, a different claim from static implementation refinement. Do not frame that distinction as an inability of cryptographic relations to quantify over weights.

The contribution here is the concrete connection between a runtime-weight safe-Rust transformer translation, its mathematical integer specification, and an accepted trained instance. Existing generic semantics, verified operators and extraction pipelines must be credited. No priority claim is made.

## Open items

- Qualify the Rust “Never panics” comments at the next retranslation. Do not change source or extraction bytes in this package.
- Dedicated run complete: fresh extraction/byte comparison, unconditional build, fresh closure replay, nanoda and planted-axiom rejection passed in package 6.
- Citadel artifact verification complete: final theorem type, source/object/export hashes and real checker/control receipts passed. See `final-run-20261118/attempt-3/VERDICT.json`.
- Review the checkpoint parser and quantisation bridge separately from proof-kernel checking, including frozen-input or single-read hardening against concurrent replacement.
- Inspect the complete SONNX artifacts and pin historical versions of related projects before public positioning.
- A compiled-binary, browser or Wasm guarantee requires a separate verified execution/compiler connection.
- Other accepted weights need their own task-accuracy proof. No training, generalisation, all-target portability, physical resource safety, throughput, timing, side-channel security or LLM scaling theorem is supplied.
- A whole-final-chain Rust mutation or trained-weight sensitivity test is separate from the historical dot mutation and the staged axiom-allowlist control.
