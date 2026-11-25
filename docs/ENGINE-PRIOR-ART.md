# Prior art and claim review: Lean-proved Rust inference

Review cutoff requested: 2026-11-18. The original literature review used web research only, with no builds, paid services or public actions. The current-status and boundary sections were corrected from the local engine statement review for package 4. The package 4 documentation repair did not reproduce external artifacts, run extraction or build proofs. Package 6 subsequently ran and authenticated the dedicated trained theorem build; it did not reproduce any external prior-art artifact.

## Evidence legend

- **[R] Read in source:** the identified passage was read in a paper body, project documentation, or announcement. This is evidence of what the authors say, not an independent reproduction or proof audit.
- **[A] Abstract-only:** only the abstract supports the technical characterization.
- **[U] Unverified:** search-snippet lead, missing artifact, supplied private-project assertion, or a conclusion/recommendation not established by an inspected proof. Recommendations and conditional future claims are explicitly marked.

Markers apply to the paragraph or table row they introduce. Sources were retrieved during this review. Live GitHub `main` documentation is not a pinned historical release. Paper dates and the dated Harmonic announcement support chronology, but this is not a complete reconstruction of every repository as it existed at the cutoff.

## Verdict

**[U, search conclusion] No exact qualifying public result was confirmed in this review. That does not justify a priority claim.** The proposed distinction is a theorem about an actual Rust/C/C++ inference implementation, universally quantified over admissible weights and inputs, proving successful return and equality to a separately readable mathematical forward specification. A proof about a Lean network, a C operator, model robustness, or one inference transcript is not automatically that theorem.

**[R/A] SONNX is a serious unresolved comparison.** Its tensor-paper abstract describes a Why3 refinement workflow from mathematical tensors through flat-array implementations to extracted C, and contract-based functional verification of complete networks. The accessible companion graph paper lists executable C extraction and strengthening the refinement chain as future work. These are attributed source/abstract reports, not an independent proof audit or an exhaustive ranking of competitors. Neither dismiss SONNX nor assert that it already proves the exact requested whole-engine claim.[18][26]

**[U, scope] The broad question remains open at artifact-audit level.** The honest result is “no exact match confirmed,” not “nobody has done this.” In particular, the paywalled SONNX tensor paper and its complete implementation/proof chain deserve inspection before any “first” wording.

## Nearest three results

These are the nearest substantive neural-inference/specification efforts found. The Rust-to-Lean pipeline below is the nearest methodological precursor, but its targets are cryptographic rather than neural.

| Result | What exactly is proved and about which artifact | Prover and trusted base | Relation to our target |
|---|---|---|---|
| **SONNX: Verified Tensor Operators for Safety-Critical ML; companion graph work** | **[A]** Machine-checked refinement from abstract tensor specifications to concrete flat-array implementations, followed by C extraction; abstract specifications compose for contract-based functional properties of complete networks. **[R]** The ERTS companion shows `ctensor_conv2d(x,w,b,...)` with shape/validity conditions and a postcondition equating its abstract output with mathematical convolution. Weights are arguments, not a single frozen checkpoint.[19][26] | **[R]** Why3 generates verification conditions discharged through automated theorem provers/SMT solvers. The ERTS paper explicitly says the Why3 C generator is not a qualified tool and manual activities remain to establish compliance. Thus code generation, drivers, C compiler/runtime, and numerical interpretation remain boundaries unless separately discharged. Exact solver versions and proof-certificate checking were not audited.[18][19] | **[R/U]** Serious prior art against broad “first verified inference in C” language. The graph paper says C runtime extraction remains future work; this review did not find a completed whole-C-engine equality theorem. This is a missing confirmation, not proof of nonexistence.[18] |
| **TorchLean** | **[R]** Lean graph semantics, graph shape soundness (`Graph.run_ports`), forward/backward tape correspondence and derivative theorems. Runtime-approximation results include transformer-block error bounds under arithmetic contracts and stage/weight bounds. The trust document explicitly distinguishes exact tape/spec models from compiled code and CUDA.[1][2] | **[R]** Lean checks mathematical claims; documented logical-dependency checks allow the standard core axioms. Native CPU tensor kernels, LibTorch, CUDA, generated kernels and executable replacements have explicit external boundaries. A backend marked “checked” is not thereby a Lean proof of its foreign implementation.[2] | **[R/U]** Generic network mathematics and execution already exist. Do not claim the first neural network in Lean or the first machine-checked forward semantics. The inspected documents do not supply a theorem relating an entire external Rust/C/C++ forward implementation to that specification for arbitrary weights.[1][2] |
| **lean4-mlir, README version v0.8.0** | **[R]** Layer and whole-network VJPs over exact reals, plus denotational ties from emitted train-step update nodes to certified steps. It covers substantial vision networks and attention, not merely MNIST. The README explicitly retains the real-to-Float32 numerics and text printing as trusted.[3] | **[R]** Lean kernel and standard core axioms; independent comparator checks are reported. Per-op printing, XLA/PJRT, IREE compilation, C FFI/runtime and GPU arithmetic remain trusted. Numerical-closeness theorems have explicit model and magnitude-window hypotheses.[3][4] | **[R/U]** Strong prior art for proof-derived executable graphs. Not an inspected proof of the final systems-language runtime. MNIST robustness theorems concern predictions under perturbations of specified mathematical networks, not correctness of arbitrary loaded weights in C/Rust.[4][25] |

**[R] MNIST detail that matters:** lean4-mlir's results distinguish exact-rational dataset measurements from kernel-proved per-image witness theorems. The document says the scorecard theorem covers the designated witnesses, not every displayed measured count. Do not promote a measured robustness score into a theorem about all images or into a runtime-equivalence claim.[25]

## Required leads and additional checks

### Rust extraction and AI provers

**[R] arXiv:2605.30106, v2 dated 2026-07-02:** the paper describes Charon/Aeneas or Hax extraction, abstract Lean specifications, and kernel-checked proofs. Applications include Plonky3 field arithmetic, FRI folding, Horner evaluation and RISC Zero Merkle inclusion. Its specification stage explicitly states that the extracted Rust function returns a result matching the mathematical target under preconditions. This is direct prior art for our method, but not neural inference. AI proof search is not a new trusted component when the produced proofs are kernel checked; translation fidelity and specification adequacy still matter.[5]

**[R] Harmonic, 2026-11-16 launch:** Aristotle announced Rust support, including claims about undefined behavior, functional correctness and unsafe blocks. Named cases are Manifest and Project 0, not neural-network inference.[8]

- **[R] Manifest:** the case study reports 28 Lean-stated results covering trading progress, error classification, tree/accounting invariants, matching and rounding. Its body reports two corrected findings, while the launch highlights a rounding bug. These are company-reported results; this review did not inspect or replay the Lean artifacts.[8][9]
- **[R] Project 0:** the case study reports 31 results across deposits, withdrawals, borrowing, repayment, liquidation and joint accounting. It explicitly limits the claim to modeled records, not checked against live on-chain accounts, and excludes token transfers, rollback and other system behavior.[10]

**[R] Theorem, Jason Gross and Rajashree Agrawal:** the verified-stack post advocates binary-level proofs, avoiding compiler correctness as an assumed bridge. The Anthropic collaboration reports RISC-V security properties across production libraries. Neither inspected source claims an arbitrary-weight neural inference engine equivalence theorem. That is a scope distinction, not evidence that Theorem has no unpublished result.[11][23]

**[A] Gross and Agrawal's related Max-of-K work** proves model-performance accuracy bounds using mechanistic understanding. It should be credited as neural-network theorem work, but its abstract does not claim a Rust/C/C++ implementation refinement theorem.[24]

### BlockCert, integer inference, and zkML

**[R] BlockCert:** a Python extraction/replay pipeline with hashed artifacts, measured coverage and approximation errors. Its Lean theorem composes local error and Lipschitz hypotheses into a global error bound. The paper explicitly says finite-trace certificates are empirical local soundness rather than universal bounds. It is neither an exact universal-weight engine theorem nor a proof of the Python implementation.[6]

**[R] int-llm:** pure-integer C inference with a real TinyLlama checkpoint, deterministic output checks, a golden-hash gate and token agreement on the stated benchmark prompts. The read README documents empirical reproducibility, not a machine-checked universal equivalence theorem. “Verified” here must not silently be read as Lean/Coq implementation verification.[7]

**[R] FlashProve is substantial and proves a different statement:** a model provider commits to weights, then produces cryptographic evidence for particular prompt/output tokens. Soundness says an accepted false claim is infeasible under the stated cryptographic model, with negligible error, rather than asserting that a particular C++ inference implementation is correct for all inputs. Lean formalizes protocol security and a slow executable verifier. The announcement explicitly says its fast C++ verifier carries no formal guarantee and that agreement is tested, not proved. The integer greedy-decoding relation is not arbitrary floating-point or sampled decoding.[12]

**[U, interpretation]** zkML relations can themselves be parameterized by arbitrary weights. Therefore “ours handles arbitrary weights, zkML does not” would be false framing. The distinction is static implementation refinement versus checking individual execution claims through a cryptographic relation. These approaches can complement each other.

### Coq, Isabelle, CakeML, C verification and runtimes

**[R] QNNVerifier:** verifies finite-word-length neural implementations using SMT-based software model checking and user-specified safety properties. The source describes C implementations, Frama-C interval inference and ESBMC. That is genuine implementation-level prior art. The inspected text does not establish the narrower generic implementation-to-mathematics equality theorem requested here.[13]

**[A] Formally Verified Neural Network Converter for Coq:** verifies the conversion into a theorem-prover representation, narrowing an important semantic gap. The abstract does not establish correctness of deployed inference C/Rust code. Full paper and proof chain were not read.[14]

**[R, limited passages] Isabelle/HOL feed-forward verification:** formal embedding, TensorFlow import, executable evaluation and classification properties. The accessible text does not establish a C/C++/Rust implementation proof. Extraction to another language is not by itself a proof of that target runtime.[15]

**[U, search-snippet lead] CakeML:** Efficient Certified Reasoning for Binarized Neural Networks describes certificate-checker extensions verified to machine code through CakeML. This is a proof checker for neural reasoning, not confirmed evidence of a neural inference runtime. Only the title/introduction extracted reliably; the machine-code characterization was read in search output and not independently checked.[16]

**[R] Additional close C result: Formal Safety Verification of ONNX Operators**, by Carolina Sá, Miguel Liquito and Gonçalo Caixeiro. The slides report functional correctness for Clip, Where and MatMul and a generalized LeNet chain. Crucially, the chain uses operator stubs without bodies and establishes safety/shape composition under contracts. Arithmetic correctness of convolution and floating-point rounding are explicitly future work. Thus its “full chain” result must not be described as complete end-to-end numerical implementation equivalence. This is a serious lead, not a counterexample established by the slides.[17]

**[U, search coverage]** Queries included the requested phrases “verified neural network inference,” “certified DNN runtime,” “CompCert neural network,” “CakeML neural network,” and “Isabelle neural network verified implementation,” plus C functional correctness, arbitrary weights, Rust/Aeneas and SONNX refinement variants. No end-to-end CompCert neural runtime was confirmed. The existence of a verified compiler alone does not prove any given neural program implements its intended mathematics.

## Honest current claim

The generic engine theorem already exists. The trained load/view witness and conditional corollary are checked. Package 6 has now accepted the unconditional trained final theorem at producer `0c346acb76b568249a41f46c39ff56caf33442ab`, with fresh replay, nanoda and the planted-axiom control. The current sentence allowed by the local statement review is:

> For the pinned quantised trained constants, Lean proves that this fixed-size integer-transformer engine's Charon/Aeneas-translated computation returns `(a + b) % 113` for every input pair below 113, without an accuracy hypothesis, with fresh Lean replay and nanoda checking of the final theorem's exported dependency closure, while checkpoint interpretation, extraction and compiled Rust or Wasm execution remain outside the proof.

This replaces the stale claim that the transformer Rust forward equivalence was not yet proved. Recurrent-adder claims are outside this engine review and are not carried into its status sentence. The new unconditional proof and independent final-checker acceptance are documented in `pilot/engine/final-run-20261118/attempt-3/VERDICT.json`. Nanoda reported 31,942 declarations with no typechecker errors and one axiom pretty-printer error.

**[U, usage conditions]** No priority claim follows. If publishing before release, say private artifact, not published implementation. The cutoff is not permission to backdate a later achievement. Do not call the small engine a general LLM engine, browser-certified binary, verified floating-point transformer or proof of task accuracy for arbitrary weights. An unconditional claim requires authentic `run --dedicated-debian` output with `accepted.json` and independent inspection of the intended exact theorem type, selected revision, source/object/export hashes and real replay/nanoda/control logs. Plan or dry-run returning 0 proves nothing. The runner prints the type; package 6 compared the complete fully explicit output byte for byte with the retained expected type and authenticated its committed `TrainedFinal.lean` source.

### Exact engine scope behind that sentence

The load box below gives **inclusive** coordinate intervals. Shapes are fixed by the in-memory Rust/translated `Weights` type, not validated by a checkpoint-file parser.

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

This accepts a coordinate box, including zero matrices and tables, not “arbitrary trained weights.” Training alone does not imply these sufficient bounds; some other checkpoints fail them. The checker establishes no checkpoint identity, provenance, task accuracy, inter-matrix relationship, exponential approximation, monotonicity or particular table entry. The pinned quantised instance is proved accepted. The original float64 checkpoint first needs quantisation. `toModel` preserves all stored coordinates, signs, shapes and order; it does not clip, rescale, transpose or drop data. The reverse `ofModel` is not a generic inverse: malformed lists can default, truncate or wrap on scalar encoding.

The specification is a fixed-point variant with one layer, four width-32 attention heads, residual width 128, biased width-512 ReLU MLP and 113 logits. It embeds exactly `[a,b,=]` and predicts only the last position, with no layer norm, dropout, KV cache, sampling, training or multi-layer API. The forward model's numerical conventions are:

- Embedding scale 2^8, Q/K/V scale 2^16, score scale 2^32. Attention's `1/sqrt(32)` is folded into quantised WQ by the bridge, not evaluated in the forward function.
- `expFix(d ≤ 0) = 2^30`. For positive `d`, `u = d >> 8` and the integer index is `n = u >> 24`. Index ≥ 32 clips the result to zero. Fractional indices are `(u >> 16) % 256`, `(u >> 8) % 256`, and `u % 256`. `Int.toNat` is only used on nonnegative indices on that branch. Each of three table products is shifted right by 30.
- Softmax subtracts the maximum and uses three `Int.tdiv` quotients of `e * 2^24` by the positive denominator. Quotients truncate toward zero and need not sum to 2^24. The maximum's special exponential branch ensures a positive denominator even for zero tables.
- Value mixing shifts right by 16, to scale 2^24; head output projections and the four-head sum have scale 2^32. The attention residual is `x2 * 2^24 + attention` without rounding there.
- MLP preactivation adds `bin * 256`. ReLU clips nonpositive values to zero and shifts positive values right by 8, to scale 2^32. MLP output adds `bout` without a shift, at scale 2^40. Final residual `(r * 256 + mlpOutput) >> 16` has scale 2^24; unembedding gives scale-2^32 logits without another shift. Signed right shifts round toward minus infinity.
- Strict `>` argmax picks the first maximum; an empty mathematical list defaults to 0, but engine logits are nonempty. Invalid inputs give mathematical `none`. Default indexing and shorter-list termination of combinations, `lincomb` and `dot` totalise malformed model lists, not the valid runtime arrays.

There is no general machine-range saturation. The clips are exponential cutoff and ReLU. Quantisation separately uses float64 scale 256, half-up `floor(v + 0.5)`, WQ division by `sqrt(32)`, `bin` scale 256^4 and `bout` scale 256^5, rejecting out-of-i8 matrices. Table generation uses rational brackets and half-up rounding to 2^30. No formal parser, quantisation or table-approximation theorem, real-softmax equivalence or float64 error bound is supplied. See [ENGINE-THEOREM.md](ENGINE-THEOREM.md) for source pointers and the conditional theorem type.

### Trust inventory and reproduction boundary

- **Statement/model adequacy:** exact load box, fixed architecture, integer scales, table semantics, first-winner tie rule, list totalisation and valid domain must be the intended specification.
- **Logical checking:** Lean kernel implementation/execution and `propext`, `Classical.choice`, `Quot.sound`. Checked Mathlib/Aeneas lemmas, tactics, generated row proofs, packing helpers and AI authors are not extra logical oracles. Their definitions and statements still need semantic review.
- **Rust semantic adequacy:** pinned Aeneas scalar/array/failure/divergence definitions, checked arithmetic, signed shifts/casts/indexing and host-width semantics. `Usize` uses `System.Platform.numBits`; the dedicated runner targets x86_64 Linux, not arbitrary target widths or Wasm32.
- **Translation:** Rust source → rustc MIR → Charon LLBC → Aeneas Lean fidelity, exact versions/flags and source/output association. Extraction reproducibility is not a proof of extractor correctness. Pure values abstract references, borrows, moves, copies, addresses, stack layout and allocation/resources; modeled errors do not execute unwind/abort.
- **Checkpoint interpretation:** identity, intended training provenance, NPZ/NPY parsing, little-endian float64 C-order/shape interpretation, float operations, sqrt, quantisation and table generation. Python interpreter/stdlib, generators, byte-comparison code and frozen manifest are provenance machinery, not logical arithmetic oracles. The theorem equates emitted constants; its proposition does not contain an NPZ hash. Separate hash/parse reads need frozen bytes or single-read hardening against hostile concurrent replacement.
- **Artifact binding:** exact checkout/dependencies/configuration, filesystem/search paths, source/object correspondence, SHA-256 assumptions, receipts and honest evidence collection. A receipt is not tamper-proof remote attestation.
- **Independent checking:** `leanchecker`, Lean object loading, `leanexport`, export-format interpretation, nanoda's enabled Nat/String extensions, allowlist/configuration and exact exporter/checker binaries. OS, loader, native runtime, CPU/hardware and storage executing every checker also remain trusted. Nanoda reduces proof-checker dependence, not source/model trust.
- **Compiled execution, not established:** Rust codegen/optimizer, profile/target/ABI, linker, libraries/host or Wasm engine, stack/resource sufficiency, runtime ingestion and unchanged-weight protocol. No verified loader/compiler/binary connection is present. `predict` and `logits` do not call `load_check`; clients must check the same unmodified weights. Qualifying the Rust “Never panics” comments is open for the next retranslation; neither Rust nor translation is edited in this package.

The historical extraction receipt is `evidence/translate/engine/summary.txt`, with pinned versions, commands and source/output hashes. The package 3 dedicated runner only compiled the committed translation. Package 4 stages fresh pinned Rust/Charon bootstrap and the checksum-pinned Aeneas release binary, isolated extraction from `rust/engine` using the historical flags, and exact byte comparison with committed `Engine.lean`. Package 6 subsequently executed this bootstrap and fresh extraction successfully; the fresh translation was byte-identical to committed `Engine.lean`. Plan and dry-run may not produce `accepted.json`. The authenticated package 6 run closes the trained accuracy premise and checks the final exported closure. It does not certify checkpoint parsing, extractor fidelity or compiled Rust/Wasm execution. It would establish no accuracy for other accepted weights, all-target portability, resource/timing/throughput/side-channel guarantee, generalisation or LLM scaling result.

## Three strongest reviewer objections and honest answers

### 1. You proved translated Lean, not the Rust binary

**[R] Basis:** Aeneas translates Rust into a pure functional model; its author describes proof-producing refinement from a deep embedding as a longer-term direction. TorchLean and lean4-mlir likewise expose native-runtime trust boundaries.[2][4][22]

**[U, answer/recommendation]** Agree. The precise claim is correctness of the pinned translated computation, with its source connection dependent on Charon/Aeneas fidelity. Publish exact source hashes, extraction commands and versions, generated Lean, main theorem, transitive axioms and independent-checker log. Require clean-source regeneration and exact byte comparison rather than a hand-edited translation. Package 4 staged that run-mode gate, and package 6 has now executed fresh extraction with byte-identical output. Lean plus nanoda reduces proof-checker risk, not mistranslation or rustc risk. Machine-code verification or a verified compiler connection is separate work, not implied by this theorem.

### 2. “Arbitrary weights” hides restrictive hypotheses and a different numerical model

**[R] Basis:** prior systems explicitly distinguish exact reals, numerical contracts, integer greedy models and deployed floating-point execution.[4][12][19]

**[U, answer/recommendation]** Agree that the domain is only accepted weights and valid inputs. Shapes are enforced by the in-memory type; acceptance supplies sufficient coordinate bounds for successful indexing and arithmetic on the stated input domain. `EngineCorrect` already proves successful return plus exact prediction equality, not merely “if the program succeeds its answer is correct.” The trained load/view and non-emptiness theorems make the domain visibly inhabited. The numerical inventory above specifies shifts, truncating division, clipping and tie-breaking, with no general saturation. Integer correctness does not establish float64 equivalence or useful behaviour for every accepted weight. The historical all-logit Python comparison is evidence, not a float-to-integer equivalence proof.

### 3. This is a small integration result, with existing generic semantics and verified operators

**[A/R] Basis:** SONNX's abstract describes verified refinement infrastructure, and TorchLean documents generic neural semantics.[26][1] lean4-mlir connects rich architectures to emitted graphs; the Rust pipeline already connects production code to mathematics.[3][5]

**[U, answer/recommendation]** Credit all four rather than claim invention of verified inference. The contribution is the generic accepted-weight refinement theorem for this concrete translated Rust forward computation and an accepted trained instance, with extraction and compiled execution outside the proof. The independently checked package 6 final trained closure adds the unconditional addition corollary, not a fully verified source-to-binary chain. Changing weights preserves the generic theorem only after load acceptance; trained task accuracy needs a separate proof. The small architecture supports this bounded feasibility result only. Generality, throughput, browser/Wasm fidelity and language-model scale need separate artifacts and evidence.

## Demonstrations to recommend

### Formal-verification engineers: a clean reproduction plus a weight-swap and mutation test

**[U, proposed, not executed]** Hand over one pinned minimal package containing Rust, its automatically regenerated and byte-compared Lean translation, a short mathematical specification, the accepted-weight theorem, an accepted trained checkpoint and exact independent-checker instructions. A reviewer could swap in a different checkpoint after proving load acceptance, without re-proving the generic engine theorem; this would not preserve addition accuracy automatically. Test a one-line indexing or rounding mutation and report its actual proof outcome, rather than promise that every mutation must fail. The historical changed-index control addresses the dot proof only. The accepted final axiom fault tests the independent allowlist, not Rust mutations, arithmetic sensitivity or learned-weight sensitivity. Lead with the theorem and dependency audit, not an AI-generated proof transcript. Source/extraction fidelity and compiled execution remain separate trust boundaries.

### General Hacker News reader: a browser adder with an honest, visible guarantee

**[U, proposed, not executed]** A separate browser-adder demonstration could compare a network's answer with ordinary addition. The recurrent-adder artifact and its claimed all-length theorem are outside this engine review and would need their own exact statement and receipts before displaying a guarantee. Do not label sampled runs as proofs or claim browser machine-code verification. If mathematical addition correctness is not itself proved, say that separately. Any transformer demo with user-loaded weights must check load acceptance for the same unmodified value and must distinguish engine correctness from task accuracy. Browser compilation and execution remain trusted.

## Limits and next decisive check

**[U]** No foreign code or proofs were built or independently checked. The original literature review took private-project facts from its supplied brief; the corrected generic engine status follows the local statement review and its historical receipt premises. The package 6 trained status additionally follows the fresh authenticated build and checker receipts named above. Abstract-only and snippet-only results remain marked. No exhaustive absence result or world-first claim is established. The original review reported rate-limited or short extractor responses and recovery of key SONNX, BlockCert, FlashProve and runtime-boundary passages through public curl/PDF extraction without paid access. Those retrievals were not repeated for this repair.

**[U, next package]** Inspect the complete SONNX tensor paper and its linked Why3/C artifacts, then audit the exact theorem scope and trusted extraction step against a whole forward-pass specification. Resolve whether it already covers a complete parameterized C network numerically, rather than operators plus an abstract graph. In parallel with any eventual publication review, pin historical source revisions for TorchLean and lean4-mlir at the cutoff. The current-status sentence above now uses the stronger trained wording allowed after the authenticated dedicated run and exact-type/artifact review. Neither that run nor the literature search would establish priority or compiled-binary correctness.

## Sources

[1] https://raw.githubusercontent.com/lean-dojo/TorchLean/main/README.md
[2] https://raw.githubusercontent.com/lean-dojo/TorchLean/main/docs/TRUST_BOUNDARIES.md
[3] https://raw.githubusercontent.com/brettkoonce/lean4-mlir/main/README.md
[4] https://raw.githubusercontent.com/brettkoonce/lean4-mlir/main/TRUST.md
[5] https://arxiv.org/html/2605.30106
[6] https://arxiv.org/html/2511.17645
[7] https://github.com/nmicic/int-llm
[8] https://www.harmonic.fun/news/aristotle-rust-verification
[9] https://www.harmonic.fun/aristotle/case-studies/manifest
[10] https://www.harmonic.fun/aristotle/case-studies/project-0
[11] https://theorem.dev/blog/verified-software-stack
[12] https://www.anthropic.com/research/provable-inference
[13] https://arxiv.org/html/2111.13110v1
[14] https://link.springer.com/chapter/10.1007/978-3-031-98208-8_12
[15] https://logicalhacking.com/publications/brucker.ea-feedforward-nn-verification-2023/brucker.ea-feedforward-nn-verification-2023.pdf
[16] https://arxiv.org/html/2507.02916v1
[17] https://haslab.github.io/MFP/PMFP/2526/M3_slides/61480_61453_60260.pdf
[18] https://ceur-ws.org/Vol-4324/paper4.pdf
[19] https://hal.science/hal-05513194v1/file/ERTS2026_paper_2.pdf
[22] https://www.sonho.fr/assets/documents/aeneas.html
[23] https://www.anthropic.com/research/formal-verification
[24] https://proceedings.neurips.cc/paper_files/paper/2024/hash/90e73f3cf1a6c84c723a2e8b7fb2b2c1-Abstract-Conference.html
[25] https://github.com/brettkoonce/lean4-mlir/blob/main/historical/RESULTS.md
[26] https://link.springer.com/chapter/10.1007/978-3-032-32357-6_2
