# E5 Report: exact reference, trained byte LM, cross-language parity

Contract: `docs/SPEC-E4-E6.md` (GLMW v1, exactly 479,504 bytes). All verdicts
below are tied to SHA-256s in `evidence/e5-bytelm/RECEIPT.json`.

## Verdicts

| Check | Result |
| --- | --- |
| `weights/mod113_v1.bin` size / `load_check` | 479,504 bytes / True |
| mod-113 accuracy, Python engine, all 12,769 pairs | **12,769 / 12,769** (wrong 0) |
| mod-113 logits FNV-1a 64 (Python engine) | `6cb24f7670e8562e`, equals the pinned `rust/transformer` fixture |
| mod-113 accuracy + hash, Rust harness engine | **12,769 / 12,769**, same hash |
| `weights/tiny_bytelm_v1.bin` size / `load_check` | 479,504 bytes / True |
| exact integer engine, val bits/byte (460 windows) | 1.3866 (argmax acc 0.7043) |
| float QAT, same 460 windows | 1.3866 (argmax acc 0.7043) |
| float QAT, all 3,674 val windows | 1.4380 (argmax acc 0.6938) |
| logit correlation, integer / 2^32 vs float QAT | 1.000000 (max abs diff 5.8e-04) |
| numpy int64 batch port vs scalar `ref_engine` | 2,048 logits, 0 mismatches |
| static bounds from weights alone | every stage fits i64, widest 61 bits |
| Rust vs Python, 200 prompts x 256 logits (tiny LM) | **0 mismatches** |
| Rust vs Python, 200 prompts x 113 logits (mod 113) | **0 mismatches** |
| native Rust greedy generation | 5.6 tokens/sec (harness build, see below) |

The mod-113 pair count appears once as a verdict, verified twice by
independent engines (the pure-Python `ref_engine` sweep and the compiled Rust
harness sweep); both reproduce the fixture hash, which is the canonical bit.

## Deliverable 1: exact Python reference + serializer

`python/bytelm/ref_engine.py` (standard library only, sha256 in the receipt):
GLMW v1 `pack`/`unpack`/`load`/`save`, `load_check` over every coordinate,
`forward_logits`, `predict_next`, `generate_greedy`. Conventions are written
into the code: `tdiv` implements Rust `i64` truncating division (Lean
`Int.tdiv`; the program's one division has nonnegative numerator and positive
denominator, so it also equals floor), and every `>>` is Python's floor shift,
which is Rust's arithmetic `i64` shift. The reference computes only the
output-relevant positions of the final layer (positions before `seq_len-1`
have no consumer there); the Rust harness computes every active position
literally, and the 200-prompt parity proves the outputs are identical.

`python/bytelm/make_mod113_weights.py` parses the trained integers from
`rust/transformer/src/weights.rs` (the pinned checkpoint's generated file) and
maps them into the general engine: `n_layers = 1`, `vocab_size = 113`, the
second layer zero, `tok` rows 114..255 and `u` columns 113..255 zero-padded.
`verify_mod113.py` then runs all 12,769 pairs through the exact integer
engine: wrong 0, ties 0, smallest margin 62,944,808,481 at pair (21, 56) —
the same margin `rust/transformer` measures — and the logit hash matches the
pinned fixture, so the general forward on `[a, b, 113]` is bit-for-bit the
original one-layer engine.

## Deliverable 2: the 2-layer byte-level LM

Architecture per the contract: 2 layers, vocab 256, max_seq 32, d_model 128,
4 heads x 32, d_mlp 512 — 464,128 parameters. Corpus
`python/bytelm/corpus.txt`: 156,822 bytes / 2,969 lines of short plain-ASCII
English (capitals, arithmetic in words, proverbs, verification Q&A,
micro-dialogs, joined three-line paragraphs, a minority of templated grammar
sentences). Deterministic split: every 10th line (index % 10 == 7) is
validation.

QAT design (documented in `train_qat.py`'s docstring): dividing every integer
by its scale turns the engine into a standard float transformer, so training
runs in normalized units with STE at every quantization point — each i8
matrix clamped to its exact `load_check` box, `bin` to ±2^30, `bout` to ±2^37,
the inter-layer stream clamped and snapped to the 1/256 grid — and the
exported file carries the exact rational exp tables of
`scripts/gen_transformer_weights.py` verbatim.

Training history, five distinct rounds on a 2-thread CPU box (CPU-only
PyTorch 2.15.0+cpu, each run bounded at ~400 s, resident usage far below
2.5 GiB; total across rounds roughly 25 minutes, the exported checkpoint is
round 5 alone at 386 s):

1. Round 1 (246,806-byte corpus, plain Adam): val 3.0671 bpb. No weight decay;
   layer-0 boxes saturate.
2. Round 2 (rebalanced 242,425-byte corpus, attention at 3x lr): val 3.4040.
   Every layer-0 matrix pinned at its box; the value path amplified attention
   to ~2^42 and the inter-layer clamp collapsed the stream to sign bits;
   greedy samples degenerated to "the the the".
3. Round 3 (quadratic saturation penalty): diverged, killed around step 900
   (bpb 7.8).
4. Round 4 (linear saturation penalty): also diverged, killed around step
   1200.
5. Round 5 (final): gentle layer 0 — 0.25x init scale and 0.15x learning rate,
   so it stays a light mixing layer inside the clamp range — AdamW with
   weight decay 0.02 (embeddings and biases exempt), no penalty. 2,900 steps
   in 386 s, val 1.1080 bpb float QAT.

Round logs are preserved under `evidence/e5-bytelm/training_rounds/`.

Final evaluation (`eval_exact.py`, on the exported checkpoint,
sha256 `c3575e46dce2bc1027955f34d29e87c23540ea28c3ead3e80c329c5cc1abac87`):

- Exact integer engine: 1.3866 bits/byte, argmax accuracy 0.7043, over the
  460-window head-to-head subset. Float QAT on the same subset is identical to
  four decimals; over all 3,674 windows it is 1.4380. The grains differ and
  are stated separately above, never mixed.
- Logit correlation 1.000000 between the integer logits / 2^32 and the float
  QAT logits; the numpy int64 batch port matches the scalar `ref_engine` on
  every one of 2,048 sampled logits.
- Static bounds computed from the weights alone (input-independent worst
  case over all stages, products and partial sums) all fit i64; the widest is
  61 bits, matching the one-layer model's profile.

Twenty greedy completions through the exact integer engine (full list in the
receipt); a representative selection, verbatim:

```
'A stitch in time'                -> ' saves nine.\nThe'
'Actions speak louder'            -> ' than the ro'
'The early bird'                  -> ' catches the lette'
'Time heals'                      -> ' all wounds.\nThe capit'
'Better late than'                -> ' never.\nThe capi'
'Two heads are'                   -> ' better than neveni'
'The engine checks'               -> ' every decoding'
'In January the days'             -> ' grow on tree'
```

These are real English words and grammar, not repeated-character collapse.
The model is tiny and 8-minute-trained, so some completions are factually
wrong ("The capital of France is" -> " Panama ", "two plus three is" ->
" fifteen.") — stated plainly rather than papered over.

## Deliverable 3: cross-language bit-exactness

`python/bytelm/rust_parity_check` is a standalone std-only Rust binary (no
dependencies, `overflow-checks = true` in dev and release, built release with
`CARGO_BUILD_JOBS=2`) implementing the SPEC-E4-E6 forward plus the GLMW v1
loader. `parity_check.py` drives it: 200 diverse byte prompts (corpus
prefixes, hand-written English, LCG random bytes, structured full-range
bytes; lengths 1..33), every one of the 256 i64 logits compared against the
scalar `ref_engine` — 51,200 logits, 0 mismatches — plus the same 200 prompts
on the mod-113 bin (22,600 logits, 0 mismatches) and the internal 12,769-pair
mod-113 sweep. The harness computes every active position at every layer,
literally as the spec reads, so the parity also validates the reference's
dead-position skip.

Native generation throughput: 5.6 tokens/sec. Scope note: the harness
allocates fresh nested vectors per forward and is a correctness instrument,
not a tuned runtime; this is a lower bound on the arithmetic, and it is not
the E6 browser target.

## Scope boundaries

- This gate covers the exact Python reference and serializer, the trained
  and quantized byte-LM checkpoint, and Rust/Python bit-exactness of the
  contract semantics. It does **not** cover the final E4 `rust/general_engine`
  crate (no_std, Charon-ready) or the E6 WebAssembly/browser integration;
  the Rust here is a parity harness for this gate, not that engine.
- `ref_engine.py` is standard library only; numpy and PyTorch are used by the
  training and evaluation scripts, and the numpy integer forward is validated
  against the scalar reference before any metric is computed from it.
- The superseded round-2 evaluation is preserved as
  `evidence/e5-bytelm/eval_exact_round2_superseded.json` (3.5857 bpb) for
  history; it is not a current verdict.

## Commands and exit statuses (final artifacts)

```
python3 python/bytelm/verify_mod113.py                                   exit 0
python3 python/bytelm/train_qat.py \
    --budget-seconds 400 --max-steps 2900 --lr 2e-3                      exit 0
python3 python/bytelm/eval_exact.py                                      exit 0
python3 python/bytelm/parity_check.py                                    exit 0
python3 python/bytelm/make_receipt.py                                    exit 0
```

Everything above is reproducible from the committed sources; the corpus is
regenerated deterministically by `make_corpus.py` (fixed seed), and both
weight files round-trip through `load_check`.
