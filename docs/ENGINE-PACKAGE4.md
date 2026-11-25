# Package 4: statement and build-runner repair

Base revision: `73c6c35f51d8a000206690193e55383b41b6c6d8`.
Branch: `vizier/engine-weights-input-20261118`.
The governing statement review is `/home/thomas/.hermes/artifacts/portfolio-takeover-20261118/engine-statement-review.md`.

## Finding disposition

| Review finding | Repair and remaining boundary |
| --- | --- |
| 2 | Both claim documents give every exact inclusive shape/bound row, table non-guarantees, sufficient-box scope and trained-instance distinction. |
| 4 | Both documents identify the fixed architecture and inventory scales, shifts, truncating division, clipping, tie-breaking and list totalisation. No float64 or real-softmax equivalence is claimed. |
| 6 | The theorem document states accepted unchanged weights and inputs below 113 as the valid-input no-panic boundary. It states that predict/logits do not call load_check. The actual Rust comment correction remains open for the next authorized source change and retranslation. |
| 8 | Both documents state the platform-width boundary and distinguish the historical receipt from a new extraction. |
| 10 | The run path now bootstraps pinned Rust/Charon and checksum-pinned Aeneas, emits fresh LLBC/Lean outside the checkout, and requires raw byte equality with the committed translation before proof builds. Actual bootstrap/extraction was not executed in this zero-spend package. |
| 11 | Plan/dry-run cannot write acceptance, even with an inherited worker marker. Generic receipt writing reserves the acceptance filename. The final writer requires completed extraction/checker steps and exclusive creation. Documents require authenticated receipt and independent exact-type/byte inspection, not a zero exit. Mechanical comparison with an independently frozen expected theorem type remains outside this package. |
| 12 | Both documents list model adequacy, logical checking, Rust semantics, translation, checkpoint interpretation, provenance machinery, artifact binding, independent checking, concrete checker execution and compiled-executable boundaries separately. |
| 13 | Both documents use the review's allowed-today sentence verbatim. Stale forward-equivalence status and recurrent-adder claims are removed. SONNX ranking is narrowed to a serious unresolved comparison; stale usage instructions are removed. |

Findings 1, 3, 5 and 7 remain supported observations, not new proof executions. Finding 9's hostile concurrent-file replacement risk is documented, not repaired in the generators. Finding 14's unproved boundaries remain explicit. No formal statement, view, proof module, Rust source, translation, gate or workflow was changed.

## Executed verification

Every check ran in the foreground through:

```sh
flock /home/thomas/.hermes/cache/scratch/lean-single-check.lock \
  systemd-run --user --scope -p MemoryMax=6G -p CPUQuota=200% \
  env LEAN_NUM_THREADS=2 <lightweight command>
```

- Final runner suite: 23 tests, zero failures, `pilot/engine/package4-tests-final.log`.
- Existing checkpoint generator suite: two tests, zero failures, `pilot/engine/package4-generator-tests.log`.
- Real final dry run: exit zero, 139 frozen source hashes matched, 135-module gate closure, `accepted: false`, no acceptance file, `pilot/engine/package4-dry-final/dry-run.json`.
- Static/source check: exit zero, 13 bound rows matched in both documents, exact allowed status wording, script syntax, whitespace and protected-path checks passed. The final dry-run runner hash equals the current runner hash. See `pilot/engine/package4-source-check.json` and its adjacent log.
- Earlier successful 21-test runner suite and real dry run are retained as pre-hardening evidence in `package4-tests.log` and `package4-dry/`. They do not stand in for the final revision's checks.

Extraction tests use synthetic executables with explicit fixture labels. They exercise exact-byte success, newline-only drift rejection, subprocess failure, missing output and ambient-flag removal. These are harness tests, not real translator execution or kernel verification. A separate source-only reviewer reported no concrete defect; it ran no commands and did not independently inspect the git diff, so that report is not execution evidence.

The estimate adds an unmeasured 1800-second Rust/Charon bootstrap and extraction allowance. The revised plan is retained in `pilot/engine/package4-dry-final/estimate.json`. It is an estimate, not a measured dedicated-run completion time or a vendor quote.

## Open work

No Lean build, actual extraction, installation, rental, paid call, run mode, unconditional final theorem check or real independent-checker control was executed. The source-built Charon bootstrap and Debian rustup dependency remain unexercised end to end. Authorize and price a dedicated run next, then inspect exact theorem type, source/object/export hashes and real checker/control logs before accepting the stronger trained result. Parser hardening, Rust comment correction/retranslation, executable fidelity and prior-art artifact inspection remain separate work.
