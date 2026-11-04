# Status

Every number here comes from a file under `evidence/`. "Not started" means no work has been
done and no evidence exists.

| Gate | What | Cap | Status | Evidence |
| --- | --- | --- | --- | --- |
| 0(a) | Toolchain: Lean versions reconciled, or vendored with diff | 2 agent-days for gate 0 | Passed. The versions differ (lean-checked-network `v4.35.0-rc2`, Aeneas `v4.35.0`), so the adder is vendored; the diff is empty | `evidence/vendor/versions.txt`, `evidence/vendored-diff.txt` |
| 0(b) | Toolchain: nanoda checks that Lean version | | Passed. nanoda_bin 0.4.19 on `v4.35.0` exports: 4 theorems, no typechecker errors | `evidence/recheck/summary.txt` |
| 0(c) | Toolchain: loop smoke test translated and one fact proved | | Passed. `LcnExec.Smoke.sum_zeros`, axioms `propext`, `Classical.choice`, `Quot.sound`. Compile-and-diff: 0 mismatches in 1,300 inputs. The planted wrong constant is caught | `evidence/translate/smoke/`, `evidence/axioms/result.txt`, `evidence/diff/smoke/summary.txt`, `evidence/plant/summary.txt` |
| 0(d) | Toolchain: nanoda rechecks the existing adder theorem | | Passed. 3 of 3 theorems under nanoda_bin 0.4.17 and 0.4.19, no typechecker errors | `evidence/parent-adder/summary.txt` |
| 1A | Adder in safe Rust proved equal to RnnAdder for every input: standard axioms only, nanoda recheck, planted wrong weight rejected, compile-and-diff agrees | 5 agent-days | Not started | |
| 1B | Adder in C to Aristotle, memory safety only, credits capped at $100 | 1 agent-day | Not started | |
| 2 | Thomas's go on the transformer | | Not started | |
| 3 | Requantize the transformer with per-layer rescaling; Python check on all 12,769 inputs; record the maximum intermediate width | | Not started | |
| 4 | Regenerate the transformer theorem for the rescaled model | | Not started | |
| 5 | Transformer in Rust, same theorem shape as 1A | | Not started | |
| 6 | Write-up: audit surface as line counts, trusted tools by name and version, all from `evidence/` | | Not started | |
| 7 | Publish, on Thomas's separate yes | | Not started | |

Gate 0 ran locally on 2026-11-04. Commands, versions and failures are in
[evidence/step0.md](evidence/step0.md).
