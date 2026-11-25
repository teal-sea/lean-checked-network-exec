# Proof checkpoint after the November 21 retry

The existing E4 session finished admission `2227` on Alibaba GLM 5.3 (`proc_f5a4e9c6cef3`). Its only writable checkout was `/home/thomas/worktrees/lcn-exec-e4-engine-20261120`; clean head `82061d25c4ae3332c5ec5f420ab2772d2a3dc51a`. A zero exit here means the bounded assignment returned, not that E4 passed. The existing boat.dev box `bx_9m9mrg3q` has a hard cutoff at 22:15:07 UTC on November 21; no extra lifetime, rental, model switch, publish or CI dispatch was authorized.

## Checked at this revision

- `Softmax.lean` is byte-identical to `0e142be` and the remote copy. Lean 4.35.0 elaborated the source directly, and `#print axioms LcnExec.GeneralEngine.softmax_at_spec` returned `[propext, Classical.choice, Quot.sound]`. The warning log is retained; this was not a warning-free build. This only certifies the softmax module under its hypotheses, not the full engine.
- `Attention.lean` is still red. The independent replay reproduced all bytes of `att4.log`. It contains 12 diagnostic rows at 11 distinct positions; the worker's six-error summary named the first six, not the whole log. The two stale `Attention` hashes and clock labels in the worker's early `STATE.md` are historical; use this receipt and commit for exact bytes and timestamps.
- `softmax-proof-and-logs.tar.gz` includes the compiled Softmax module and its build metadata, checked byte-for-byte. It complements `proof-checkpoint-1c48c71/compiled-proof-prefix.tar.gz`. Neither is a self-contained toolchain/cache or a final proof export.

## Next step in the same proof session

Use the exact local/guest `Attention.lean` and `Attention.log` in the receipt. With the pinned Lean toolchain, two Lean threads and `~/e4/locks/build.lock`, fix the two step-bound index-length goals, two model-projection rewrites, and two dependent-binder rewrites; re-read the remaining tail diagnostics at 169–183 after those six edits instead of assuming they are all cascades. Verify with `lake build LcnExec.GeneralEngine.Attention`, saving the build's actual exit, sources, and logs locally before the window closes. Then continue the unimplemented attention stages, Downstream, Stages, and Correct. Keep the frozen Rust, bounds, model and theorem contract intact. Full axiom audit, fresh replay, nanoda and all three negative controls still require a compiled end-to-end theorem. No heavy work on Citadel. No automatic Alibaba relaunch from a background exit callback.
