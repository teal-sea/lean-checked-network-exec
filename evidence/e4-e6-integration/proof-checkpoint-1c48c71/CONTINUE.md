# Current proof checkpoint, 2026-11-20 05:10 UTC

Source: `vizier/e4-general-engine-20261120`, commit `1c48c71b69d708df19e086743ea4b4d63600ec24`, worktree `/home/thomas/worktrees/lcn-exec-e4-engine-20261120`. Existing interactive coding session: `local-e32a1e1d956bd4f8fc89d594d53f1d8d8f8dc8d090c454498ce2707b5db5d168`, Alibaba `alibaba-token-plan/glm-5.3` via Provider gateway. The last worker attempt ended at its 100-tool cap, with 200 total main calls across both attempts. This is not an Alibaba quota error. Provider plan balance is not readable through the installed tools. Do not hook an automatic Token Plan inference launch to this process-exit notice. Reuse the original session for a directly initiated interactive continuation; no other worker, metered fallback or provider substitution.

The current box is `bx_9m9mrg3q` with checkout `/home/user/e4/repo` and original cutoff 09:12:42 UTC today. Verify it remains reachable and the local/remote hashes still match before compiling. No new rental, extra lifetime, publication or builds on Citadel. No changes to `gates/`, Rust arithmetic, round-5 weights or bounds to make a proof pass.

## What is accepted and what is not

`RECEIPT.json` ties the exact checkpoint and compiler to a coordinator replay on the existing box: `lake build LcnExec.GeneralEngine.Load` exited 0 against cached objects; `lake build LcnExec.GeneralEngine.Softmax` exited 1. The captured `Softmax.log` has 12 source diagnostics. This is not an independent fresh kernel replay of the program and is not the full engine theorem.

## First implementation checkpoint

Work on `LcnExec/GeneralEngine/Softmax.lean` only until the next build passes. Keep the closed Rust and Load sources untouched. Work in the existing remote proof environment with `LEAN_NUM_THREADS=2`; point Lake at the pinned Lean v4.35.0. Use `timeout 70s lake build LcnExec.GeneralEngine.Softmax > <owned-log> 2>&1`, recording the producer exit directly, not `tee`'s status.

Use the retained log, not the worker's rough error count. The exp loop has a range-index normalization goal and a scaled denominator invariant. Solve these in small local helper lemmas. In both loops, check the actual dependent indexed equality expected on the exit and initialization paths; do not use arbitrary `omega` fuel increases to patch mismatched types. Structure postconditions for the Aeneas `step` tactic rather than giving it raw `∃` or `And` program specifications. Preserve equality, nonnegativity and the joint sum bound. Save the first verified module commit before moving on and save partial source plus the actual red log at a stable intermediate checkpoint if the tool limit is approaching.

After this checkpoint the agreed order is Attention, Downstream, Stages and Correct, then the standard-axiom audit, fresh replay, nanoda and all three semantic negative controls. Reuse the supporting objects already built. A remote timeout or an unexpected kernel diagnostic is not a semantic negative-control pass. The E5 model is integrated locally; E6's final browser replay must use the exact source that makes it through the proof gate.
