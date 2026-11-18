> Session notes of 2026-11-17, copied unedited on 2026-11-18 from the machine that ran gate 1A. Paths under `scratch/`, `logs/` and `.work/` point at files that no longer exist.

# aeneas-lane notes (session 2026-11-17)

## Machine
- 4 cores, 15 GB RAM, no swap, 24 GB free at start (df: 252G size, 15G used, 24G avail).
- Ubuntu 24.04.5, glibc 2.39, gcc 13.3.0, Python 3.13.18.
- elan 4.2.4, Lean v4.35.0 installed. rustup 1.29.3; toolchains: stable (1.97.0, default), nightly, nightly-2026-05-01, 1.99.1.
- nix IS on PATH (/nix/var/nix/profiles/default/bin). check-charon-install.sh would take the nix route.
  PINS.md records the rustup route. => run install.sh with nix removed from PATH.
- rsync NOT installed (plant_wrong_weight.sh needs it). apt lists empty.
- No GNU time; use bash `time`.

## Evidence plan
- All scripts take EVIDENCE env override (common.sh). Use EVIDENCE=$ROOT/evidence/gate1a so
  committed gate-0 evidence under evidence/{build,axioms,recheck,diff,plant,translate} is untouched.
- THEOREMS=evidence/gate1a/proposed-theorems.txt for axioms.sh / recheck.sh.

## Timeline
2026-11-17T18:36:01Z notes created
- 18:36:06Z install attempt 1: FAILED after 17.8 s. PATH filter missed /usr/local/bin/nix (symlink),
  so check-charon-install.sh took `nix develop`; nix got HTTP 403 from the proxy for
  github.com/numtide/flake-utils archive. Log: logs/install-attempt1-nix-route.log
- 18:37:03Z install attempt 2 with PATH=$HOME/.elan/bin:/root/.cargo/bin:/usr/sbin:/usr/bin:/sbin:/bin
  (no nix): exit 0, real 2m37.293s user 5m27.847s sys 0m45.578s. Log: logs/install.log
  Last line: installed: aeneas nightly-2026.11.04-d1e177b; charon 0.1.308 (a58d159210b3a36fedeaba4437bda896a8b12f0d)
  Same charon-ml failure as step0.md failure 1 (`/bin/sh: 1: dune: not found`), Charon tests not run.
- Disk after install: 11G avail. charon/target = 11G, nightly-2026-09-17 = 2.5G.
- 18:41:29Z removed toolchain/aeneas/charon/charon/target (11G build dir; bin/charon, bin/charon-driver are copies). Retranslation gives same hashes: adder llbc 51fa763e..., Adder.lean 79cec4b4...; smoke llbc 6bd5c506..., Smoke.lean a5d4d3f5... (matches committed evidence; committed llbc hash 7f39276b differs: llbc embeds its absolute path)
- 18:47:24Z lake exe cache get: 1m22.6s. first lake -R build --no-cache: exit 0, real 3m50.8s user 9m7.9s (Aeneas lib from source + LcnExec incl. Translated/Adder + RnnAdder)
- 19:0xZ translation of rust/adder: first attempt, no Rust change. llbc 51fa763e..., Adder.lean 79cec4b4... (9885 bytes).
  Unchanged with src/bin/adder_eval.rs present (same hashes).
- Proof development in scratch/Proofs.lean with `lake env lean` (no olean writes). Snapshots:
  Proofs.part1.ok.lean (dot_b, thr, step, out, carry, add_bits), Proofs.part2.ok.lean (+ add_u64 loop),
  Proofs.all.ok.lean (everything, `#print axioms` all [propext, Classical.choice, Quot.sound]) -- elaboration only, NOT lake build yet.
- Key design: rustNet (Net read off adder.weights.*) + rustNet_eq : rustNet = RnnAdder.Trained.net by simp.
  Loop invariants in suffix form (drop i) for dot_b/step/add_bits; prefix form (bitPairs a b i) for add_u64.
  Helper specs applied with `step with`: cond_add_index.spec, cond_add.spec, cond_set_bit.spec.
- Errors met: (1) `step*` "does nothing" at an `if` inside a bind -> helper spec + `step with`.
  (2) take_set_succ needed List.take_set_of_le. (3) `dsimp made no progress` on `let (s, c) := (s, c)` -> `show`.
  (4) simpa type mismatch in add_bits_len_ne: simp already turned `sum.len = xs.len` into lengths.
- 19:27:14Z cold state prepared (removed lean/.lake/build, Aeneas .lake/build, packages' *.c.o.export*); starting scripts/gate1a.sh
- 19:27:20Z-19:43:58Z scripts/gate1a.sh run 1 (cold build): exit 0, real 16m37s. timings: translate 4, translate-lib-only 4,
  build 595 (cold: 266 Aeneas modules, 1773 jobs; exes 3523 jobs), statements 4, axioms 3, recheck 106, diff-adder 22,
  plant-smoke 41, plant-adder 56, plant-adder-off-by-one 47, plant-adder-rust 54, ci 62.
  axioms: 14 ok. nanoda 0.4.19: 14/14 no typechecker errors (decl counts in evidence/gate1a/recheck/summary.txt).
  diff: 3535 inputs, 0 mismatches for adder_eval and adder_net_eval.
  plants: adder (WOA 125->25 in translation): build fails Proofs.lean:58:38 unsolved goals False; diff 2141/3535 (adder_eval).
          off-by-one (124): build fails, diff not caught. rust (weights.rs in copy, retranslated): build fails; diff 2141/3535 (adder_net_eval).
  cosmetic bug: translate-lib-only/result.txt listed target/ files -> fixed after the run (list before translating). Needs final rerun.
- Coordinator commits checkpoints of the tree (git log shows "Checkpoint of the agent lanes in progress"); my files are in them.
- rsync was missing: installed by apt-get (rsync 3.2.7).
- Native evaluator of the translation is slow on long slices: 0.26 s at 511, 1.03 s at 1000, 8.5 s at 2000 (cubic). Inputs capped at 1000.
## Goal 2 (MLP) notes
- Charon translates rust/mlp as is (incl. unsafe fast.rs). Aeneas on full LLBC fails:
  "[Error] Aeneas does not yet support dereferencing raw pointers. Source: 'src/fast.rs', lines 21:25-21:38 Compiler source: interp/InterpPaths.ml, line 197"
- charon --exclude 'crate::fast' : Aeneas generates Mlp.lean (414714 bytes, 6229 lines, 21 s). Tables are Array.make literals.
- Lean on the as-generated Mlp.lean (as-is crate, fast excluded): each table def fails after ~2.7 min with
  "(deterministic) timeout at `«synthesize pending MVars»`, maximum number of heartbeats (1000000) has been reached";
  whole file 8m20s; functions then fail "Unknown identifier `weights.E1`".
- With maxHeartbeats 0, first table cut to N rows (manual runs, machine shared with other lanes' Lean jobs):
  1 row 4.1 s, 4 rows 5.9 s, 16 rows 18.3 s (elab 9.8 s), 32 rows 49-54 s peak RSS 2.4 GB,
  64 rows: killed by my 7 GB cap at 390 s (uncapped run earlier: kernel OOM-killed a lean process at 10.7 GB anon RSS after ~508 s; I believe that was this run),
  113 rows (full table): stopped by me after 20 min, not finished.
  trace.profiler: time is in elaborating the nested list literal; per-row cost grows with the number of rows already elaborated.
- Cause (my reading, not verified upstream): each `k#i8` is `I8.ofInt k (by first | decide | scalar_tac)`, one postponed tactic block per literal.
- Variant: one const per row (scripts/mlp_row_consts.py). Charon keeps the const references; Aeneas emits 339 row defs + 3 tables.
  Elaborates: 134 s, peak RSS 4.75 GB (manual), 181 s via lake build in pilot tree. The 9 function defs are textually identical to the as-is translation.
- Pilot proofs (pilot/mlp-row-consts/LcnExec/Mlp/Proofs.lean 336 lines): hidden.spec, score.spec, predict_loop.spec, predict.spec,
  predict_out_of_range, E1_eq/E2_eq/W2_eq (simp only [...global_simps, ints8_make]; decide +kernel), predict_eq. `lake env lean` 25 s, peak RSS 3.8 GB.
  Table equality: all three in ~10 s each incl. imports -> cheap.
- Parent theorem scratch build (scripts/mlp_parent_theorem.sh): started 20:33:18Z with other lanes' jobs running; Rows modules 175-317 s each.
- EXTRA_CHARON_ARGS: first named CHARON_ARGS, which collided with Charon's own env var (charon-driver panicked "invalid number").
- 21:10:07Z saved run-1 evidence copy to gate1a-run1-evidence/; cold state prepared for final gate1a run
- 20:33:18Z-20:55:02Z scripts/mlp_parent_theorem.sh (3rd run; first two failed on my scratch lakefile: roots/globs): lake build 21 modules exit 0, 1165 s wall; adds_mod_113 axioms [propext, Classical.choice, Quot.sound].
- 20:55-21:09Z scripts/mlp_pilot.sh run 1: ok (13m49s) but RSS sampling printed 0 MB and the as-generated probe ran the whole file (427 s). Fixed.
- 21:10:11Z-21:29:36Z scripts/gate1a.sh FINAL run (cold build, other lanes' jobs running): exit 0, 19m25s.
  translate 5, translate-lib-only 4, build 790, statements 4, axioms 3, recheck 95, diff-adder 23, plant-smoke 35, plant-adder 49,
  plant-adder-off-by-one 51, plant-adder-rust 57, ci 48. Statements identical to run 1.
- 21:30:03Z-21:51:55Z scripts/mlp_pilot.sh FINAL run with MLP_PILOT_PROBE_ROWS="16 32 64" MLP_PILOT_RSS_CAP=7000: exit 0, 21m52s.
  as generated: 472 s, peak RSS 1961 MB, exit 1, 3 timeouts, 6 error lines. 16 rows 16 s/1630 MB; 32 rows 49 s/1821 MB; 64 rows 425 s, 7066 MB, stopped at cap.
  variant: translation build 160 s, proofs 38 s, 6 theorems axioms ok, nanoda 5 theorems ok (3366/3370/3362/7934/5242), composed not rechecked.
- Checks at the end: rust/adder + rust/mlp sources sha256 unchanged since 18:40Z; gates/ and .github/ unchanged since cea03d4;
  parent checkout clean at 0214aa3; lean/RnnAdder hashes unchanged. c/adder/SPEC.md and scripts/aristotle.sh changed by other lanes, not by me.
- Removed my scratch: .work/plant*, .work/gate1a. Kept .work/mlp (parent-theorem project is what mlp_pilot.sh imports).
