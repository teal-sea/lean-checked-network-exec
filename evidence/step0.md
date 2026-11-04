# Step 0: toolchain and loop smoke test

Run on 2026-11-04 (UTC), on one Linux x86_64 machine: Debian, glibc 2.41, 16 cores, 31 GiB
RAM. Every number below is in a file under `evidence/`, written by a script, or is quoted from a
log with the command that produced it. The pins are in
[toolchain/PINS.md](../toolchain/PINS.md).

## Gate 0

| Row | Result | Evidence |
| --- | --- | --- |
| (a) Lean versions | The pins differ. lean-checked-network's `rnn/lean` is on `leanprover/lean4:v4.35.0-rc2`; Aeneas's `backends/lean` is on `leanprover/lean4:v4.35.0`. So the adder took the vendored route: `RnnAdder/Network.lean` and `RnnAdder/Trained.lean` are copied byte for byte, and the diff is empty. Neither project was patched. The dependency route was also tried and builds on v4.35.0 (exit 0); it is recorded only, not used. | `vendor/versions.txt`, `vendored-diff.txt`, `vendor/dependency-route.log` |
| (b) nanoda on that Lean version | nanoda_bin 0.4.19 accepts v4.35.0 exports (lean4export 3.1.0, format 3.1.0). Smoke theorem: 4,901 declarations. Vendored adder theorems: 641, 641 and 1,650. No typechecker errors. | `recheck/summary.txt` |
| (c) Loop smoke test | Charon and Aeneas translated `rust/smoke` on the first attempt, with no change to the Rust. `LcnExec.Smoke.sum_zeros` is proved, with axioms `propext`, `Classical.choice` and `Quot.sound`. | `translate/smoke/`, `axioms/result.txt` |
| (d) nanoda on the existing adder theorem | lean-checked-network's own `rnn/lean`, at `0214aa3` and built on its v4.35.0-rc2: `sums_correct`, `carry_correct` and `adds` pass nanoda_bin 0.4.17 (that toolchain's) and 0.4.19. They check 641, 641 and 1,650 declarations, with no typechecker errors. | `parent-adder/summary.txt` |

The gate scripts on the smoke test and the vendored adder theorems, last run 15:47 to 16:04 UTC:

| Script | Result | Evidence |
| --- | --- | --- |
| `build.sh` | Builds Aeneas's Lean library from the pinned source (266 modules), then `LcnExec`, `RnnAdder` and the native `smoke_eval`. 583 s wall, 2,556 s user | `build/` |
| `axioms.sh` | 4 theorems pass. `sum_zeros` uses `propext`, `Classical.choice` and `Quot.sound`; the three adder theorems use `propext` and `Quot.sound` | `axioms/result.txt` |
| `recheck.sh` | nanoda_bin 0.4.19 passes 4 of 4 with no typechecker errors. Each run reports 1 pretty printer error, `"Unable to print axioms"`, as lean-checked-network's nanoda runs do | `recheck/summary.txt` |
| `diff.sh` | 1,300 seeded inputs (20 per length 0..64), 0 mismatches. On the Rust side, 658 give `ok` and 642 give `fail overflow` | `diff/smoke/summary.txt` |
| `plant_wrong_weight.sh` | Plants `sum_loop xs 0#u32 0#usize` → `sum_loop xs 1#u32 0#usize` in the translation. Caught by `build.sh`, because the proof fails. Caught by `diff.sh`: 658 of 1,300 disagree. `axioms.sh` also fails, but only because the failed build left no object file for the proof | `plant/` |
| `recheck_parent_adder.sh` | Gate 0(d) above | `parent-adder/` |

## Versions

| Command | Output |
| --- | --- |
| `toolchain/bin/aeneas -version` | `aeneas nightly-2026.11.04-d1e177b` |
| `toolchain/aeneas/charon/bin/charon version` | `0.1.308 (a58d159210b3a36fedeaba4437bda896a8b12f0d)` |
| `charon toolchain-version` | `nightly-2026-09-17` |
| `lean --version` (in `lean/`) | `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)` |
| `lake --version` | `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)` |
| `nanoda_bin -h` (v4.35.0 toolchain) | `nanoda_bin 0.4.19` |
| `nanoda_bin -h` (v4.35.0-rc2 toolchain) | `nanoda_bin 0.4.17` |
| `leanexport --version` (v4.35.0) | `{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc","version":"4.35.0"}}}` |
| `rustc --version` (in `rust/`) | `rustc 1.99.1 (58cf8f9c3 2026-10-13)` |
| `elan --version` | `elan 4.2.4 (227caca13 2026-08-25)` |
| `python3 --version` | `Python 3.13.5` |

`nanoda_bin --version` does not print a version. It prints `Error: failed to open configuration
file: Os { code: 2, kind: NotFound, message: "No such file or directory" }`, so the version comes
from the first line of `-h`.

## Commands, in order

1. `toolchain/install.sh`: Aeneas nightly binary (sha256-checked), then `make setup-charon`.
   Last line: `installed: aeneas nightly-2026.11.04-d1e177b; charon 0.1.308
   (a58d159210b3a36fedeaba4437bda896a8b12f0d)`. `make setup-charon` alone took 294 s wall
   (885 s user). See failure 1.
2. In `lean/`: `lake update` (153 s), `lake exe cache get` (28 s), `lake build` of the empty
   project (2.9 s, exit 0).
3. `scripts/vendor.sh`: gate 0(a) above.
4. `scripts/translate.sh smoke`: Charon about 52 s, Aeneas 2 s. LLBC sha256
   `7f39276b624fd8ce88758868d70dcb6c3e1fa2a7b56bc5c82e57c9f0c7ff21fd`, generated
   `lean/LcnExec/Translated/Smoke.lean` sha256
   `a5d4d3f5885bbc25eae5ac9745ebe87d117e8c6c48927fabeb4e990fa4d248b4`. A second run gave
   the same two hashes.
5. `scripts/build.sh`: 583 s wall. An earlier `lake build smoke_eval` on the prebuilt Aeneas
   objects took 313 s wall, 2,362 s user. Most of that time is the C compile of about 1,700
   modules (Mathlib, Aeneas and the rest) that the native binary links.
6. `scripts/axioms.sh`: 10.5 s.
7. `scripts/recheck.sh`: 217 s wall. nanoda takes 5 s of that; the rest is hashing the 63,544
   object files on `LEAN_PATH` before and after (the script fails if any changes). The smoke
   export is 19,589,301 bytes.
8. `scripts/diff.sh`: 14 s.
9. `scripts/plant_wrong_weight.sh`: 83 s.
10. `scripts/recheck_parent_adder.sh`: 84 s.
11. A control for the axiom gates, run by hand rather than by a script. A scratch Lean project
    on v4.35.0 with `axiom bad : 1 = 2` and `theorem uses_bad : 1 = 2 := bad`:
    - `axioms.sh` printed `uses_bad: [bad]  NOT ALLOWED: bad` and exited 1;
    - `recheck.sh` exited 1, and nanoda printed `Error: export file declares unpermitted axiom
      "bad"`.
12. Prebuilt against source-built Aeneas objects, by hand. I extracted `./lib` from the release
    asset `lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz` (sha256
    `080967101fab806fca2d3654a0c236ec42afb038119e76adde43f621e6b02e2c`) and compared it with
    the build from step 5 (`sha256sum` of every `*.olean*` file under `lib`, both sides).
    - All 1,596 files the source build produced are byte-identical to the archive's.
    - The archive has 6 more: `AeneasMeta.olean` and its `.private`, `.server` and `.hash`
      siblings, the root module `AeneasMeta`, which nothing here imports.

## The translation

The Rust (`rust/smoke/src/lib.rs`):

```rust
pub fn sum(xs: &[u32]) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    while i < xs.len() {
        acc += xs[i];
        i += 1;
    }
    acc
}
```

What Aeneas generated (`lean/LcnExec/Translated/Smoke.lean`, abridged):

- The file uses the Lean module system (`module`, `public import Aeneas`, `@[expose] public
  section`), which is Aeneas's default (`-use-lean-modules true`), inside `namespace smoke`.
- The loop body becomes its own function. `sum_loop.body xs acc i : Result (ControlFlow (U32 ×
  Usize) U32)` returns `ok (cont (acc1, i3))` to continue and `ok (done acc)` to stop. Indexing is
  `Slice.index_usize xs i`, which fails when out of bounds. `acc + i2` and `i + 1#usize` are
  checked additions that fail on overflow.
- The loop is `sum_loop xs acc i := loop (fun (acc1, i1) => sum_loop.body xs acc1 i1) (acc, i)`.
  Aeneas's `loop` combinator is defined by `partial_fixpoint`.
- The function itself is `sum xs := sum_loop xs 0#u32 0#usize`.
- The file has no `axiom`, `opaque`, `sorry`, `extern` or `implemented_by`. `translate.sh` fails if
  any of those words appear.
- `Result α` is now `ITree RustEffect α`, not an inductive with `ok`/`fail`/`div`. The Hoare triple
  `m ⦃ x => p x ⦄` is `spec`, which means total correctness: it rules out failure and divergence.

What I changed to get it through: nothing in the Rust function. Three settings matter:

- `overflow-checks = true` in both cargo profiles. Aeneas models `+=` on `u32` as failing on
  overflow, and a release build would otherwise wrap. This keeps the binary that `diff.sh`
  runs on Aeneas's semantics.
- Charon gets `-- --lib`, so it translates only the library and not the `smoke_eval` harness
  binary.
- The loop is written as `while` with an index from the start. The `for x in xs` form was not
  tried.

## The proof

The proof is in `lean/LcnExec/Smoke/Proofs.lean`, 43 lines.

- `sum_zeros_spec`: `smoke.sum xs ⦃ r => r = 0#u32 ⦄` for every slice whose entries are all
  `0#u32`. It applies `loop.spec_decr_nat` with the measure `xs.length - i` and the invariant
  `acc = 0#u32 ∧ i ≤ xs.length`. Each body branch is three `step`s and then `scalar_tac`.
- `eq_ok_of_spec`: a total-correctness triple gives `m = ok v` with `p v`. Aeneas has no
  lemma of this shape, so it is proved by cases on `Result` through its `cases_eliminator`.
- `sum_zeros`: `smoke.sum xs = ok 0#u32` for every slice of zeros, which is the smoke fact.

Errors on the way, with exact text:

1. ``error: Tactic `split` failed: Could not split an `if` or `match` expression in the goal``.
   After unfolding the body, the `if` sat under `have i1 := xs.len;`, and the invariant's
   pair projections were not reduced. `dsimp only at hacc hi ⊢` fixed both.
2. ``error(lean.unknownIdentifier): Unknown identifier `spec_ok` ``. It lives in
   `Aeneas.Std.WP`.
3. ``error: `simp` made no progress``, followed by Lean's note that the target was not
   type-correct at the `implicit` transparency level. `step` had already discharged the
   `ok (cont ...)` triple, so the goal was a plain conjunction. Removing the `simp` fixed it.

## Failures, with exact text

1. `make setup-charon`, Charon's OCaml half:

   ```
   /bin/sh: 1: dune: not found
   make[2]: *** [Makefile:8: build-dev] Error 127
   make[1]: *** [Makefile:53: build-dev-charon-ml] Error 2
   ```

   The script still exits 0: it runs `make test` and then `exit 0`. Charon's Rust binaries were
   built in the dev profile, but `charon-ml` was not. Charon's tests come after that step in
   `make test`, so they did not run. Aeneas's binary does not need `charon-ml`.
2. The first timing wrapper failed with `/bin/bash: line 1: /usr/bin/time: No such file or
   directory`. The machine has no GNU time, so the scripts use bash's `time`.
3. The first version of `plant_wrong_weight.sh` wrote into this checkout:
   - it gave the copy this checkout's `toolchain/` through a symlink, and Lake rebuilt 223 Aeneas
     modules there;
   - Lake rebuilt them because their traces in the release archive list the precompiled
     AeneasMeta library as an input, and the copy built without precompilation;
   - the 63,544 object files on `LEAN_PATH` were byte-identical before and after, so no result
     changed.

   Fixed: the copy now gets its own copy of Aeneas's Lean library, and the script fails if
   anything under the shared `lean/.lake/packages` is written. The rerun took 83 s and rebuilt
   nothing from Aeneas.
4. Lake's configuration cache. `lake update` first elaborated Aeneas's lakefile without `CI` set,
   and Lake keeps that elaboration (`lean/.lake/config/1/lakefile.olean`). So later builds
   precompiled AeneasMeta, although the scripts export `CI=1`. Fixed: the build scripts pass `-R`
   (reconfigure). The final build has no `:dynlib` targets.
5. In the plant, `axioms.sh` failed with ``error: object file '<copy>/lean/.lake/build/lib/lean/LcnExec/Smoke/Proofs.olean' of module LcnExec.Smoke.Proofs does not exist``.
   That is a consequence of the build failure, not an axiom finding. The build failure is:

   ```
   error: LcnExec/Smoke/Proofs.lean:35:2: unsolved goals
   case hInv
   xs : Slice U32
   hzero : ∀ x ∈ ↑xs, x = 0#u32
   ⊢ False
   ```

## Deviations from the brief, and gaps

- Aeneas came from the official nightly binary for the pinned commit. It was not installed through
  Nix or built from source; the reasons are in `toolchain/PINS.md`. So the Aeneas binary is a
  trusted tool built by Aeneas's CI.
- Charon's test suite did not run (failure 1).
- lean-checked-network's `verify.sh` has no nanoda step, so `recheck.sh` follows
  `acas/gen/nanoda.py`.
- Lake fetched Aeneas's prebuilt Lean objects at first, because the lakefile sets
  `preferReleaseBuild`. The scripts now pass `--no-cache` and build from source, and the source
  build matches the archive (command 12).
- Mathlib's objects come from Mathlib's cache and are not rebuilt, as in lean-checked-network.
- Files beyond the layout in the brief:
  - `toolchain/install.sh` installs the pins;
  - `scripts/common.sh` holds the shared settings;
  - `scripts/vendor.sh` produces gate 0(a);
  - `scripts/inputs.py` generates the seeded inputs for `diff.sh`;
  - `scripts/recheck_parent_adder.sh` produces gate 0(d);
  - `rust/smoke/` is the Step 0 crate;
  - `rust/rust-toolchain.toml` pins the production Rust toolchain;
  - `gates/theorems.txt` lists the theorems the gates check;
  - `gates/ci.sh` is the sequence CI runs.
- `STATUS.md` fills in the gate 0 rows from this evidence. Every other row is "not started".
- `.github/CODEOWNERS` was edited after the first commit, at Thomas's instruction. The first
  commit named @TeaLynx, taken literally from the brief; that resolves to an unrelated GitHub
  account, `tealynx`, which never had access. It now names @teal-sea.
- CODEOWNERS does not bind yet: that needs a branch protection rule on `main` requiring
  code-owner review, which is not set.
- CI checks the committed `lean/LcnExec/Translated/Smoke.lean` but does not rerun the
  translation. The translation reproduces byte for byte locally (command 4), but in CI, drift
  between `rust/` and the translation would show only through `diff.sh`'s sampled inputs.

## Next

1. Gate 1A. Port the adder's evaluator (`RnnAdder/Network.lean`: `layer`, `step`, `out`, `carry`,
   `run`) to `rust/adder` with fixed-width integers, translate it, and prove `run` and
   `finalCarry` equal to RnnAdder's for every input list. The proofs should follow the smoke
   test's pattern: `loop.spec_decr_nat` with an invariant. A bound by hand, to be checked in 1A:
   with weights in [-127, 127] and 4 units, every pre-activation is at most
   4·127 + 2·127 + 127 = 889 in absolute value.
2. For 1A, `plant_wrong_weight.sh` should perturb a weight in `rust/adder` and retranslate in
   the copy, so the proof itself rejects it. The copy then needs Charon.
3. A translation-drift job in CI: install the pins, run `translate.sh`, and fail on any
   difference. The Charon build is about 11 GB and took 5 minutes here. This changes `gates/`
   and `.github/`, so it needs @teal-sea's review.
4. Protect `main` with required code-owner review, if CODEOWNERS should bind.
5. For gate 5: lean-checked-network's `transformer/mathlib` project is on Lean v4.35.0 with
   Mathlib `56a005855ea1`, the same pins as Aeneas. The transformer theorem may therefore come in
   as a lake dependency rather than vendored. Not tried.
