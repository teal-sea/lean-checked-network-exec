# E6 private browser integration

The page runs the Rust engine verified in E4 and the real byte-level model trained in E5. The [build manifest](build-manifest.json) records the hashes of the WebAssembly binary and both weight files.

## Open the private page

Unpack the ZIP and run the command below from the extracted directory using Node.js. Open `http://127.0.0.1:8765/web/index.html` in your browser. The server listens only on your machine. Stop it with Ctrl-C; the demo has no remote dependencies.

```sh
node scripts/e6_browser_replay.js --serve 8765
```

Start with **Generate** to see byte-by-byte text completion and the raw scores. The **mod-113** tab runs the addition checkpoint; the full 12,769-pair check takes about a minute on the two-CPU Linux test setup with overflow checks enabled.

## Automated browser replay on Linux

From the unpacked directory, use an existing Node.js and Chromium:

```sh
node scripts/e6_browser_replay.js
```

The harness starts a loopback HTTP server and a fresh Chromium profile on at most two CPUs. Its output under `evidence/e6-wasm/browser-run-*/` includes response-body hashes, the native comparison, upload rejection and restoration, and screenshots. It stops the browser and server afterward. If Chromium reports `Socket path too long`, extract to a shorter private path or point `CHROMIUM` to a launcher that sets a short, private `TMPDIR` before running Chromium. No sandbox settings need to change.

The coordinator replay on Chromium 156 matched the served Wasm and both weight files to the manifest, matched native Rust's sample logits, rejected an invalid upload, and restored byte-identical generation without reloading. All 12,769 addition pairs were exact. The earlier worker's sandbox could not start the browser; that was a harness startup failure, not a page result.

## Local results

| Check | Measured result |
| --- | --- |
| Exact Rust 1.99.1 offline locked Wasm build | Passed with overflow checks on |
| Wrapper parser tests | 4/4 passed |
| Native mod-113 | 12,769/12,769 exact in 31.789 s, frozen logits FNV-1a `6cb24f7670e8562e` |
| Single-threaded Node Wasm mod-113 | 12,769/12,769 exact in 121.101 s |
| Trained byte model, native versus Node Wasm | 5/5 prompt byte and greedy sequence matches, 256/256 signed logits for the first prompt, deterministic repeat |
| Native and Node Wasm rejection | Native parsed the corrupt file and rejected its bounds. Wasm returned load 0, predict −1 and logits pointer 0 |
| Upload recovery, real Wasm with a Node DOM fixture | Pre-fix failed and post-fix passed |

The first prompt, `A stitch in time`, generated the 16 bytes ` saves nine.\nThe` in both native Rust and Node Wasm. One recorded Wasm run took 5.38 s for those 16 steps. The verifier stores native and Wasm logits as signed decimal strings and compares them as `BigInt` values. See [the native reference](native-general.json) and [the Node Wasm receipt](RECEIPT.json).

The earlier provisional browser run exposed the [original upload failure](../e4-e6-integration/provisional-browser-replay-20261120.json). The checked-in pre-fix JavaScript and HTML are saved byte-for-byte, and [the failing replay](upload-regression-before.json) uses the rebuilt Wasm. The rejected upload overwrote the recovery buffer, with Generate enabled and Restore hidden. [The repaired replay](upload-regression-after.json) retains the approved file hash, exposes Restore, blocks generation, and generates the same bytes after restoration. The [fixture manifest](fixtures/manifest.json) records the one-byte mutation at offset 16.

## Rebuild from the integration worktree

```sh
sh web/build.sh
node scripts/e6_upload_regression.js before  # expected exit 1
node scripts/e6_upload_regression.js after
python3 -I scripts/e6_package.py
node scripts/e6_wasm_receipt.js
```

Regenerate the native reference on the repository checkout with the installed Rust 1.99.1 toolchain, using an ignored target directory.

```sh
cargo +1.99.1 run --manifest-path rust/general_engine_wasm/Cargo.toml \
  --release --offline --locked -j 2 --target-dir rust/general_engine_wasm/target/e6-native-replay \
  --example e6_native
```

Use `python3 -I scripts/e6_package.py` after regenerating the native reference to update the manifest. The manifest binds exact bytes, including the reference's measured timings. Packaging the same inputs produces the same ZIP.

## Proof scope

The Lean theorems `LcnExec.GeneralEngine.general_engine_correct` and `LcnExec.GeneralEngine.forward_logits_spec` cover translated `predict_next` and `forward_logits` for every load-accepted weight set and the supported input interface, including safe rejection of invalid inputs. The proof concerns the Aeneas translation and the frozen integer specification. The Rust-to-Lean translation tool, Rust-to-Wasm compiler, Wasm wrapper, binary parser, generation loop, non-greedy sampler, browser and transport are not proved by those theorems. The checkpoints are identified by hashes and tested separately.
