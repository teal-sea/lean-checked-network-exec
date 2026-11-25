#!/usr/bin/env node
// Node WebAssembly receipt: instantiates web/general_engine_wasm.wasm (the
// exact binary the browser page uses) in Node.js and checks, against the native
// Rust run in evidence/e6-wasm/native-general.json:
//   (a) the valid mod113 GLMW v1 blob loads (load_check == 1) and all 12,769
//       (a, b) pairs are exact inside actual WebAssembly,
//   (b) an out-of-bounds weight byte (tok[0][0] = 99, file offset 16) is
//       rejected (load_check == 0) and the module refuses to predict afterwards,
//   (c) byte-LM greedy generation runs deterministically in WebAssembly and
//       matches native Rust bit-for-bit, tokens and raw i64 logits.
// Writes evidence/e6-wasm/RECEIPT.json. Zero dependencies, node:fs and
// node:crypto only.
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");

const ROOT = path.resolve(__dirname, "..");
const WASM = path.join(ROOT, "web", "general_engine_wasm.wasm");
const MOD113 = path.join(ROOT, "weights", "mod113_v1.bin");
const BYTELM = path.join(ROOT, "weights", "tiny_bytelm_v1.bin");
const NATIVE = path.join(ROOT, "evidence", "e6-wasm", "native-general.json");
const MANIFEST = path.join(ROOT, "evidence", "e6-wasm", "build-manifest.json");
const OUT = path.join(ROOT, "evidence", "e6-wasm", "RECEIPT.json");

const FILE_LEN = 479_504;
const MAX_SEQ = 32;
const VOCAB = 256;

const sha256 = (buf) => crypto.createHash("sha256").update(buf).digest("hex");

async function main() {
  const wasmBytes = fs.readFileSync(WASM);
  const mod113Bytes = fs.readFileSync(MOD113);
  const bytelmBytes = fs.readFileSync(BYTELM);
  const native = JSON.parse(fs.readFileSync(NATIVE, "utf8"));
  const manifest = JSON.parse(fs.readFileSync(MANIFEST, "utf8"));
  for (const [file, bytes] of [
    ["web/general_engine_wasm.wasm", wasmBytes],
    ["weights/mod113_v1.bin", mod113Bytes],
    ["weights/tiny_bytelm_v1.bin", bytelmBytes],
  ]) {
    if (sha256(bytes) !== manifest.files[file].sha256) throw new Error("build hash mismatch: " + file);
  }

  const { instance } = await WebAssembly.instantiate(wasmBytes);
  const e = instance.exports;
  const weightBuf = e.wasm_get_weight_buf_ptr();
  const tokensBuf = e.wasm_get_tokens_buf_ptr();
  const memoryBytes = () => new Uint8Array(e.memory.buffer, weightBuf, FILE_LEN);
  const tokens = new Uint32Array(e.memory.buffer, tokensBuf, MAX_SEQ);
  let logitsView = null;
  let logitsPtr = 0;

  const writeWeights = (bytes) => {
    if (bytes.length !== FILE_LEN) {
      throw new Error(`weight file must be ${FILE_LEN} bytes, got ${bytes.length}`);
    }
    memoryBytes().set(bytes);
  };

  // ---- (a) valid mod113 blob: load_check, then all 12,769 pairs ----------
  writeWeights(mod113Bytes);
  const loadOk = e.wasm_load_weights();
  if (loadOk !== 1) throw new Error("mod113_v1.bin failed load_check inside WebAssembly");
  tokens[2] = 113;
  let wrong = 0;
  let wrongFirst = null;
  const t0 = performance.now();
  for (let a = 0; a < 113; a++) {
    for (let b = 0; b < 113; b++) {
      tokens[0] = a;
      tokens[1] = b;
      const got = e.wasm_predict_next(3);
      if (got !== (a + b) % 113) {
        wrong++;
        if (!wrongFirst) wrongFirst = [a, b, got, (a + b) % 113];
      }
    }
  }
  const sweepMs = performance.now() - t0;
  const checkA = {
    description: "valid mod113 GLMW v1 blob loads and all 12,769 (a, b) pairs are exact inside WebAssembly",
    load_check: loadOk,
    pairs: 12769,
    exact: 12769 - wrong,
    wrong,
    wrong_first: wrongFirst,
    single_thread_ms: Math.round(sweepMs),
    note: "tokens [a, b, =] with = as token 113, predict_next over logits 0..113",
  };
  if (wrong !== 0) throw new Error(`mod113 sweep: ${wrong} wrong pairs, first ${JSON.stringify(wrongFirst)}`);

  // ---- (b) out-of-bounds byte rejected ------------------------------------
  const corrupt = Uint8Array.from(bytelmBytes);
  corrupt[16] = 99; // tok[0][0], the first payload byte; 99 > 68
  writeWeights(corrupt);
  const loadCorrupt = e.wasm_load_weights();
  tokens[0] = 21;
  tokens[1] = 56;
  tokens[2] = 113;
  const predictAfterFail = e.wasm_predict_next(3);
  const logitsAfterFail = e.wasm_forward_logits(3);
  const checkB = {
    description: "out-of-bounds weight byte is rejected inside WebAssembly",
    byte: 99,
    offset: 16,
    field: "tok[0][0]",
    load_check: loadCorrupt,
    predict_next_after_fail: predictAfterFail,
    forward_logits_after_fail: logitsAfterFail,
    note: "load_check == 0, and the module drops the weights so prediction returns -1 and logits 0",
  };
  if (native.corrupt.load_check !== false || !native.corrupt.parsed ||
      loadCorrupt !== 0 || predictAfterFail !== -1 || logitsAfterFail !== 0) {
    throw new Error(`corrupt-weight rejection failed: load ${loadCorrupt}, predict ${predictAfterFail}, logits ${logitsAfterFail}`);
  }

  // ---- (c) byte-LM greedy: Wasm vs native, bit-for-bit --------------------
  writeWeights(bytelmBytes);
  const bytelmLoad = e.wasm_load_weights();
  if (bytelmLoad !== 1) throw new Error("tiny_bytelm_v1.bin failed load_check inside WebAssembly");

  const prompts = native.bytelm.prompts;
  let promptMismatches = 0;
  const promptResults = [];
  for (const p of prompts) {
    const enc = new TextEncoder().encode(p.prompt_utf8);
    if (enc.length !== p.prompt_len || JSON.stringify(Array.from(enc)) !== JSON.stringify(p.prompt_bytes)) {
      throw new Error(`prompt bytes mismatch for ${p.prompt_utf8}`);
    }
    tokens.fill(0);
    for (let i = 0; i < p.prompt_len; i++) tokens[i] = enc[i];
    const steps = p.final_len - p.prompt_len;
    const started = performance.now();
    const finalLen = e.wasm_generate_greedy(p.prompt_len, steps);
    const generated = [];
    for (let i = p.prompt_len; i < finalLen; i++) generated.push(tokens[i]);
    const match = finalLen === p.final_len && JSON.stringify(generated) === JSON.stringify(p.tokens);
    if (!match) promptMismatches++;
    promptResults.push({ prompt_utf8: p.prompt_utf8, prompt_bytes: Array.from(enc), final_len: finalLen,
      generated, tokens_match_native: match, wall_ms: performance.now() - started });
  }

  // Determinism: the first prompt, generated twice, byte for byte.
  const runPrompt0 = () => {
    const enc = new TextEncoder().encode(prompts[0].prompt_utf8);
    tokens.fill(0);
    for (let i = 0; i < enc.length; i++) tokens[i] = enc[i];
    const finalLen = e.wasm_generate_greedy(enc.length, prompts[0].final_len - enc.length);
    return Array.from(tokens.slice(enc.length, finalLen));
  };
  const run1 = runPrompt0();
  const run2 = runPrompt0();
  const deterministic = JSON.stringify(run1) === JSON.stringify(run2);

  // Raw i64 logits of prompt 0, bit-for-bit against native.
  const enc0 = new TextEncoder().encode(prompts[0].prompt_utf8);
  tokens.fill(0);
  for (let i = 0; i < enc0.length; i++) tokens[i] = enc0[i];
  const ptr = e.wasm_forward_logits(enc0.length);
  if (!ptr || native.bytelm.prompt0_logits.length !== VOCAB ||
      !native.bytelm.prompt0_logits.every((v) => typeof v === "string" && /^-?\d+$/.test(v))) {
    throw new Error("expected 256 exact signed decimal logits");
  }
  if (ptr !== logitsPtr) {
    logitsPtr = ptr;
    logitsView = new BigInt64Array(e.memory.buffer, ptr, VOCAB);
  }
  let logitsMismatches = 0;
  let firstLogitMismatch = null;
  for (let v = 0; v < VOCAB; v++) {
    if (logitsView[v] !== BigInt(native.bytelm.prompt0_logits[v])) {
      logitsMismatches++;
      if (!firstLogitMismatch) firstLogitMismatch = { v, wasm: logitsView[v].toString(), native: String(native.bytelm.prompt0_logits[v]) };
    }
  }

  const checkC = {
    description: "byte-LM greedy generation in WebAssembly matches native Rust bit-for-bit and is deterministic",
    load_check: bytelmLoad,
    prompts: prompts.length,
    greedy_token_sequences_match_native: promptMismatches === 0,
    prompt_mismatches: promptMismatches,
    prompts_detail: promptResults,
    deterministic_repeat: deterministic,
    prompt0_logits_compared: VOCAB,
    prompt0_logits: Array.from(logitsView, (v) => v.toString()),
    prompt0_logits_mismatches: logitsMismatches,
    prompt0_first_logit_mismatch: firstLogitMismatch,
    native_reference: "evidence/e6-wasm/native-general.json (rust example e6_native, release, host build)",
  };
  if (promptMismatches !== 0 || !deterministic || logitsMismatches !== 0) {
    throw new Error("byte-LM Wasm/native comparison failed");
  }

  const receipt = {
    gate: "E6",
    what: "general_engine served in WebAssembly: browser UI and automated verification",
    date_utc: new Date().toISOString(),
    runner: {
      node: process.version,
      platform: `${process.platform} ${process.arch}`,
      wasm: "WebAssembly.instantiate of web/general_engine_wasm.wasm (the same binary web/index.html loads)",
    },
    artifacts: {
      wasm: { path: "web/general_engine_wasm.wasm", bytes: wasmBytes.length, sha256: sha256(wasmBytes) },
      weights: {
        mod113_v1: { path: "weights/mod113_v1.bin", bytes: mod113Bytes.length, sha256: sha256(mod113Bytes) },
        tiny_bytelm_v1: { path: "weights/tiny_bytelm_v1.bin", bytes: bytelmBytes.length, sha256: sha256(bytelmBytes) },
      },
      native_reference: { path: "evidence/e6-wasm/native-general.json", sha256: sha256(fs.readFileSync(NATIVE)) },
    },
    checks: {
      a_valid_mod113_loads_and_12769_pairs_exact_in_wasm: checkA,
      b_out_of_bounds_weight_byte_rejected_in_wasm: checkB,
      c_bytelm_greedy_wasm_matches_native_bit_for_bit: checkC,
    },
    scope: "Node WebAssembly only. Browser replay is a separate check.",
  };

  fs.mkdirSync(path.dirname(OUT), { recursive: true });
  fs.writeFileSync(OUT, JSON.stringify(receipt, null, 2) + "\n");
  console.log(`wrote ${OUT}`);
  console.log(`(a) mod113: load_check ${loadOk}, 12,769/12,769 exact, ${Math.round(sweepMs)} ms single-threaded`);
  console.log(`(b) corrupt tok[0][0] = 99: load_check ${loadCorrupt}, predict_next ${predictAfterFail}`);
  console.log(`(c) bytelm: ${prompts.length}/${prompts.length} greedy sequences match native, logits ${VOCAB}/${VOCAB}, deterministic ${deterministic}`);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
