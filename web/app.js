/* general_engine lab: zero-dependency front end for general_engine_wasm.wasm.
 * All arithmetic runs inside the WebAssembly module built from the proved
 * general_engine crate (overflow-checks on). This file only moves bytes. */
"use strict";

const MAX_SEQ = 32;
const VOCAB = 256;
const FILE_LEN = 479504;
// Every entry load_check touches: 462,848 int8 (tok 32768, pos 4096, 2 layers of
// 196,608, u 32768) plus 2,080 i64 (bin 1024, bout 256, exp tables 800).
const BOUNDS_CHECKED = 464928;

const $ = (id) => document.getElementById(id);
const state = {
  wasm: null,
  weightBuf: 0,
  tokens: null,       // Uint32Array over the wasm token buffer
  logits: null,       // BigInt64Array over the wasm logits buffer
  logitsPtr: 0,
  pristine: null,     // Last approved byte-model file, independent of the Wasm buffer
  weightName: "",
  byteReady: false,
  loadingCustom: false,
  mod113Bytes: null,
  tab: "bytelm",
  running: false,
  stopFlag: false,
  decoder: null,
};

/* ------------------------------------------------------------------ wasm */

async function initWasm() {
  const response = await fetch("general_engine_wasm.wasm");
  const { instance } = await WebAssembly.instantiateStreaming(response);
  state.wasm = instance.exports;
  state.weightBuf = state.wasm.wasm_get_weight_buf_ptr();
  state.tokens = new Uint32Array(state.wasm.memory.buffer, state.wasm.wasm_get_tokens_buf_ptr(), MAX_SEQ);
  state.logitsPtr = 0;
  $("engine-meta").textContent =
    "engine: general_engine_wasm.wasm loaded, " + instance.exports.memory.buffer.byteLength + " bytes linear memory";
}

function writeWeights(bytes) {
  if (bytes.length !== FILE_LEN) {
    throw new Error("GLMW v1 file must be exactly " + FILE_LEN + " bytes, got " + bytes.length);
  }
  new Uint8Array(state.wasm.memory.buffer, state.weightBuf, FILE_LEN).set(bytes);
}

function loadWeights(bytes, badge) {
  writeWeights(bytes);
  const ok = state.wasm.wasm_load_weights() === 1;
  badge.className = "badge " + (ok ? "pass" : "fail");
  badge.textContent = ok
    ? "load_check: PASS: all " + BOUNDS_CHECKED + " int8/i64 bounds verified"
    : "load_check: FAIL";
  return ok;
}

function syncByteControls() {
  const busy = state.running || state.loadingCustom;
  $("file-input").disabled = busy;
  $("generate-btn").disabled = busy || !state.byteReady;
  $("corrupt-btn").disabled = busy || !state.byteReady;
  $("restore-btn").disabled = busy;
  $("restore-btn").classList.toggle("hidden", state.byteReady || !state.pristine);
}

function rejectByteWeights(name, reason) {
  state.byteReady = false;
  $("load-badge").className = "badge fail";
  $("load-badge").textContent = "load_check: FAIL";
  $("weight-note").textContent = name + " rejected: " + reason +
    (state.pristine ? ". Restore valid weights to resume generation." : ".");
  $("gen-part").textContent = "";
  $("logit-body").replaceChildren();
  $("gen-stats").textContent = "generation paused: rejected weights";
  syncByteControls();
}

function approveByteWeights(bytes, name, note) {
  if (!loadWeights(bytes, $("load-badge"))) {
    rejectByteWeights(name, "the GLMW parser or engine bounds check failed");
    return false;
  }
  state.pristine = bytes.slice();
  state.weightName = name;
  state.byteReady = true;
  $("weight-name").textContent = name;
  $("weight-note").textContent = note;
  syncByteControls();
  return true;
}

/* ------------------------------------------------------------------ tabs */

function switchTab(tab) {
  if (state.running || state.loadingCustom) return;
  state.tab = tab;
  for (const btn of $("tabs").children) {
    btn.classList.toggle("active", btn.dataset.tab === tab);
  }
  $("tab-bytelm").classList.toggle("active", tab === "bytelm");
  $("tab-mod113").classList.toggle("active", tab === "mod113");
  // One wasm instance, one weight buffer: switching tabs reloads its weights.
  if (tab === "bytelm" && state.byteReady) {
    if (!loadWeights(state.pristine, $("load-badge"))) {
      rejectByteWeights(state.weightName, "reloading the approved file failed");
    }
  } else if (tab === "mod113" && state.mod113Bytes) {
    loadWeights(state.mod113Bytes, $("m-load-badge"));
  }
}

/* ------------------------------------------------------------- byte tab */

function setTokens(windowBytes) {
  const n = Math.min(windowBytes.length, MAX_SEQ);
  for (let i = 0; i < n; i++) state.tokens[i] = windowBytes[windowBytes.length - n + i];
  return n;
}

function charLabel(b) {
  if (b === 10) return "\\n";
  if (b === 13) return "\\r";
  if (b === 9) return "\\t";
  if (b >= 32 && b < 127) return String.fromCharCode(b);
  if (b >= 128) return "utf8";
  return ".";
}

function renderLogits(chosen) {
  const ptr = state.wasm.wasm_forward_logits(currentWindowLen());
  if (ptr === 0) return;
  if (state.logitsPtr !== ptr) {
    state.logitsPtr = ptr;
    state.logits = new BigInt64Array(state.wasm.memory.buffer, ptr, VOCAB);
  }
  // Top 8 by strict-first-maximum ordering over the full 256-byte vocab.
  const top = [];
  for (let v = 0; v < VOCAB; v++) {
    const value = state.logits[v];
    let i = top.length;
    while (i > 0 && value > top[i - 1].value) i--;
    if (i < 8) {
      top.splice(i, 0, { v, value });
      if (top.length > 8) top.pop();
    }
  }
  const body = $("logit-body");
  // Clearing the table body with innerHTML = "" is safe (no content, fixed markup).
  body.innerHTML = "";
  top.forEach((entry, rank) => {
    // All cell content is engine-computed numbers or a fixed label set, built
    // with DOM methods rather than innerHTML.
    const tr = document.createElement("tr");
    if (entry.v === chosen) tr.className = "chosen";
    const cells = [
      String(rank + 1),
      String(entry.v),
      charLabel(entry.v),
      entry.value.toString(),
      entry.v === chosen ? "chosen" : "",
    ];
    cells.forEach((text, i) => {
      const td = document.createElement("td");
      td.textContent = text;
      if (i === 2) td.className = "charcell";
      if (i === 3) td.className = "numcell";
      tr.appendChild(td);
    });
    body.appendChild(tr);
  });
}

let genWindow = [];

function currentWindowLen() {
  return Math.min(genWindow.length, MAX_SEQ);
}

function updatePromptMeta() {
  const bytes = new TextEncoder().encode($("prompt").value);
  const inWindow = Math.min(bytes.length, MAX_SEQ);
  $("prompt-meta").textContent =
    bytes.length + " bytes \u00b7 context window: " + inWindow + " / " + MAX_SEQ +
    " bytes" + (bytes.length > MAX_SEQ ? " (sliding: engine sees the last " + MAX_SEQ + ")" : "");
}

function sleepFrames() {
  // A 0 ms timeout rather than requestAnimationFrame: rAF is throttled or
  // paused entirely in background tabs, while timers still let the UI paint.
  return new Promise((resolve) => setTimeout(resolve, 0));
}

async function generate() {
  if (state.running || state.loadingCustom || !state.byteReady || state.tab !== "bytelm") return;
  const promptBytes = new TextEncoder().encode($("prompt").value);
  if (promptBytes.length === 0) {
    $("gen-stats").textContent = "prompt is empty, nothing to condition on";
    return;
  }
  const mode = $("mode").value;
  const steps = Math.max(1, Math.min(512, $("steps").value | 0));
  const temp = Math.max(0.05, Math.min(64, parseFloat($("temp").value) || 1.0));
  const tNum = Math.max(1, Math.min(4096, Math.round(temp * 64)));
  const tDen = 64;
  const k = Math.max(1, Math.min(256, $("topk").value | 0));
  const seed = ($("seed").value | 0) || 1;

  state.running = true;
  state.stopFlag = false;
  syncByteControls();
  $("stop-btn").disabled = false;
  $("prompt-part").textContent = $("prompt").value;
  $("gen-part").textContent = "";
  state.decoder = new TextDecoder("utf-8", { fatal: false });
  genWindow = Array.from(promptBytes);

  const t0 = performance.now();
  let produced = 0;
  for (let s = 0; s < steps && !state.stopFlag; s++) {
    const n = setTokens(genWindow);
    let next;
    if (mode === "greedy") {
      next = state.wasm.wasm_predict_next(n);
    } else {
      next = state.wasm.wasm_sample_topk(n, k, tNum, tDen, seed);
    }
    if (next < 0) {
      $("gen-stats").textContent = "engine rejected the input (weights or tokens out of range)";
      break;
    }
    renderLogits(next);
    genWindow.push(next);
    if (genWindow.length > 4 * MAX_SEQ) genWindow = genWindow.slice(-2 * MAX_SEQ);
    produced++;
    $("gen-part").textContent += state.decoder.decode(new Uint8Array([next]), { stream: true });
    const ms = (performance.now() - t0) / produced;
    $("gen-stats").textContent = produced + " tokens \u00b7 " + ms.toFixed(1) + " ms/token \u00b7 " + mode +
      (mode === "sample" ? " (T=" + temp + ", k=" + k + ", seed=" + seed + ")" : "");
    await sleepFrames();
  }
  if (state.decoder) $("gen-part").textContent += state.decoder.decode();
  state.running = false;
  syncByteControls();
  $("stop-btn").disabled = true;
}

function corruptTest() {
  if (!state.byteReady || state.running || state.loadingCustom || state.tab !== "bytelm") return;
  const corrupt = state.pristine.slice();
  corrupt[16] = 99; // tok[0][0], first payload byte, out of [-68, 68]
  if (loadWeights(corrupt, $("load-badge"))) {
    // Do not leave the control file active if the checker unexpectedly accepts it.
    writeWeights(new Uint8Array(FILE_LEN));
    state.wasm.wasm_load_weights();
    rejectByteWeights("corrupt test", "unexpected engine acceptance of tok[0][0] = 99");
  } else {
    rejectByteWeights("corrupt test", "tok[0][0] = 99 at byte 16 exceeds the [-68, 68] bound");
  }
}

function restoreWeights() {
  if (!state.pristine || state.running || state.loadingCustom || state.tab !== "bytelm") return;
  if (approveByteWeights(state.pristine, state.weightName,
    state.weightName + " restored from the last approved file")) {
    $("gen-stats").textContent = "valid weights restored · ready to generate";
  }
}

async function loadCustomFile(file) {
  if (state.running || state.loadingCustom || state.tab !== "bytelm") return;
  state.loadingCustom = true;
  syncByteControls();
  try {
    const bytes = new Uint8Array(await file.arrayBuffer());
    approveByteWeights(bytes, file.name, file.name + ": approved custom GLMW v1 weights");
  } catch (e) {
    rejectByteWeights(file.name, e.message);
  } finally {
    state.loadingCustom = false;
    syncByteControls();
  }
}

/* ----------------------------------------------------------- mod113 tab */

function predictPair() {
  if (state.running || state.tab !== "mod113") return;
  const a = clampInt($("m-a").value, 0, 112);
  const b = clampInt($("m-b").value, 0, 112);
  $("m-a").value = a;
  $("m-b").value = b;
  loadWeights(state.mod113Bytes, $("m-load-badge"));
  state.tokens[0] = a;
  state.tokens[1] = b;
  state.tokens[2] = 113;
  const got = state.wasm.wasm_predict_next(3);
  const want = (a + b) % 113;
  $("m-predict-out").textContent =
    "tokens [a, b, =] = [" + a + ", " + b + ", 113]\n" +
    "predict_next -> " + (got < 0 ? "rejected" : got) + "\n" +
    "(a + b) mod 113 = " + want + "\n" +
    (got === want ? "exact" : "MISMATCH");
}

function clampInt(value, lo, hi) {
  const n = Math.round(parseFloat(value));
  if (!Number.isFinite(n)) return lo;
  return Math.max(lo, Math.min(hi, n));
}

/* The sweep worker: its own instance of the SAME wasm binary, its own copy of
 * the mod113 weights, a slice of a-rows. Returns wrong count and wall time. */
const WORKER_SRC = `
"use strict";
self.onmessage = async (ev) => {
  const { wasmUrl, weightsUrl, aStart, aEnd, id } = ev.data;
  try {
    const [wb, wts] = await Promise.all([
      fetch(wasmUrl).then((r) => r.arrayBuffer()),
      fetch(weightsUrl).then((r) => r.arrayBuffer()),
    ]);
    const { instance } = await WebAssembly.instantiate(wb);
    const e = instance.exports;
    new Uint8Array(e.memory.buffer, e.wasm_get_weight_buf_ptr(), wts.byteLength).set(new Uint8Array(wts));
    if (e.wasm_load_weights() !== 1) {
      self.postMessage({ id, error: "load_check failed in worker" });
      return;
    }
    const tokens = new Uint32Array(e.memory.buffer, e.wasm_get_tokens_buf_ptr(), 32);
    tokens[2] = 113;
    let wrong = 0;
    let count = 0;
    const t0 = performance.now();
    for (let a = aStart; a < aEnd; a++) {
      for (let b = 0; b < 113; b++) {
        tokens[0] = a;
        tokens[1] = b;
        if (e.wasm_predict_next(3) !== (a + b) % 113) wrong++;
        count++;
      }
    }
    self.postMessage({ id, done: true, wrong, count, ms: performance.now() - t0 });
  } catch (err) {
    self.postMessage({ id, error: String(err) });
  }
};
`;

async function verifyAll() {
  if (state.running || state.tab !== "mod113") return;
  state.running = true;
  const btn = $("m-verify-btn");
  btn.disabled = true;
  const out = $("m-verify-out");
  const bar = $("m-progress");
  bar.className = "progress";
  bar.style.width = "0%";
  out.textContent = "loading the module and weights into workers...";

  const wasmUrl = new URL("general_engine_wasm.wasm", location.href).href;
  const weightsUrl = new URL("../weights/mod113_v1.bin", location.href).href;
  const t0 = performance.now();
  let done = 0;
  let wrong = 0;
  const total = 12769;
  const activeWorkers = new Map();

  const finish = (workerCount, error) => {
    const secs = (performance.now() - t0) / 1000;
    bar.style.width = "100%";
    bar.className = "progress done";
    if (error || wrong > 0 || done !== total) {
      const failure = error || (done !== total ? done + " of 12,769 pairs checked" :
        wrong + " of 12,769 pairs wrong");
      out.textContent =
        "FAIL: " + failure + " after " + secs.toFixed(2) + " s";
    } else {
      out.textContent =
        "12,769 / 12,769 exact\n" +
        "every (a, b) pair: predict_next((a + b) mod 113), inside WebAssembly\n" +
        secs.toFixed(2) + " s wall, " + workerCount + " worker" + (workerCount === 1 ? "" : "s") +
        ", checked arithmetic on (" + (total / secs).toFixed(0) + " pairs/s)";
    }
    state.running = false;
    btn.disabled = false;
  };

  try {
    const workerCount = Math.min(navigator.hardwareConcurrency || 1, 2);
    // Split the 113 a-rows into chunks, 4 per worker for progress granularity.
    const chunkCount = workerCount * 4;
    const rows = [];
    for (let c = 0; c < chunkCount; c++) {
      const aStart = Math.floor((113 * c) / chunkCount);
      const aEnd = Math.floor((113 * (c + 1)) / chunkCount);
      if (aEnd > aStart) rows.push([aStart, aEnd]);
    }
    const chunks = rows.map(([aStart, aEnd], id) => ({ id, aStart, aEnd }));
    let nextChunk = 0;

    const runWorker = () =>
      new Promise((resolve, reject) => {
        let url;
        try {
          url = URL.createObjectURL(new Blob([WORKER_SRC], { type: "text/javascript" }));
          const worker = new Worker(url);
          activeWorkers.set(worker, url);
          const stop = () => {
            worker.terminate();
            URL.revokeObjectURL(url);
            activeWorkers.delete(worker);
          };
          const ask = () => {
            if (nextChunk < chunks.length) {
              const chunk = chunks[nextChunk++];
              worker.postMessage({ wasmUrl, weightsUrl, aStart: chunk.aStart, aEnd: chunk.aEnd, id: chunk.id });
            } else {
              stop();
              resolve();
            }
          };
          worker.onmessage = (ev) => {
            const m = ev.data;
            if (m.error) {
              stop();
              reject(new Error(m.error));
              return;
            }
            if (m.done) {
              wrong += m.wrong;
              done += m.count;
              bar.style.width = Math.min(100, (done / total) * 100).toFixed(1) + "%";
              out.textContent = done + " / 12,769 pairs checked...";
              ask();
            }
          };
          worker.onerror = (err) => {
            stop();
            reject(new Error("worker error: " + err.message));
          };
          ask();
        } catch (err) {
          if (url) URL.revokeObjectURL(url);
          reject(err);
        }
      });

    await Promise.all(Array.from({ length: Math.min(workerCount, chunks.length) }, runWorker));
    finish(workerCount, null);
  } catch (err) {
    for (const [worker, url] of activeWorkers) {
      worker.terminate();
      URL.revokeObjectURL(url);
    }
    activeWorkers.clear();
    // No workers (or a worker failed): verify on the main thread, no progress illusion.
    try {
      if (!loadWeights(state.mod113Bytes, $("m-load-badge"))) throw new Error("mod-113 weights rejected");
      wrong = 0;
      let count = 0;
      const t1 = performance.now();
      for (let a = 0; a < 113; a++) {
        for (let b = 0; b < 113; b++) {
          state.tokens[0] = a;
          state.tokens[1] = b;
          state.tokens[2] = 113;
          if (state.wasm.wasm_predict_next(3) !== (a + b) % 113) wrong++;
          count++;
        }
        bar.style.width = ((count / total) * 100).toFixed(1) + "%";
        out.textContent = count + " / 12,769 pairs checked (single thread)...";
        await sleepFrames();
      }
      out.textContent = (wrong === 0
        ? "12,769 / 12,769 exact\n"
        : "FAIL: " + wrong + " of 12,769 pairs wrong\n") +
        ((performance.now() - t1) / 1000).toFixed(2) + " s wall, 1 thread (workers unavailable: " + err.message + ")\n" +
        "inside WebAssembly, checked arithmetic on";
      bar.className = wrong === 0 ? "progress done" : "progress";
      state.running = false;
      btn.disabled = false;
    } catch (err2) {
      finish(0, String(err2));
    }
  }
}

/* -------------------------------------------------------------- wiring */

async function main() {
  try {
    await initWasm();
    const [bytelm, mod113] = await Promise.all([
      fetch("../weights/tiny_bytelm_v1.bin").then((r) => r.arrayBuffer()),
      fetch("../weights/mod113_v1.bin").then((r) => r.arrayBuffer()),
    ]);
    state.mod113Bytes = new Uint8Array(mod113);
    approveByteWeights(new Uint8Array(bytelm), "tiny_bytelm_v1.bin",
      "Trained byte model · GLMW v1 · 479,504 bytes");
  } catch (err) {
    $("engine-meta").textContent = "engine failed to load: " + err;
    return;
  }

  for (const btn of $("tabs").children) {
    btn.addEventListener("click", () => switchTab(btn.dataset.tab));
  }
  $("prompt").addEventListener("input", updatePromptMeta);
  updatePromptMeta();
  for (const chip of $("chips").children) {
    chip.addEventListener("click", () => {
      $("prompt").value = chip.dataset.p;
      updatePromptMeta();
    });
  }
  $("mode").addEventListener("change", () => {
    $("sample-row").classList.toggle("on", $("mode").value === "sample");
  });
  $("generate-btn").addEventListener("click", generate);
  $("stop-btn").addEventListener("click", () => { state.stopFlag = true; });
  $("corrupt-btn").addEventListener("click", corruptTest);
  $("restore-btn").addEventListener("click", restoreWeights);
  $("file-input").addEventListener("change", (ev) => {
    const file = ev.target.files?.[0];
    ev.target.value = "";
    if (file) return loadCustomFile(file);
  });
  $("m-predict-btn").addEventListener("click", predictPair);
  $("m-verify-btn").addEventListener("click", verifyAll);
}

main();
