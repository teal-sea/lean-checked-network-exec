#!/usr/bin/env node
"use strict";

// Exercises the real app.js event handlers and Wasm in a minimal Node DOM fixture.
// Browser transport and UI rendering are covered separately by e6_browser_replay.js.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const crypto = require("node:crypto");

const root = path.resolve(__dirname, "..");
const ev = path.join(root, "evidence/e6-wasm");
const before = process.argv[2] === "before";
const html = fs.readFileSync(path.join(root, before ? "evidence/e6-wasm/upload-before.index.html.txt" : "web/index.html"), "utf8");
const approved = fs.readFileSync(path.join(root, "weights/tiny_bytelm_v1.bin"));
const invalid = Buffer.from(approved);
invalid[16] = 99;
const assets = {
  "general_engine_wasm.wasm": ["web/general_engine_wasm.wasm", "application/wasm"],
  "../weights/tiny_bytelm_v1.bin": ["weights/tiny_bytelm_v1.bin", "application/octet-stream"],
  "../weights/mod113_v1.bin": ["weights/mod113_v1.bin", "application/octet-stream"],
};
const digest = (bytes) => crypto.createHash("sha256").update(bytes).digest("hex");
const log = { mode: before ? "before" : "after", environment: "Node DOM fixture with real Wasm",
  approved_sha256: digest(approved), rejected_sha256: digest(invalid), events: [] };
const nodes = new Map();
function element() {
  const listeners = new Map();
  const attributes = new Set();
  return {
    textContent: "", className: "", children: [], dataset: {}, style: {}, value: "", disabled: false,
    classList: {
      add: (s) => attributes.add(s), remove: (s) => attributes.delete(s),
      contains: (s) => attributes.has(s),
      toggle: (s, on) => on ? attributes.add(s) : attributes.delete(s),
    },
    addEventListener: (kind, fn) => listeners.set(kind, fn),
    async fire(kind) { return listeners.get(kind)?.({ target: this }); },
    appendChild(child) { this.children.push(child); },
    replaceChildren(...children) { this.children = children; },
    set innerHTML(value) { assert.equal(value, ""); this.children = []; },
  };
}
const document = {
  getElementById(id) {
    if (!nodes.has(id)) {
      assert.match(html, new RegExp('id="' + id + '"'));
      nodes.set(id, element());
    }
    return nodes.get(id);
  },
  createElement: element,
};
const get = (id) => document.getElementById(id);
get("restore-btn").classList.add("hidden");
get("prompt").value = "A stitch in time";
get("steps").value = "4";
get("mode").value = "greedy";
const context = vm.createContext({ document, TextEncoder, TextDecoder, WebAssembly, setTimeout, performance,
  fetch: async (url) => {
    const [file, type] = assets[url];
    return new Response(fs.readFileSync(path.join(root, file)), { headers: { "Content-Type": type } });
  } });
const evaluate = (code) => vm.runInContext(code, context);

async function snapshot(label) {
  const result = {
    label, badge: get("load-badge").textContent, note: get("weight-note").textContent,
    name: get("weight-name").textContent, generateDisabled: get("generate-btn").disabled,
    restoreVisible: !get("restore-btn").classList.contains("hidden"),
    stats: get("gen-stats").textContent, generated: get("gen-part").textContent,
    retainedSha256: digest(evaluate("state.pristine")),
    wasmPredict: evaluate('state.wasm.wasm_predict_next(setTokens(new TextEncoder().encode(document.getElementById("prompt").value)))'),
    wasmLogitsAccepted: evaluate('state.wasm.wasm_forward_logits(setTokens(new TextEncoder().encode(document.getElementById("prompt").value))) !== 0'),
  };
  log.events.push(result);
  return result;
}

async function upload(name, data) {
  const input = get("file-input");
  input.files = [{ name, arrayBuffer: async () => Uint8Array.from(data).buffer }];
  await input.fire("change");
  await new Promise((resolve) => setTimeout(resolve, 0));
}

async function main() {
  await evaluate(fs.readFileSync(path.join(root, before ? "evidence/e6-wasm/upload-before.app.js.txt" : "web/app.js"), "utf8"));
  const startup = await snapshot("trained startup weights");
  assert.match(startup.badge, /PASS/);
  assert.equal(startup.retainedSha256, log.approved_sha256);
  await upload("approved-custom.bin", approved);
  assert.match(get("load-badge").textContent, /PASS/);
  await get("generate-btn").fire("click");
  const original = await snapshot("valid custom upload and generation");
  assert.match(original.stats, /4 tokens/);
  await upload("qa-invalid.bin", invalid);
  const rejected = await snapshot("actual file-input handler rejected out-of-range payload");
  assert.match(rejected.badge, /FAIL/);
  assert.equal(rejected.wasmPredict, -1);
  assert.equal(rejected.wasmLogitsAccepted, false);
  if (!rejected.generateDisabled) await get("generate-btn").fire("click");
  await snapshot("generation attempted after rejection");
  assert.equal(rejected.retainedSha256, log.approved_sha256, "rejection must retain the last approved bytes");
  assert.equal(rejected.generateDisabled, true, "generation must stay blocked until explicit restoration");
  assert.equal(rejected.restoreVisible, true, "explicit restore must be available");
  await get("restore-btn").fire("click");
  const restored = await snapshot("explicit restore without reload");
  assert.match(restored.badge, /PASS/);
  assert.equal(restored.retainedSha256, log.approved_sha256);
  assert.equal(restored.name, "approved-custom.bin");
  await get("generate-btn").fire("click");
  const regenerated = await snapshot("generation after restore");
  assert.match(regenerated.stats, /4 tokens/);
  assert.equal(regenerated.generated, original.generated);
  evaluate('switchTab("mod113")');
  get("m-a").value = "21";
  get("m-b").value = "56";
  await get("m-predict-btn").fire("click");
  log.mod113Ui = get("m-predict-out").textContent;
  assert.match(log.mod113Ui, /predict_next -> 77\n\(a \+ b\) mod 113 = 77\nexact$/);
  evaluate('switchTab("bytelm")');
  const returned = await snapshot("return to approved byte weights after mod-113");
  assert.equal(returned.name, "approved-custom.bin");
  assert.equal(returned.retainedSha256, log.approved_sha256);
  assert.equal(returned.wasmPredict, startup.wasmPredict);
  log.pass = true;
}

main().catch((err) => {
  log.pass = false;
  log.error = err.stack;
  process.exitCode = 1;
}).finally(() => {
  fs.writeFileSync(path.join(ev, "upload-regression-" + (before ? "before" : "after") + ".json"),
    JSON.stringify(log, null, 2) + "\n");
  console.log(JSON.stringify(log, null, 2));
});
