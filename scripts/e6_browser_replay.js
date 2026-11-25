#!/usr/bin/env node
"use strict";

// Private loopback replay. Requires an existing Chromium and Node (no packages).
// Browser, HTTP transport, and screenshots are independent of the Node Wasm receipt.
const assert = require("node:assert/strict");
const crypto = require("node:crypto");
const fs = require("node:fs");
const http = require("node:http");
const path = require("node:path");
const { spawn } = require("node:child_process");

const root = path.resolve(__dirname, "..");
const evidence = path.join(root, "evidence/e6-wasm");
const run = fs.mkdtempSync(path.join(evidence, "browser-run-"));
const report = { scope: "isolated Chromium against task-owned 127.0.0.1 HTTP",
  pass: false, started: new Date().toISOString(), checks: {}, requests: [], exceptions: [] };
const sha = (buf) => crypto.createHash("sha256").update(buf).digest("hex");
const save = () => fs.writeFileSync(path.join(run, "browser-ui-check.json"), JSON.stringify(report, null, 2) + "\n");
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const same = (a, b) => assert.deepEqual(a, b);
const required = [
  "web/general_engine_wasm.wasm", "weights/tiny_bytelm_v1.bin", "weights/mod113_v1.bin",
];
const mime = { ".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8", ".wasm": "application/wasm", ".bin": "application/octet-stream" };
let server;
let browser;
let cdp;

function limitedCpus() {
  const allowed = /^Cpus_allowed_list:\s*([^\n]+)/m.exec(fs.readFileSync("/proc/self/status", "utf8"));
  assert.ok(allowed, "could not determine process CPU affinity");
  const cpus = [];
  for (const range of allowed[1].trim().split(",")) {
    const [lo, hi = lo] = range.split("-").map(Number);
    for (let cpu = lo; cpu <= hi && cpus.length < 2; cpu++) cpus.push(cpu);
    if (cpus.length === 2) break;
  }
  assert.ok(cpus.length);
  return cpus.join(",");
}

function chromium() {
  const profile = path.join(run, "profile");
  fs.mkdirSync(profile);
  for (const dir of ["config", "cache", "tmp"]) fs.mkdirSync(path.join(run, dir));
  const cpus = limitedCpus();
  const binary = process.env.CHROMIUM || "/usr/bin/chromium";
  const args = ["-c", cpus, binary, "--headless", "--remote-debugging-pipe",
    "--disable-gpu", "--disable-background-networking", "--disable-component-update",
    "--disable-dev-shm-usage", "--disable-sync", "--no-first-run", "--no-default-browser-check",
    "--no-proxy-server", "--renderer-process-limit=1", "--window-size=1440,1050",
    "--user-data-dir=" + profile, "about:blank"];
  report.chromiumCommand = ["/usr/bin/taskset", ...args];
  browser = spawn("/usr/bin/taskset", args, {
    detached: true,
    env: { ...process.env, XDG_CONFIG_HOME: path.join(run, "config"),
      XDG_CACHE_HOME: path.join(run, "cache"), TMPDIR: path.join(run, "tmp") },
    stdio: ["ignore", "ignore", "pipe", "pipe", "pipe"],
  });
  const log = fs.createWriteStream(path.join(run, "chromium.stderr.log"));
  browser.stderr.pipe(log);
  let seq = 0;
  let unread = "";
  const pending = new Map();
  const fail = (reason) => {
    for (const f of pending.values()) { clearTimeout(f.timer); f.reject(reason); }
    pending.clear();
  };
  browser.on("error", fail);
  browser.on("exit", (code, signal) => {
    report.chromiumExit = { code, signal };
    fail(new Error(`Chromium exited: ${code ?? signal}`));
  });
  browser.stdio[3].on("error", fail);
  browser.stdio[4].on("error", fail);
  browser.stdio[4].setEncoding("utf8");
  browser.stdio[4].on("data", (data) => {
    unread += data;
    let end;
    while ((end = unread.indexOf("\0")) !== -1) {
      const message = JSON.parse(unread.slice(0, end));
      unread = unread.slice(end + 1);
      const next = pending.get(message.id);
      if (next) {
        clearTimeout(next.timer);
        pending.delete(message.id);
        if (message.error) next.reject(new Error(next.method + ": " + JSON.stringify(message.error)));
        else next.resolve(message.result);
      } else if (message.method === "Runtime.exceptionThrown") {
        report.exceptions.push(message.params.exceptionDetails);
      }
    }
  });
  return (method, params = {}, sessionId) => new Promise((resolve, reject) => {
    const id = ++seq;
    const timer = setTimeout(() => {
      pending.delete(id);
      reject(new Error("CDP deadline: " + method));
    }, 20000);
    pending.set(id, { resolve, reject, timer, method });
    browser.stdio[3].write(JSON.stringify({ id, method, params, sessionId }) + "\0");
  });
}

async function listen(assets, port = 0) {
  server = http.createServer((req, res) => {
    const route = new URL(req.url, "http://127.0.0.1").pathname;
    const file = assets.get(route);
    if (req.method !== "GET" || !file) {
      report.requests.push({ route, method: req.method, status: 404 });
      res.writeHead(404).end("File not in the private page");
      return;
    }
    res.once("finish", () => report.requests.push({ route, status: 200, sha256: file.sha256,
      bytes: file.data.length, user_agent: req.headers["user-agent"] || null }));
    res.writeHead(200, { "Content-Type": file.type, "Content-Length": file.data.length,
      "Cache-Control": "no-store", "X-Content-Type-Options": "nosniff" });
    res.end(file.data);
  });
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen({ host: "127.0.0.1", port }, resolve);
  });
  return "http://127.0.0.1:" + server.address().port;
}

const FETCH_DIGESTS = `
(() => {
  const original = globalThis.fetch.bind(globalThis);
  globalThis.__e6assetReads = [];
  globalThis.__e6sha = async (bytes) => {
    const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
    return Array.from(digest, (byte) => byte.toString(16).padStart(2, "0")).join("");
  };
  globalThis.fetch = async (...args) => {
    const response = await original(...args);
    const record = { path: new URL(response.url).pathname, status: response.status };
    globalThis.__e6assetReads.push(record);
    response.clone().arrayBuffer().then(async (data) => {
      record.sha256 = await globalThis.__e6sha(data);
      record.bytes = data.byteLength;
    }).catch((error) => { record.error = String(error); });
    return response;
  };
})();
`;

async function main() {
  save();
  const manifest = JSON.parse(fs.readFileSync(path.join(evidence, "build-manifest.json")));
  const nativePath = "evidence/e6-wasm/native-general.json";
  const nativeBytes = fs.readFileSync(path.join(root, nativePath));
  assert.equal(sha(nativeBytes), manifest.files[nativePath].sha256);
  const native = JSON.parse(nativeBytes);
  const acceptedNames = ["web/index.html", "web/app.js", "web/style.css", ...required];
  const assets = new Map(acceptedNames.map((relative) => {
    const data = fs.readFileSync(path.join(root, relative));
    const sha256 = sha(data);
    assert.equal(sha256, manifest.files[relative].sha256, relative);
    return ["/" + relative, { data, sha256, type: mime[path.extname(relative)] }];
  }));
  const serveOnly = process.argv[2] === "--serve";
  report.mode = serveOnly ? "serve-only" : "browser-replay";
  const port = serveOnly ? Number(process.argv[3] || 8765) : 0;
  if (!Number.isInteger(port) || port < 0 || port > 65535) throw new Error("Invalid loopback port");
  const origin = await listen(assets, port);
  report.origin = origin;
  console.log("Private page: " + origin + "/web/index.html");
  console.log("Evidence: " + run);
  if (serveOnly) {
    await new Promise((resolve) => { process.once("SIGINT", resolve); process.once("SIGTERM", resolve); });
    return;
  }

  cdp = chromium();
  report.browser = await cdp("Browser.getVersion");
  const { targetId } = await cdp("Target.createTarget", { url: "about:blank" });
  const { sessionId } = await cdp("Target.attachToTarget", { targetId, flatten: true });
  const send = (method, params) => cdp(method, params, sessionId);
  await send("Page.enable");
  await send("Runtime.enable");
  await send("DOM.enable");
  await send("Network.enable");
  await send("Network.setCacheDisabled", { cacheDisabled: true });
  await send("Page.addScriptToEvaluateOnNewDocument", { source: FETCH_DIGESTS });
  const evaluate = async (expression) => {
    const { result, exceptionDetails } = await send("Runtime.evaluate", { expression,
      awaitPromise: true, returnByValue: true });
    if (exceptionDetails) throw new Error(exceptionDetails.exception?.description || exceptionDetails.text);
    return result.value;
  };
  const waitFor = async (condition, budget = 20000) => {
    const deadline = performance.now() + budget;
    while (performance.now() < deadline) {
      try {
        if (await evaluate(condition)) return;
      } catch (error) {
        if (!/execution context was destroyed|cannot find (?:default )?context/i.test(error.message)) {
          throw error;
        }
      }
      await sleep(100);
    }
    throw new Error("Browser condition timed out: " + condition);
  };
  const text = (id) => evaluate(`document.getElementById(${JSON.stringify(id)}).textContent`);
  const click = (id) => evaluate(`document.getElementById(${JSON.stringify(id)}).click()`);
  const screenshot = async (name) => {
    const { data } = await send("Page.captureScreenshot", { format: "png", fromSurface: true });
    fs.writeFileSync(path.join(run, name + ".png"), Buffer.from(data, "base64"));
  };
  const stateSnapshot = () => evaluate(`(async () => ({
    selected: document.getElementById("weight-name").textContent,
    note: document.getElementById("weight-note").textContent,
    badge: document.getElementById("load-badge").textContent,
    disabled: document.getElementById("generate-btn").disabled,
    restoreVisible: !document.getElementById("restore-btn").classList.contains("hidden"),
    retainedSha256: await __e6sha(state.pristine),
    wasmPredict: state.wasm.wasm_predict_next(setTokens(new TextEncoder().encode(document.getElementById("prompt").value))),
    wasmLogits: state.wasm.wasm_forward_logits(setTokens(new TextEncoder().encode(document.getElementById("prompt").value))) !== 0
  }))()`);
  const upload = async (file) => {
    const { root: dom } = await send("DOM.getDocument");
    const { nodeId } = await send("DOM.querySelector", { nodeId: dom.nodeId, selector: "#file-input" });
    assert.ok(nodeId, "missing real file input");
    await send("DOM.setFileInputFiles", { nodeId, files: [file] });
  };
  const generate = async (steps) => {
    const started = performance.now();
    const prompt = native.bytelm.prompts[0];
    const result = await evaluate(`(async () => {
      const prompt = document.getElementById("prompt");
      prompt.value = ${JSON.stringify(prompt.prompt_utf8)};
      prompt.dispatchEvent(new Event("input", { bubbles: true }));
      const promptBytes = Array.from(new TextEncoder().encode(prompt.value));
      document.getElementById("mode").value = "greedy";
      document.getElementById("steps").value = "${steps}";
      document.getElementById("generate-btn").click();
      while (state.running) await new Promise((resolve) => setTimeout(resolve, 20));
      return { promptBytes, generated: genWindow.slice(promptBytes.length),
        text: document.getElementById("gen-part").textContent,
        stats: document.getElementById("gen-stats").textContent,
        rawLogits: Array.from(state.logits ?? [], (value) => value.toString()),
        displayedLogits: Array.from(document.querySelectorAll("#logit-body tr"), (row) =>
          [row.cells[1]?.textContent, row.cells[3]?.textContent])
      };
    })()`);
    result.wallMs = performance.now() - started;
    same(result.promptBytes, prompt.prompt_bytes);
    same(result.generated, prompt.tokens.slice(0, steps));
    return result;
  };

  await send("Page.navigate", { url: origin + "/web/index.html" });
  await waitFor(`document.querySelector("#load-badge")?.textContent.includes("PASS")`);
  await waitFor(`globalThis.__e6assetReads?.filter((r) => r.sha256).length === 3`);
  const received = await evaluate("__e6assetReads");
  for (const file of required) {
    const matches = received.filter((item) => item.path === "/" + file);
    same(matches.length, 1);
    same(matches[0].status, 200);
    same(matches[0].sha256, manifest.files[file].sha256);
  }
  report.checks.browserDeliveredAssets = received;
  const startup = await stateSnapshot();
  assert.match(startup.badge, /PASS/);
  assert.equal(startup.retainedSha256, manifest.files["weights/tiny_bytelm_v1.bin"].sha256);
  report.checks.startup = startup;
  const first = await generate(1);
  assert.ok(native.bytelm.prompt0_logits.every((v) => typeof v === "string" && /^-?\d+$/.test(v)));
  same(first.rawLogits.length, 256);
  same(first.rawLogits, native.bytelm.prompt0_logits);
  same(first.displayedLogits.length, 8);
  for (const [token, logit] of first.displayedLogits) same(logit, first.rawLogits[Number(token)]);
  report.checks.promptLogits = first;
  await screenshot("trained-logits");

  const approvedBytes = assets.get("/weights/tiny_bytelm_v1.bin").data;
  const approved = path.join(run, "approved-custom.bin");
  const broken = path.join(run, "qa-invalid.bin");
  const brokenBytes = Buffer.from(approvedBytes);
  brokenBytes[16] = 99;
  fs.writeFileSync(approved, approvedBytes);
  fs.writeFileSync(broken, brokenBytes);
  report.checks.uploadFixtures = { approvedSha256: sha(approvedBytes), rejectedSha256: sha(brokenBytes),
    changedOffset: 16, changedByte: 99 };
  const initialDocument = await evaluate("performance.timeOrigin");
  await upload(approved);
  await waitFor(`document.getElementById("weight-name").textContent === "approved-custom.bin" && !state.loadingCustom`);
  const custom = await stateSnapshot();
  assert.match(custom.badge, /PASS/);
  same(custom.retainedSha256, startup.retainedSha256);
  report.checks.customUpload = custom;
  const generated = await generate(4);
  report.checks.customGreedy = generated;

  await upload(broken);
  await waitFor(`document.getElementById("weight-note").textContent.includes("qa-invalid.bin rejected") && !state.loadingCustom`);
  const rejected = await stateSnapshot();
  report.checks.rejectedUpload = rejected;
  save();
  assert.match(rejected.badge, /FAIL/);
  same(rejected.disabled, true);
  same(rejected.restoreVisible, true);
  same(rejected.selected, "approved-custom.bin");
  same(rejected.retainedSha256, custom.retainedSha256);
  same(rejected.wasmPredict, -1);
  same(rejected.wasmLogits, false);
  await click("generate-btn");
  same(await text("gen-part"), "");
  await screenshot("rejected-upload");

  await click("restore-btn");
  const restored = await stateSnapshot();
  report.checks.restored = restored;
  same(await evaluate("performance.timeOrigin"), initialDocument);
  assert.match(restored.note, /restored/);
  assert.match(restored.badge, /PASS/);
  same(restored.selected, "approved-custom.bin");
  same(restored.retainedSha256, custom.retainedSha256);
  same(restored.wasmPredict, startup.wasmPredict);
  const replay = await generate(4);
  same(replay.generated, generated.generated);
  same(replay.rawLogits, generated.rawLogits);
  report.checks.deterministicReplay = replay;
  await screenshot("restored-generation");

  await evaluate('document.querySelector("[data-tab=mod113]").click()');
  await click("m-predict-btn");
  report.checks.mod113Pair = await text("m-predict-out");
  assert.match(report.checks.mod113Pair, /predict_next -> 77\n\(a \+ b\) mod 113 = 77\nexact$/);
  save();
  const sweepStart = performance.now();
  await click("m-verify-btn");
  await waitFor('!document.getElementById("m-verify-btn").disabled', 300000);
  const sweep = await text("m-verify-out");
  report.checks.mod113Sweep = { text: sweep, wallMs: performance.now() - sweepStart };
  assert.match(sweep, /^12,769 \/ 12,769 exact/);
  assert.match(sweep, /\b[12] (?:worker[s]?|thread)\b/);
  await screenshot("mod113-sweep");
  for (const file of required) {
    const served = report.requests.filter((r) => r.route === "/" + file && r.status === 200);
    assert.ok(served.length > 0, file);
    for (const request of served) same(request.sha256, manifest.files[file].sha256);
  }
  same(report.exceptions, []);
  report.pass = true;
}

async function cleanup() {
  if (browser && browser.exitCode === null && browser.signalCode === null) {
    const exited = new Promise((resolve) => browser.once("exit", resolve));
    await Promise.race([cdp("Browser.close").catch(() => {}), sleep(1200)]);
    if (browser.exitCode === null && browser.signalCode === null) {
      try { process.kill(-browser.pid, "SIGTERM"); } catch (error) { if (error.code !== "ESRCH") throw error; }
      await Promise.race([exited, sleep(1200)]);
    }
    if (browser.exitCode === null && browser.signalCode === null) {
      try { process.kill(-browser.pid, "SIGKILL"); } catch (error) { if (error.code !== "ESRCH") throw error; }
    }
  }
  if (server?.listening) {
    server.closeAllConnections();
    await new Promise((resolve) => server.close(resolve));
  }
}

main().catch((error) => {
  report.error = { message: error.message, code: error.code, stack: error.stack };
  console.error(error);
  process.exitCode = 1;
}).finally(async () => {
  try { await cleanup(); }
  catch (error) { report.cleanupError = String(error); report.pass = false; process.exitCode = 1; }
  report.finished = new Date().toISOString();
  save();
  console.log("Browser receipt: " + path.join(run, "browser-ui-check.json"));
});
