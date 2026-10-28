// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs.

// Smoke test for the WASI build of the CLI (run with `make wasi-test`).
//
// The module (target/wasm32-wasip1/wasm/chyp-rs.wasm) is run under node:wasi
// the way a host with no filesystem would run it: no preopened directories,
// the theory on stdin (`chyp-rs summary -`), output read from stdout. For every
// fixture with upstream expectations (not crash/, as in wasm_smoke.mjs) and
// every law, its stdout, stderr and exit status must be byte-identical to the
// native `target/release/chyp-rs summary FILE`; $CHYP_RS_STDIN_NAME makes `-`
// report the file's name. `check` and `json` are compared the same way.
// It also checks that the module imports nothing but WASI preview 1.
import { closeSync, mkdtempSync, openSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { WASI } from "node:wasi";

const root = new URL("..", import.meta.url).pathname;
const cli = join(root, "target/release/chyp-rs");
const wasmPath = join(root, "target/wasm32-wasip1/wasm/chyp-rs.wasm");
const dirs = ["tests/fixtures/upstream", "tests/fixtures/derived", "tests/fixtures/original", "laws"];
const files = dirs.flatMap((d) =>
  readdirSync(join(root, d))
    .filter((f) => f.endsWith(".chyp"))
    .map((f) => `${d}/${f}`),
);

// Fail loudly if the fixtures went missing rather than passing on zero files.
const MIN_FILES = 23;
if (files.length < MIN_FILES) {
  console.error(`FAIL only ${files.length} .chyp files found, expected at least ${MIN_FILES}`);
  process.exit(1);
}

let failures = 0;
const fail = (msg) => {
  failures++;
  console.error("FAIL", msg);
};

const module = new WebAssembly.Module(readFileSync(wasmPath));

// 1. The only imports are WASI preview 1 functions.
const imports = WebAssembly.Module.imports(module);
const foreign = imports.filter((i) => i.module !== "wasi_snapshot_preview1" || i.kind !== "function");
if (foreign.length) fail(`non-WASI imports: ${JSON.stringify(foreign)}`);
console.log(`ok imports: ${imports.length}, all wasi_snapshot_preview1 (${imports.map((i) => i.name).join(", ")})`);

const tmp = mkdtempSync(join(tmpdir(), "chyp-rs-wasi-"));
const nativeEnv = { ...process.env };
delete nativeEnv.CHYP_RS_STDIN_NAME;

// Run the module once with `input` (a path) as stdin; no directories are
// preopened, so it cannot read files itself.
function runWasi(args, input, env = {}) {
  const outPath = join(tmp, "stdout");
  const errPath = join(tmp, "stderr");
  const stdin = openSync(input, "r");
  const stdout = openSync(outPath, "w");
  const stderr = openSync(errPath, "w");
  let status;
  try {
    const wasi = new WASI({ version: "preview1", args: ["chyp-rs", ...args], env, stdin, stdout, stderr, returnOnExit: true });
    const instance = new WebAssembly.Instance(module, wasi.getImportObject());
    status = wasi.start(instance);
  } catch (e) {
    status = `trap: ${e}`;
  } finally {
    closeSync(stdin);
    closeSync(stdout);
    closeSync(stderr);
  }
  return { status, stdout: readFileSync(outPath), stderr: readFileSync(errPath) };
}

function runNative(args, input) {
  const r = spawnSync(cli, args, { cwd: root, env: nativeEnv, maxBuffer: 1 << 28, input: input === undefined ? undefined : readFileSync(input) });
  if (r.error) throw r.error;
  return { status: r.status, stdout: r.stdout, stderr: r.stderr };
}

function same(what, wasm, native) {
  for (const k of ["status", "stdout", "stderr"]) {
    const a = wasm[k];
    const b = native[k];
    const eq = Buffer.isBuffer(a) ? Buffer.compare(a, b) === 0 : a === b;
    if (!eq) {
      fail(`${what}: ${k} differs: wasi ${JSON.stringify(String(a).slice(0, 200))} vs native ${JSON.stringify(String(b).slice(0, 200))}`);
      return false;
    }
  }
  return true;
}

// 2. Every fixture and law: theory on stdin vs the native CLI on the file.
let compared = 0;
for (const file of files) {
  const path = join(root, file);
  const env = { CHYP_RS_STDIN_NAME: file };
  let ok = true;
  let summaryMs = 0;
  for (const cmd of ["summary", "check", "json"]) {
    const t0 = performance.now();
    const wasm = runWasi([cmd, "-"], path, env);
    const ms = Math.round(performance.now() - t0);
    const native = runNative([cmd, file]);
    if (native.status !== 0 && native.status !== 1) fail(`${file}: native ${cmd} exited ${native.status}`);
    ok = same(`${file} ${cmd}`, wasm, native) && ok;
    compared++;
    if (cmd === "summary") summaryMs = ms;
  }
  if (ok) {
    const parts = JSON.parse(runWasi(["summary", "-"], path, env).stdout.toString("utf8"))[0].parts.length;
    console.log(`ok ${file}: summary/check/json identical to native (${parts} parts, summary in ${summaryMs} ms)`);
  }
}

// 3. Without $CHYP_RS_STDIN_NAME, stdin is reported as `-`, as natively.
{
  const path = join(root, "laws/drivers.chyp");
  const wasm = runWasi(["summary", "-"], path);
  if (same("summary - (unnamed)", wasm, runNative(["summary", "-"], path))) {
    if (JSON.parse(wasm.stdout.toString("utf8"))[0].file !== "-") fail("unnamed stdin is not reported as `-`");
    else console.log("ok unnamed stdin reported as `-`");
  }
}

// 4. Error paths match the native CLI: invalid UTF-8, an empty theory, a
// syntax error, and the stack limits (nesting cap, a long chain).
const cases = {
  "invalid_utf8.chyp": Buffer.from("gen f : 1 -> 1\n\xff\n", "latin1"),
  "empty.chyp": Buffer.alloc(0),
  "syntax.chyp": Buffer.from("gen f : 1 -> 1\nrule r : f = (\n"),
  "nest500.chyp": Buffer.from(`gen f : 1 -> 1\nlet x = ${"(".repeat(500)}f${")".repeat(500)}\n`),
  "nest501.chyp": Buffer.from(`gen f : 1 -> 1\nlet x = ${"(".repeat(501)}f${")".repeat(501)}\n`),
  "chain20000.chyp": Buffer.from(`gen f : 1 -> 1\nrule ff : f ; f = f\nlet x = ${Array(20000).fill("f").join(" ; ")}\nrewrite r : f ; f ; f = f ; f by ff\n`),
};
for (const [name, bytes] of Object.entries(cases)) {
  const path = join(tmp, name);
  writeFileSync(path, bytes);
  let ok = true;
  for (const cmd of ["summary", "check"]) {
    ok = same(`${name} ${cmd}`, runWasi([cmd, "-"], path, { CHYP_RS_STDIN_NAME: path }), runNative([cmd, path])) && ok;
  }
  if (ok) console.log(`ok ${name}: identical to native`);
}

rmSync(tmp, { recursive: true, force: true });
if (failures) {
  console.error(`${failures} failure(s)`);
  process.exit(1);
}
console.log(`wasi smoke test: ${files.length} files, ${compared} runs identical to native`);
