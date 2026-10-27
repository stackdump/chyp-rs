// Smoke test for the wasm32 bundle (run with `make wasm-test`).
//
// For every fixture with upstream expectations it:
//   1. checks the theory step by step through `Session.step()` and compares
//      every part's (kind, line, name, status) with upstream Chyp's results
//      (tests/fixtures/expected/*.json);
//   2. compares the one-shot `check()` JSON (diagrams and layout included)
//      with the native CLI's `chyp-rs json FILE`, which must be identical:
//      the layout is deterministic across targets.
import { readFileSync, readdirSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { join, basename } from "node:path";
import { initSync, Session, check, upstream_commit } from "../pkg/chyp.js";

const root = new URL("..", import.meta.url).pathname;
initSync({ module: readFileSync(join(root, "pkg/chyp_bg.wasm")) });

const cli = join(root, "target/release/chyp-rs");
const dirs = ["tests/fixtures/upstream", "tests/fixtures/derived", "laws"];
const files = dirs.flatMap((d) =>
  readdirSync(join(root, d)).filter((f) => f.endsWith(".chyp")).map((f) => join(root, d, f)),
);

let failures = 0;
const fail = (msg) => {
  failures++;
  console.error("FAIL", msg);
};

if (upstream_commit() !== "3d28483") fail("upstream_commit");

for (const file of files) {
  const src = readFileSync(file, "utf8");
  const stem = basename(file, ".chyp");
  const expected = JSON.parse(readFileSync(join(root, "tests/fixtures/expected", stem + ".json"), "utf8"));

  // 1. Step by step.
  const s = new Session(src);
  const outline = JSON.parse(s.outline());
  if (outline.parts.length !== expected.parts.length) fail(`${stem}: ${outline.parts.length} parts`);
  if (outline.parts.some((p) => p.status !== "unchecked")) fail(`${stem}: parts checked before step()`);
  const stepped = [];
  let part;
  while ((part = JSON.parse(s.step())) !== null) {
    stepped.push(part);
    if (part.kind !== "GenPart" && part.kind !== "LetPart" && part.kind !== "RulePart" && part.kind !== "TheoremPart") {
      if (part.goals_after === undefined) fail(`${stem}: step ${part.index} has no goals_after`);
    }
  }
  if (!s.done()) fail(`${stem}: not done after stepping`);
  const after = JSON.parse(s.outline()).parts;
  expected.parts.forEach((e, i) => {
    const g = after[i];
    if (!g || g.kind !== e.kind || g.line !== e.line || g.name !== e.name || g.status !== e.status) {
      fail(`${stem}: part ${i}: got ${JSON.stringify(g && [g.kind, g.line, g.name, g.status])}, upstream ${JSON.stringify([e.kind, e.line, e.name, e.status])}`);
    }
  });
  if (stepped.length !== expected.parts.length) fail(`${stem}: stepped ${stepped.length} parts`);

  // 2. Native/wasm parity, including layout coordinates.
  // (The CLI exits 1 when a step is invalid; only its output matters here.)
  const run = spawnSync(cli, ["json", file], { encoding: "utf8", maxBuffer: 1 << 28 });
  if (run.status !== 0 && run.status !== 1) fail(`${stem}: chyp-rs json exited ${run.status}: ${run.stderr}`);
  const native = JSON.parse(run.stdout);
  const wasm = JSON.parse(check(src));
  if (JSON.stringify(native) !== JSON.stringify(wasm)) fail(`${stem}: wasm check() differs from native json`);

  const n = expected.parts.filter((p) => p.status === "valid").length;
  console.log(`ok ${stem}: ${stepped.length} parts, ${n} valid, matches upstream and native`);
}

// A rule's diagrams, and reset().
const s = new Session(readFileSync(join(root, "laws/sync_spiders.chyp"), "utf8"));
const rule = JSON.parse(s.rule("frob"));
const boxes = (d) => d.edges.filter((e) => !e.wire).map((e) => e.label).sort().join(",");
if (!rule || boxes(rule.lhs) !== "fork,join" || boxes(rule.rhs) !== "fork,join") fail("rule('frob')");
if (s.rule("nope") !== "null") fail("rule('nope')");
s.check_all();
s.reset();
if (s.position() !== 0 || s.done()) fail("reset()");

if (failures) {
  console.error(`${failures} failure(s)`);
  process.exit(1);
}
console.log(`wasm smoke test: ${files.length} files ok`);
