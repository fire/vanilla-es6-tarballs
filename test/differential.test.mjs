// Byte-identical differential test: the Lean CLI (verified model) and the
// ES6 program must produce EXACTLY the same archives, and each must extract
// the other's output.
import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { fileURLToPath } from "node:url";

const repo = path.dirname(fileURLToPath(import.meta.url)).replace(/test$/, "");
const LEAN_EXE = path.join(repo, ".lake", "build", "bin", "targz.exe");
const JS = path.join(repo, "targz.mjs");
const haveLean = fs.existsSync(LEAN_EXE);

function prngBytes(seed, n) {
  let s = seed >>> 0;
  return Uint8Array.from({ length: n }, () => {
    s ^= s << 13;
    s ^= s >>> 17;
    s ^= s << 5;
    s >>>= 0;
    return s & 0xff;
  });
}

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "targz-diff-"));

test("Lean and JS produce byte-identical archives", { skip: !haveLean && "lake exe targz not built" }, () => {
  const dir = path.join(tmp, "in");
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, "text.txt"),
    "differential testing is the best testing. ".repeat(200));
  fs.writeFileSync(path.join(dir, "rand.bin"), prngBytes(42, 8000));
  fs.writeFileSync(path.join(dir, "runs.bin"), new Uint8Array(4096).fill(9));
  fs.writeFileSync(path.join(dir, "empty.bin"), new Uint8Array(0));

  const files = ["text.txt", "rand.bin", "runs.bin", "empty.bin"];
  const leanOut = path.join(tmp, "lean.tgz");
  const jsOut = path.join(tmp, "js.tgz");
  execFileSync(LEAN_EXE, ["c", leanOut, ...files], { cwd: dir });
  execFileSync(process.execPath, [JS, "c", jsOut, ...files], { cwd: dir });

  const a = fs.readFileSync(leanOut);
  const b = fs.readFileSync(jsOut);
  assert.equal(a.length, b.length, "archive sizes differ");
  assert.ok(a.equals(b), "archives are not byte-identical");
});

test("cross extraction (Lean archive → JS extract and vice versa)", { skip: !haveLean && "lake exe targz not built" }, () => {
  const dir = path.join(tmp, "in2");
  fs.mkdirSync(dir, { recursive: true });
  const payload = prngBytes(7, 5000);
  fs.writeFileSync(path.join(dir, "x.bin"), payload);

  const leanOut = path.join(tmp, "lean2.tgz");
  execFileSync(LEAN_EXE, ["c", leanOut, "x.bin"], { cwd: dir });
  const jsDest = path.join(tmp, "js-x");
  fs.mkdirSync(jsDest, { recursive: true });
  execFileSync(process.execPath, [JS, "x", leanOut, "-C", jsDest]);
  assert.deepEqual(new Uint8Array(fs.readFileSync(path.join(jsDest, "x.bin"))), payload);

  const jsOut = path.join(tmp, "js2.tgz");
  execFileSync(process.execPath, [JS, "c", jsOut, "x.bin"], { cwd: dir });
  const leanDest = path.join(tmp, "lean-x");
  fs.mkdirSync(leanDest, { recursive: true });
  execFileSync(LEAN_EXE, ["x", jsOut, "-C", leanDest]);
  assert.deepEqual(new Uint8Array(fs.readFileSync(path.join(leanDest, "x.bin"))), payload);
});
