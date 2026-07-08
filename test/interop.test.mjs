// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

// Interop with the system tar (Windows ships bsdtar as tar.exe).
import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { fileURLToPath } from "node:url";
import { create, extract } from "../targz.mjs";

const JS_CLI = fileURLToPath(new URL("../targz.mjs", import.meta.url));

function findTar() {
  for (const c of ["C:\\Windows\\System32\\tar.exe", "tar"]) {
    try {
      execFileSync(c, ["--version"], { stdio: "pipe" });
      return c;
    } catch {
      /* keep looking */
    }
  }
  return null;
}

const TAR = findTar();
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "targz-interop-"));

test("system tar reads our archive", { skip: TAR === null && "no tar.exe" }, () => {
  const entries = [
    { name: "hello.txt", data: new TextEncoder().encode("hello interop\n") },
    { name: "sub/dir/data.bin", data: Uint8Array.from({ length: 5000 }, (_, i) => i % 251) },
  ];
  const archive = path.join(tmp, "ours.tgz");
  fs.writeFileSync(archive, create(entries));

  const listing = execFileSync(TAR, ["-tzf", archive], { encoding: "utf8" });
  assert.match(listing, /hello\.txt/);
  assert.match(listing, /sub\/dir\/data\.bin/);

  const dest = path.join(tmp, "sys-extract");
  fs.mkdirSync(dest, { recursive: true });
  execFileSync(TAR, ["-xzf", archive, "-C", dest]);
  assert.deepEqual(
    new Uint8Array(fs.readFileSync(path.join(dest, "hello.txt"))),
    entries[0].data
  );
  assert.deepEqual(
    new Uint8Array(fs.readFileSync(path.join(dest, "sub", "dir", "data.bin"))),
    entries[1].data
  );
});

test("we read system tar archives (ustar)", { skip: TAR === null && "no tar.exe" }, () => {
  const src = path.join(tmp, "src");
  fs.mkdirSync(src, { recursive: true });
  const payload = new TextEncoder().encode("made by bsdtar\n".repeat(100));
  fs.writeFileSync(path.join(src, "f1.txt"), payload);
  const archive = path.join(tmp, "theirs-ustar.tgz");
  execFileSync(TAR, ["-czf", archive, "--format=ustar", "-C", src, "f1.txt"]);

  const entries = extract(new Uint8Array(fs.readFileSync(archive)));
  assert.notEqual(entries, null);
  const f1 = entries.find((e) => e.name.endsWith("f1.txt"));
  assert.ok(f1);
  assert.deepEqual(f1.data, payload);
});

test(
  "we read bsdtar ustar archives with prefix-split long paths",
  { skip: TAR === null && "no tar.exe" },
  () => {
    const src = path.join(tmp, "src-long");
    const deep = "level1-abcdefghij/level2-abcdefghij/level3-abcdefghij/level4-abcdefghij/level5-abcdefghij";
    fs.mkdirSync(path.join(src, ...deep.split("/")), { recursive: true });
    const payload = new TextEncoder().encode("deep file\n");
    const rel = `${deep}/leaf-file-with-a-rather-long-name.txt`; // > 100 chars total
    fs.writeFileSync(path.join(src, ...rel.split("/")), payload);
    const archive = path.join(tmp, "theirs-long.tgz");
    execFileSync(TAR, ["-czf", archive, "--format=ustar", "-C", src, rel]);

    const entries = extract(new Uint8Array(fs.readFileSync(archive)));
    assert.notEqual(entries, null);
    const leaf = entries.find((e) => e.name === rel);
    assert.ok(leaf, `expected joined prefix name ${rel}, got ${entries.map((e) => e.name)}`);
    assert.deepEqual(leaf.data, payload);
  }
);

test(
  "we read system tar default format (pax), incl. mtime metadata",
  { skip: TAR === null && "no tar.exe" },
  () => {
    const src = path.join(tmp, "src2");
    fs.mkdirSync(src, { recursive: true });
    const payload = Uint8Array.from({ length: 700 }, (_, i) => (i * 37) % 256);
    fs.writeFileSync(path.join(src, "f2.bin"), payload);
    const stamp = 1500000000;
    fs.utimesSync(path.join(src, "f2.bin"), stamp, stamp);
    const archive = path.join(tmp, "theirs-default.tgz");
    execFileSync(TAR, ["-czf", archive, "-C", src, "f2.bin"]);

    const entries = extract(new Uint8Array(fs.readFileSync(archive)));
    assert.notEqual(entries, null);
    const f2 = entries.find((e) => e.name.endsWith("f2.bin"));
    assert.ok(f2);
    assert.deepEqual(f2.data, payload);
    assert.equal(f2.mtime, stamp);
  }
);

test(
  "we read pax long names (> 255 chars) from system tar",
  { skip: TAR === null && "no tar.exe" },
  () => {
    const src = path.join(tmp, "src-pax-long");
    const seg = "a-directory-segment-of-considerable-length";
    const deep = Array.from({ length: 6 }, (_, i) => `${seg}-${i}`).join("/");
    fs.mkdirSync(path.join(src, ...deep.split("/")), { recursive: true });
    const rel = `${deep}/leaf.txt`; // ~270 chars: needs pax, not just prefix
    const payload = new TextEncoder().encode("very deep\n");
    fs.writeFileSync(path.join(src, ...rel.split("/")), payload);
    const archive = path.join(tmp, "theirs-pax-long.tgz");
    execFileSync(TAR, ["-czf", archive, "-C", src, rel]);

    const entries = extract(new Uint8Array(fs.readFileSync(archive)));
    assert.notEqual(entries, null);
    const leaf = entries.find((e) => e.name === rel);
    assert.ok(leaf, `pax path not reconstructed; got ${entries.map((e) => e.name)}`);
    assert.deepEqual(leaf.data, payload);
  }
);

test(
  "round trip through the CLI preserves directories and mtimes",
  { skip: TAR === null && "no tar.exe" },
  () => {
    const src = path.join(tmp, "src-meta");
    fs.mkdirSync(path.join(src, "sub"), { recursive: true });
    fs.writeFileSync(path.join(src, "sub", "f.txt"), "meta");
    const stamp = 1600000000;
    fs.utimesSync(path.join(src, "sub", "f.txt"), stamp, stamp);
    const archive = path.join(tmp, "cli-meta.tgz");
    execFileSync(process.execPath, [JS_CLI, "c", archive, "sub"], { cwd: src });
    const dest = path.join(tmp, "cli-meta-x");
    fs.mkdirSync(dest, { recursive: true });
    execFileSync(process.execPath, [JS_CLI, "x", archive, "-C", dest]);
    const st = fs.statSync(path.join(dest, "sub", "f.txt"));
    assert.equal(Math.floor(st.mtimeMs / 1000), stamp);
    assert.ok(fs.statSync(path.join(dest, "sub")).isDirectory());
    // and bsdtar agrees about the layout
    const listing = execFileSync(TAR, ["-tzf", archive], { encoding: "utf8" });
    assert.match(listing, /sub\//);
    assert.match(listing, /sub\/f\.txt/);
  }
);
