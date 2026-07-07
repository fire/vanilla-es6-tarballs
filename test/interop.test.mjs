// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

// Interop with the system tar (Windows ships bsdtar as tar.exe).
import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { create, extract } from "../targz.mjs";

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
  "we read system tar default format (pax headers are skipped)",
  { skip: TAR === null && "no tar.exe" },
  () => {
    const src = path.join(tmp, "src2");
    fs.mkdirSync(src, { recursive: true });
    const payload = Uint8Array.from({ length: 700 }, (_, i) => (i * 37) % 256);
    fs.writeFileSync(path.join(src, "f2.bin"), payload);
    const archive = path.join(tmp, "theirs-default.tgz");
    execFileSync(TAR, ["-czf", archive, "-C", src, "f2.bin"]);

    const entries = extract(new Uint8Array(fs.readFileSync(archive)));
    assert.notEqual(entries, null);
    const f2 = entries.find((e) => e.name.endsWith("f2.bin"));
    assert.ok(f2);
    assert.deepEqual(f2.data, payload);
  }
);
