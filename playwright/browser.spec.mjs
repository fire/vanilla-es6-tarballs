// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

// The vanilla ES6 core must run unchanged in a real browser: this suite
// imports /targz.mjs as an ES module in Chromium and runs the round trips
// in-page (pure Uint8Array code, zero imports — the Node CLI block is inert).
import { test, expect } from "@playwright/test";

async function runInPage(page, fn) {
  await page.goto("/");
  return page.evaluate(fn);
}

test("module imports cleanly in the browser", async ({ page }) => {
  const keys = await runInPage(page, async () => {
    const m = await import("/targz.mjs");
    return Object.keys(m).sort();
  });
  expect(keys).toEqual(
    ["VERSION", "crc32", "create", "deflate", "extract", "gunzip", "gzip", "inflate", "tar", "untar"].sort()
  );
});

test("crc32 check vector in-browser", async ({ page }) => {
  const v = await runInPage(page, async () => {
    const m = await import("/targz.mjs");
    return m.crc32(new TextEncoder().encode("123456789"));
  });
  expect(v).toBe(0xcbf43926);
});

test("deflate/inflate and gzip/gunzip round trips in-browser", async ({ page }) => {
  const ok = await runInPage(page, async () => {
    const m = await import("/targz.mjs");
    // same xorshift32 corpus as the Node tests
    const prngBytes = (seed, n) => {
      let s = seed >>> 0;
      return Uint8Array.from({ length: n }, () => {
        s ^= s << 13;
        s ^= s >>> 17;
        s ^= s << 5;
        s >>>= 0;
        return s & 0xff;
      });
    };
    const eq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
    const cases = [
      new Uint8Array(0),
      new TextEncoder().encode("browser browser browser round trip ".repeat(40)),
      prngBytes(21, 20000),
      new Uint8Array(300).fill(7),
    ];
    for (const data of cases) {
      const r = m.inflate(m.deflate(data));
      if (r === null || !eq(r[0], data)) return `inflate failed at ${data.length}`;
      const g = m.gunzip(m.gzip(data));
      if (g === null || !eq(g, data)) return `gunzip failed at ${data.length}`;
    }
    return "ok";
  });
  expect(ok).toBe("ok");
});

test("create/extract round trip in-browser", async ({ page }) => {
  const result = await runInPage(page, async () => {
    const m = await import("/targz.mjs");
    const enc = new TextEncoder();
    const entries = [
      { name: "docs/readme.txt", data: enc.encode("tarballs in the browser\n") },
      { name: "bin/data", data: Uint8Array.from({ length: 5000 }, (_, i) => (i * 7) % 256) },
    ];
    const back = m.extract(m.create(entries));
    if (back === null) return "extract returned null";
    if (back.length !== 2) return `expected 2 entries, got ${back.length}`;
    const eq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
    if (back[0].name !== "docs/readme.txt" || !eq(back[0].data, entries[0].data)) {
      return "entry 0 mismatch";
    }
    if (back[1].name !== "bin/data" || !eq(back[1].data, entries[1].data)) {
      return "entry 1 mismatch";
    }
    return "ok";
  });
  expect(result).toBe("ok");
});

test("corrupted archives are rejected in-browser", async ({ page }) => {
  const ok = await runInPage(page, async () => {
    const m = await import("/targz.mjs");
    const g = m.create([{ name: "f", data: new TextEncoder().encode("x".repeat(100)) }]);
    const bad = g.slice();
    bad[bad.length - 5] ^= 0xff;
    return m.extract(bad) === null;
  });
  expect(ok).toBe(true);
});
