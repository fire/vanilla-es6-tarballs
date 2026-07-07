import { test } from "node:test";
import assert from "node:assert/strict";
import { create, extract, deflate, inflate, gzip, gunzip, crc32 } from "../targz.mjs";

// Deterministic xorshift32 PRNG — same constants as the Lean/browser tests.
function prng(seed) {
  let s = seed >>> 0;
  return () => {
    s ^= s << 13;
    s ^= s >>> 17;
    s ^= s << 5;
    s >>>= 0;
    return s & 0xff;
  };
}

function prngBytes(seed, n) {
  const g = prng(seed);
  return Uint8Array.from({ length: n }, () => g());
}

// Compressible corpus: random runs with repeats.
function compressible(seed, n) {
  const g = prng(seed);
  const out = [];
  while (out.length < n) {
    if (g() < 128 && out.length > 8) {
      const dist = 1 + (g() % Math.min(255, out.length));
      const len = 3 + (g() % 30);
      for (let i = 0; i < len && out.length < n; i++) {
        out.push(out[out.length - dist]);
      }
    } else out.push(g());
  }
  return Uint8Array.from(out);
}

test("crc32 check vector", () => {
  assert.equal(crc32(new TextEncoder().encode("123456789")), 0xcbf43926);
});

test("deflate/inflate round trips", () => {
  const cases = [
    new Uint8Array(0),
    new Uint8Array([42]),
    new Uint8Array(300).fill(7), // long run → overlapping copies
    prngBytes(1, 1000), // incompressible
    compressible(2, 5000),
    compressible(3, 70000), // > 65535 exercises stored chunking if fallback hits
    prngBytes(4, 66000),
  ];
  for (const data of cases) {
    const res = inflate(deflate(data));
    assert.notEqual(res, null);
    assert.deepEqual(res[0], data);
  }
});

test("gzip/gunzip round trips", () => {
  for (const data of [new Uint8Array(0), prngBytes(5, 2000), compressible(6, 20000)]) {
    assert.deepEqual(gunzip(gzip(data)), data);
  }
});

test("gunzip rejects corruption", () => {
  const g = gzip(compressible(7, 500));
  const bad = g.slice();
  bad[bad.length - 5] ^= 0xff; // flip a CRC byte
  assert.equal(gunzip(bad), null);
  const badMagic = g.slice();
  badMagic[0] = 0;
  assert.equal(gunzip(badMagic), null);
});

test("create/extract round trips", () => {
  const entries = [
    { name: "a.txt", data: new TextEncoder().encode("hello world\n") },
    { name: "dir/sub/data.bin", data: compressible(8, 10000) },
    { name: "x".repeat(100), data: new Uint8Array(0) }, // name length boundary
    { name: "rand.bin", data: prngBytes(9, 3000) },
  ];
  const back = extract(create(entries));
  assert.notEqual(back, null);
  assert.equal(back.length, entries.length);
  for (let i = 0; i < entries.length; i++) {
    assert.equal(back[i].name, entries[i].name);
    assert.deepEqual(back[i].data, entries[i].data);
  }
});

test("create([]) round trips", () => {
  assert.deepEqual(extract(create([])), []);
});

test("create rejects invalid names", () => {
  assert.throws(() => create([{ name: "y".repeat(101), data: new Uint8Array(1) }]));
  assert.throws(() => create([{ name: "", data: new Uint8Array(1) }]));
});
