// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

// node:zlib as an independent reference implementation (dev-only — never
// imported by targz.mjs itself).
import { test } from "node:test";
import assert from "node:assert/strict";
import zlib from "node:zlib";
import { gzip, gunzip } from "../targz.mjs";

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

const corpus = [
  new Uint8Array(0),
  new TextEncoder().encode("The quick brown fox jumps over the lazy dog. ".repeat(50)),
  prngBytes(11, 40000),
  new Uint8Array(100000).fill(65),
];

test("zlib gunzips our gzip", () => {
  for (const data of corpus) {
    assert.deepEqual(new Uint8Array(zlib.gunzipSync(Buffer.from(gzip(data)))), data);
  }
});

test("we gunzip zlib's gzip (dynamic/fixed blocks, default header)", () => {
  for (const data of corpus) {
    assert.deepEqual(gunzip(new Uint8Array(zlib.gzipSync(Buffer.from(data)))), data);
  }
});

test("we gunzip zlib level 0 (stored blocks)", () => {
  for (const data of corpus) {
    assert.deepEqual(
      gunzip(new Uint8Array(zlib.gzipSync(Buffer.from(data), { level: 0 }))),
      data
    );
  }
});

test("we gunzip gzip members with FNAME and FEXTRA header fields", () => {
  const data = new TextEncoder().encode("payload with a filename header");
  const raw = zlib.deflateRawSync(Buffer.from(data));
  const crc = zlib.crc32 ? zlib.crc32(data) : null; // node >= 22.2
  const crcv = crc === null ? 0 : crc >>> 0;
  const name = Buffer.from("file.txt\0", "latin1");
  const extra = Buffer.from([4, 0, 1, 2, 3, 4]); // XLEN=4 + 4 payload bytes
  const trailer = Buffer.alloc(8);
  trailer.writeUInt32LE(crcv, 0);
  trailer.writeUInt32LE(data.length % 2 ** 32, 4);
  // FLG = FEXTRA(4) | FNAME(8)
  const hdr = Buffer.from([0x1f, 0x8b, 8, 12, 0, 0, 0, 0, 0, 255]);
  const member = Buffer.concat([hdr, extra, name, raw, trailer]);
  if (crc === null) {
    // no zlib.crc32 on this Node: just check the parse fails on CRC (not header)
    assert.equal(gunzip(new Uint8Array(member)), null);
  } else {
    assert.deepEqual(gunzip(new Uint8Array(member)), data);
  }
});
