// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

// Golden vectors and adversarial (malformed-input) vectors. The golden
// archive bytes are pinned in Tests/Vectors.lean too, and the differential
// suite keeps Lean and JS byte-identical — so these pins guard both.
import { test } from "node:test";
import assert from "node:assert/strict";
import { create, extract, inflate, deflate, gzip, gunzip, crc32, untar } from "../targz.mjs";

const enc = new TextEncoder();
const hex = (s) => Uint8Array.from(s.match(/../g), (b) => parseInt(b, 16));

/* ------------------------------- CRC-32 -------------------------------- */

test("crc32 known vectors", () => {
  assert.equal(crc32(new Uint8Array(0)), 0x00000000);
  assert.equal(crc32(enc.encode("a")), 0xe8b7be43);
  assert.equal(crc32(enc.encode("abc")), 0x352441c2);
  assert.equal(crc32(enc.encode("123456789")), 0xcbf43926);
  assert.equal(crc32(Uint8Array.from({ length: 256 }, (_, i) => i)), 0x29058c73);
});

/* --------------------------- Golden archive ----------------------------- */

// create([{name:"hello.txt", data:"hello world\n"}]) — pinned bytes.
// Also pinned in Tests/Vectors.lean; a drift in either implementation or in
// determinism (sort stability, tie-breaking, header fields) fails this.
const GOLDEN =
  "1f8b08000000000000ffedfd010480301045010c400000600020ff98000000000088221c" +
  "635d0a00000000000000000000000000000000d02d0c03688bb8630e3b77efde01c0b632" +
  "c7512e71fd021a53082e677d7506a8fce512072268b94747a6d2fad8654e8af47656bddc" +
  "17ec0d663cf7f7674cbc0c3f41364c336006cc80196860e006f25e992c00080000";

test("golden archive bytes are stable", () => {
  const archive = create([{ name: "hello.txt", data: enc.encode("hello world\n") }]);
  assert.equal(Buffer.from(archive).toString("hex"), GOLDEN);
});

test("golden archive extracts", () => {
  const entries = extract(hex(GOLDEN));
  assert.equal(entries.length, 1);
  assert.equal(entries[0].name, "hello.txt");
  assert.deepEqual(entries[0].data, enc.encode("hello world\n"));
});

/* ------------------------ Handcrafted DEFLATE --------------------------- */

// Local bit writer for crafting adversarial streams (LSB-first, like DEFLATE).
function craft() {
  const bits = [];
  return {
    le(v, n) {
      for (let i = 0; i < n; i++) {
        bits.push((v >>> i) & 1);
      }
    },
    msb(code, len) {
      for (let i = len - 1; i >= 0; i--) {
        bits.push((code >>> i) & 1);
      }
    },
    bytes() {
      const out = new Uint8Array(Math.ceil(bits.length / 8));
      bits.forEach((b, i) => {
        out[i >> 3] |= b << (i & 7);
      });
      return out;
    },
  };
}

test("stored block vector decodes", () => {
  // bfinal=1 btype=00, 5 pad bits, LEN=3, NLEN=~3, "abc"
  const r = inflate(new Uint8Array([0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63]));
  assert.notEqual(r, null);
  assert.deepEqual(r[0], enc.encode("abc"));
  assert.equal(r[1], 8);
});

test("malformed DEFLATE streams are rejected", () => {
  // reserved block type 11
  assert.equal(inflate(new Uint8Array([0x07])), null);
  // fixed block coding symbol 286 (undefined length symbol)
  assert.equal(inflate(new Uint8Array([0x1b, 0x03])), null);
  // truncated stored body
  assert.equal(inflate(new Uint8Array([0x01, 0x03, 0x00, 0xfc, 0xff, 0x61])), null);
  // NLEN not the complement of LEN
  assert.equal(inflate(new Uint8Array([0x01, 0x03, 0x00, 0xfc, 0xfe, 0x61, 0x62, 0x63])), null);
  // empty input
  assert.equal(inflate(new Uint8Array(0)), null);
});

test("fixed block with a too-far distance is rejected", () => {
  // bfinal=1 btype=01; lit 'a' (8-bit code 0x30+0x61); length sym 257 (7-bit
  // code 1 → len 3); dist sym 1 (5-bit code 1 → dist 2) — but only 1 byte of
  // output exists, so dist 2 must be refused.
  const w = craft();
  w.le(1, 1);
  w.le(1, 2);
  w.msb(0x30 + 0x61, 8);
  w.msb(1, 7);
  w.msb(1, 5);
  assert.equal(inflate(w.bytes()), null);
});

test("dynamic block starting with CL repeat symbol 16 is rejected", () => {
  // A valid CL code (16→1 bit, 17,18→2 bits) whose first decoded symbol is
  // 16 ("repeat previous") with nothing before it.
  const w = craft();
  w.le(1, 1); // bfinal
  w.le(2, 2); // btype=10
  w.le(0, 5); // HLIT
  w.le(0, 5); // HDIST
  w.le(15, 4); // HCLEN → all 19 CL lens follow
  w.le(1, 3); // len(16) = 1   (clOrder[0])
  w.le(2, 3); // len(17) = 2
  w.le(2, 3); // len(18) = 2
  for (let i = 3; i < 19; i++) {
    w.le(0, 3);
  }
  w.msb(0, 1); // CL symbol 16 — no previous length to repeat
  assert.equal(inflate(w.bytes()), null);
});

test("codeword walk that never hits a code is rejected", () => {
  // CL code with only two 2-bit codes (00, 01); feeding 1-bits never matches,
  // so the decoder walks to maxLen and gives up.
  const w = craft();
  w.le(1, 1);
  w.le(2, 2);
  w.le(0, 5);
  w.le(0, 5);
  w.le(15, 4);
  for (let p = 0; p < 19; p++) {
    w.le(p === 3 || p === 17 ? 2 : 0, 3); // clOrder[3] = sym 0, clOrder[17] = sym 1
  }
  w.le(0x7f, 7); // seven 1-bits: miss at every depth
  assert.equal(inflate(w.bytes()), null);
});

test("dynamic block using distance symbol 30 is rejected", () => {
  // HDIST = 31 declares 32 distance codes, so symbols 30/31 are decodable
  // but have no base-table entry (RFC 1951: "they will not occur").
  const w = craft();
  w.le(1, 1);
  w.le(2, 2);
  w.le(31, 5); // HLIT → 288 literal/length codes
  w.le(31, 5); // HDIST → 32 distance codes
  w.le(15, 4); // HCLEN → all 19 CL lens
  for (let p = 0; p < 19; p++) {
    // CL code: len(9) = 1 (clOrder[6]), len(5) = 1 (clOrder[9])
    w.le(p === 6 || p === 9 ? 1 : 0, 3);
  }
  for (let i = 0; i < 288; i++) {
    w.msb(1, 1); // CL symbol 9 → every literal/length code is 9 bits
  }
  for (let i = 0; i < 32; i++) {
    w.msb(0, 1); // CL symbol 5 → every distance code is 5 bits
  }
  w.msb(257, 9); // length symbol 257 (len 3, no extra bits)
  w.msb(30, 5); // distance symbol 30 — undefined
  assert.equal(inflate(w.bytes()), null);
});

test("far matches: window edge round trips", () => {
  // repeat at exactly the 32768 window bound (matchable) …
  let s = 0x2f00d;
  const rand = (n) =>
    Uint8Array.from({ length: n }, () => {
      s ^= s << 13;
      s ^= s >>> 17;
      s ^= s << 5;
      s >>>= 0;
      return s & 0xff;
    });
  const a = rand(32768);
  const atEdge = new Uint8Array([...a, ...a.subarray(0, 1000)]);
  const r1 = inflate(deflate(atEdge));
  assert.deepEqual(r1[0], atEdge);
  // … and just past it (not matchable; must still round trip as literals)
  const b = rand(33000);
  const pastEdge = new Uint8Array([...b, ...b.subarray(0, 1000)]);
  const r2 = inflate(deflate(pastEdge));
  assert.deepEqual(r2[0], pastEdge);
});

/* --------------------------- gzip container ----------------------------- */

test("gzip members with FCOMMENT and FHCRC header fields", async () => {
  const zlib = await import("node:zlib");
  const data = enc.encode("optional header fields");
  const raw = zlib.deflateRawSync(Buffer.from(data));
  const trailer = Buffer.alloc(8);
  trailer.writeUInt32LE(crc32(data), 0);
  trailer.writeUInt32LE(data.length % 2 ** 32, 4);
  // FLG = FCOMMENT(16): NUL-terminated comment after the base header
  const fcomment = Buffer.concat([
    Buffer.from([0x1f, 0x8b, 8, 16, 0, 0, 0, 0, 0, 255]),
    Buffer.from("a comment\0", "latin1"),
    raw,
    trailer,
  ]);
  assert.deepEqual(gunzip(new Uint8Array(fcomment)), data);
  // FLG = FHCRC(2): two header-CRC bytes (skipped, not verified)
  const fhcrc = Buffer.concat([
    Buffer.from([0x1f, 0x8b, 8, 2, 0, 0, 0, 0, 0, 255]),
    Buffer.from([0xab, 0xcd]),
    raw,
    trailer,
  ]);
  assert.deepEqual(gunzip(new Uint8Array(fhcrc)), data);
});

test("malformed gzip containers are rejected", () => {
  const good = gzip(enc.encode("x"));
  // too short / wrong magic / wrong method
  assert.equal(gunzip(new Uint8Array([0x1f, 0x8b, 8])), null);
  assert.equal(gunzip(Uint8Array.from(good, (b, i) => (i === 1 ? 0x8c : b))), null);
  assert.equal(gunzip(Uint8Array.from(good, (b, i) => (i === 2 ? 9 : b))), null);
  // ISIZE flipped
  assert.equal(gunzip(Uint8Array.from(good, (b, i) => (i === good.length - 1 ? b ^ 0xff : b))), null);
  // truncated trailer
  assert.equal(gunzip(good.subarray(0, good.length - 3)), null);
  // FEXTRA announcing more bytes than exist
  assert.equal(
    gunzip(new Uint8Array([0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 255, 0xff, 0x00, 1, 2])),
    null
  );
  // FNAME with no terminating NUL
  assert.equal(
    gunzip(new Uint8Array([0x1f, 0x8b, 8, 8, 0, 0, 0, 0, 0, 255, 0x61, 0x62])),
    null
  );
});

test("trailing bytes after a complete member are ignored", () => {
  const data = enc.encode("first member");
  const doubled = new Uint8Array([...gzip(data), ...gzip(enc.encode("second"))]);
  assert.deepEqual(gunzip(doubled), data);
});

/* ------------------------------- USTAR ---------------------------------- */

// Recompute a header's checksum in place (offsets 148..155: 6 octal digits,
// NUL, space) after test-side surgery.
function fixChecksum(tarBytes, headerOff) {
  let sum = 0;
  for (let i = 0; i < 512; i++) {
    sum += i >= 148 && i < 156 ? 0x20 : tarBytes[headerOff + i];
  }
  const digits = sum.toString(8).padStart(6, "0");
  for (let i = 0; i < 6; i++) {
    tarBytes[headerOff + 148 + i] = digits.charCodeAt(i);
  }
  tarBytes[headerOff + 154] = 0;
  tarBytes[headerOff + 155] = 0x20;
}

function payloadOf(entries) {
  return gunzip(create(entries));
}

test("tar checksum corruption is rejected", () => {
  const t = payloadOf([{ name: "f", data: enc.encode("data") }]).slice();
  t[0] ^= 0xff; // name byte changes, checksum now wrong
  assert.equal(untar(t), null);
});

test("tar truncated archive is rejected", () => {
  const t = payloadOf([{ name: "f", data: enc.encode("data") }]);
  assert.equal(untar(t.subarray(0, 700)), null);
  assert.equal(untar(new Uint8Array(100)), null);
});

test("non-file typeflags are skipped", () => {
  const t = payloadOf([
    { name: "adir", data: new Uint8Array(0) },
    { name: "kept.txt", data: enc.encode("kept") },
  ]).slice();
  t[156] = 0x35; // typeflag '5' (directory) on the first entry
  fixChecksum(t, 0);
  const es = untar(t);
  assert.notEqual(es, null);
  assert.equal(es.length, 1);
  assert.deepEqual(es[0].data, enc.encode("kept"));
});

test("ustar prefix field is joined onto the name", () => {
  const t = payloadOf([{ name: "leaf.txt", data: enc.encode("nested") }]).slice();
  const prefix = enc.encode("some/deep");
  t.set(prefix, 345);
  fixChecksum(t, 0);
  const es = untar(t);
  assert.equal(new TextDecoder().decode(es[0].name), "some/deep/leaf.txt");
});

test("octal fields tolerate leading spaces", () => {
  const t = payloadOf([{ name: "f", data: enc.encode("1234") }]).slice();
  // rewrite the 12-byte size field as "     4 \0…" style: spaces then digits
  const field = enc.encode("      4    ");
  t.set(field, 124);
  t[135] = 0;
  fixChecksum(t, 0);
  const es = untar(t);
  assert.notEqual(es, null);
  assert.deepEqual(es[0].data, enc.encode("1234"));
});

test("extract propagates tar-level failure", () => {
  const archive = create([{ name: "f", data: enc.encode("data") }]);
  const payload = gunzip(archive).slice();
  payload[156] = 0x37; // unknown typeflag → skipped → zero entries, still valid
  fixChecksum(payload, 0);
  assert.deepEqual(untar(payload), []);
});
