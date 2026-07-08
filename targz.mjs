// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

/*
 * targz.mjs — dependency-free tar + gzip (dynamic-Huffman DEFLATE) in one ES6 file.
 *
 * Line-by-line transcription of the Lean 4 model in TarGz/ (proved there:
 * `extract (create files) = some files`, `inflate ∘ deflate = id`,
 * `gunzip ∘ gzip = id`, `untar ∘ tar = id`, `crc32 = crc32Spec`). Each section
 * names the Lean definitions it mirrors. Documented divergences — a bit
 * accumulator instead of `List Bool`, typed arrays / Maps instead of lists —
 * are enforced by byte-identical differential tests against `lake exe targz`.
 *
 * The core is pure Uint8Array code with zero imports — it runs in a browser.
 * The CLI at the bottom activates only under Node and loads node:fs lazily.
 *
 *   node targz.mjs c out.tar.gz <files...>   create
 *   node targz.mjs x archive.tar.gz [-C dir] extract
 *   node targz.mjs t archive.tar.gz          list
 */

/* ============================ CRC-32 =====================================
 * Lean: TarGz.Crc32 (crcTable, crc32Update, crc32; proved = bit-serial spec)
 */

const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let i = 0; i < 256; i++) {
    let c = i;
    for (let k = 0; k < 8; k++) {c = c & 1 ? (c >>> 1) ^ 0xedb88320 : c >>> 1;}
    t[i] = c >>> 0;
  }
  return t;
})();

// Lean: TarGz.crc32
export function crc32(bytes) {
  let c = 0xffffffff;
  for (let i = 0; i < bytes.length; i++) {
    c = ((c >>> 8) ^ CRC_TABLE[(c ^ bytes[i]) & 0xff]) >>> 0;
  }
  return (c ^ 0xffffffff) >>> 0;
}

/* ============================ Bit streams ================================
 * Lean: TarGz.Bits models bits as `List Bool` (LSB-first per byte).
 * Divergence: accumulator writer / positional reader (differential-tested).
 */

function bitWriter() {
  return { bytes: [], buf: 0, cnt: 0 };
}

// Lean: natBitsLE n over the stream — v's low n bits, LSB first
function writeBits(w, v, n) {
  for (let i = 0; i < n; i++) {
    w.buf |= ((v >>> i) & 1) << w.cnt;
    if (++w.cnt === 8) {
      w.bytes.push(w.buf);
      w.buf = 0;
      w.cnt = 0;
    }
  }
}

// Lean: msbBits len code — codeword bits, MSB first
function writeBitsMSB(w, code, len) {
  for (let i = len - 1; i >= 0; i--) {
    w.buf |= ((code >>> i) & 1) << w.cnt;
    if (++w.cnt === 8) {
      w.bytes.push(w.buf);
      w.buf = 0;
      w.cnt = 0;
    }
  }
}

// Lean: bitsToBytes — zero-pad the final partial byte
function finishBits(w) {
  if (w.cnt > 0) {
    w.bytes.push(w.buf);
    w.buf = 0;
    w.cnt = 0;
  }
  return Uint8Array.from(w.bytes);
}

function bitReader(bytes) {
  return { bytes, pos: 0, len: bytes.length * 8 };
}

// Lean: readBitsLE — null when the stream is exhausted
function readBits(r, n) {
  if (r.pos + n > r.len) {return null;}
  let v = 0;
  for (let i = 0; i < n; i++) {
    v += ((r.bytes[r.pos >>> 3] >>> (r.pos & 7)) & 1) * 2 ** i;
    r.pos++;
  }
  return v;
}

/* ============================ Canonical Huffman ==========================
 * Lean: TarGz.Huffman (canonicalCodes, encodeSym, decodeSym; the round trip
 * decodeSym_encodeSym is proved for any PrefixFree assignment).
 */

// Lean: TarGz.canonicalCodes — positional [len, code] per symbol
function canonicalCodes(maxLen, lens) {
  const used = [];
  for (let i = 0; i < lens.length; i++) {if (lens[i] !== 0) {used.push([lens[i], i]);}}
  used.sort((a, b) => a[0] - b[0]); // stable sort by length (ES2019)
  const codes = lens.map(() => [0, 0]);
  let start = 0;
  for (const [l, i] of used) {
    codes[i] = [l, Math.floor(start / 2 ** (maxLen - l))];
    start += 2 ** (maxLen - l);
  }
  return codes;
}

// Lean: TarGz.encodeSym (unknown/unused symbols emit nothing)
function encodeSym(w, codes, s) {
  if (s < codes.length && codes[s][0] !== 0) {writeBitsMSB(w, codes[s][1], codes[s][0]);}
}

// Lean: TarGz.findSym as a (len<<16|code) → first-symbol table
function decodeTable(codes) {
  const m = new Map();
  for (let s = 0; s < codes.length; s++) {
    const [l, c] = codes[s];
    if (l !== 0) {
      const key = l * 65536 + c;
      if (!m.has(key)) {m.set(key, s);}
    }
  }
  return m;
}

// Lean: TarGz.decodeSym / decodeSymAux — bit walk up to maxLen
function decodeSym(r, table, maxLen) {
  let acc = 0;
  for (let k = 1; k <= maxLen; k++) {
    const b = readBits(r, 1);
    if (b === null) {return null;}
    acc = 2 * acc + b;
    const hit = table.get(k * 65536 + acc);
    if (hit !== undefined) {return hit;}
  }
  return null;
}

// Lean: TarGz.NumPrefix / PrefixFree — the decidable runtime check
function numPrefix(p, q) {
  return p[0] <= q[0] && Math.floor(q[1] / 2 ** (q[0] - p[0])) === p[1];
}

function prefixFree(maxLen, codes) {
  const used = [];
  for (const p of codes) {
    if (p[0] !== 0) {
      if (!(p[0] <= maxLen && p[1] < 2 ** p[0])) {return false;}
      used.push(p);
    }
  }
  for (let i = 0; i < used.length; i++) {
    for (let j = 0; j < used.length; j++) {
      if (i !== j && numPrefix(used[i], used[j])) {return false;}
    }
  }
  return true;
}

// Lean: TarGz.SymUsable
function symUsable(codes, s) {
  return s < codes.length && codes[s][0] !== 0;
}

/* ============================ Code-length heuristic ======================
 * Lean: TarGz.HuffLen — proof-free by design; the encoder re-validates the
 * result (DynOk) and falls back to stored blocks. Must match Lean exactly
 * for byte-identical output.
 */

// Lean: TarGz.wqInsert — stable insert before the first strictly greater weight
function wqInsert(q, w, t) {
  let i = 0;
  while (i < q.length && !(w < q[i][0])) {i++;}
  q.splice(i, 0, [w, t]);
  return q;
}

// Lean: TarGz.buildTree — pair the two lightest until one remains
function buildTree(q) {
  if (q.length === 0) {return null;}
  while (q.length >= 2) {
    const [w1, t1] = q[0];
    const [w2, t2] = q[1];
    q = wqInsert(q.slice(2), w1 + w2, { l: t1, r: t2 });
  }
  return q[0][1];
}

// Lean: TarGz.treeDepths / maxDepth
function treeDepths(depths, t, d) {
  if (t.l === undefined) {depths.push([t.s, d]);}
  else {
    treeDepths(depths, t.l, d + 1);
    treeDepths(depths, t.r, d + 1);
  }
}

// Lean: TarGz.tryLengths
function tryLengths(maxLen, n, freqs) {
  let q = [];
  const usedCount = freqs.reduce((a, f) => a + (f !== 0 ? 1 : 0), 0);
  for (let i = 0; i < freqs.length; i++) {
    if (freqs[i] !== 0) {q = wqInsert(q, freqs[i], { s: i });}
  }
  const tree = buildTree(q);
  if (tree === null) {return null;}
  // Lean-fidelity branch; unreachable through the
// public API because mkLengths applies ensureTwoUsed first.
/* node:coverage disable */
  if (usedCount === 1) {
    return Array.from({ length: n }, (_, s) => (freqs[s] !== 0 ? 1 : 0));
  }
  /* node:coverage enable */
  const depths = [];
  treeDepths(depths, tree, 0);
  let md = 0;
  for (const [, d] of depths) {md = Math.max(md, d);}
  if (md > maxLen) {return null;}
  const lens = new Array(n).fill(0);
  for (const [s, d] of depths) {lens[s] = d;}
  return lens;
}

// Lean: TarGz.ensureTwoUsed
function ensureTwoUsed(freqs) {
  const f = freqs.slice();
  const used = f.reduce((a, x) => a + (x !== 0 ? 1 : 0), 0);
  if (used === 0) {
    f[0] += 1;
    f[1] += 1;
  } else if (used === 1) {
    if (f[0] === 0) {f[0] += 1;}
    else {f[1] += 1;}
  }
  return f;
}

// Lean: TarGz.mkLengths — ≤ 4 frequency-halving retries, then all-zero
function mkLengths(maxLen, n, freqs0) {
  let fs = ensureTwoUsed(freqs0);
  for (let retries = 5; retries > 0; retries--) {
    const lens = tryLengths(maxLen, n, fs);
    if (lens !== null) {return lens;}
    fs = fs.map((f) => (f === 0 ? 0 : Math.floor(f / 2) + 1));
  }
  return new Array(n).fill(0);
}

/* ============================ LZ77 =======================================
 * Lean: TarGz.Lz77 — greedy hash-chain matcher; the round trip
 * resolve_tokenize is proved from the verified match postcondition only.
 * Tokens: [byte] for literals, [len, dist] for references.
 */

// Lean: TarGz.hash3
function hash3(a, b, c) {
  return ((a << 10) ^ (b << 5) ^ c) & 32767;
}

// Lean: TarGz.matchLen
function matchLen(data, src, pos, fuel) {
  let n = 0;
  while (n < fuel && data[src + n] === data[pos + n]) {n++;}
  return n;
}

// Lean: TarGz.chainWalk (tries = 32, window 32768, max match 258)
function chainWalk(data, pos, prev, cand, tries, bestLen, bestDist) {
  const fuel = Math.min(258, data.length - pos);
  for (let t = tries; t > 0; t--) {
    if (!(cand < pos && pos - cand <= 32768)) {break;}
    const l = matchLen(data, cand, pos, fuel);
    if (l > bestLen) {
      bestLen = l;
      bestDist = pos - cand;
    }
    cand = prev[cand];
  }
  return [bestLen, bestDist];
}

// Lean: TarGz.tokenizeGo / tokenize
function tokenize(data) {
  const size = data.length;
  const head = new Uint32Array(32768).fill(size);
  const prev = new Uint32Array(size).fill(size);
  const toks = [];
  let pos = 0;
  while (pos < size) {
    if (pos + 3 <= size) {
      const h = hash3(data[pos], data[pos + 1], data[pos + 2]);
      const cand = head[h];
      const [bestLen, bestDist] = chainWalk(data, pos, prev, cand, 32, 0, 0);
      head[h] = pos;
      prev[pos] = cand;
      if (bestLen >= 3) {
        toks.push([bestLen, bestDist]);
        pos += bestLen;
      } else {
        toks.push([data[pos]]);
        pos += 1;
      }
    } else {
      toks.push([data[pos]]);
      pos += 1;
    }
  }
  return toks;
}

/* ============================ DEFLATE ====================================
 * Lean: TarGz.Deflate — dynamic-Huffman encoder with the decidable DynOk
 * runtime check and a stored-block fallback; the decoder handles all three
 * block types (proved round trip: inflate_deflate_append).
 */

// Lean: TarGz.lenTable / distTable — [sym, base, extraBits]
const LEN_TABLE = [
  [257, 3, 0], [258, 4, 0], [259, 5, 0], [260, 6, 0], [261, 7, 0], [262, 8, 0],
  [263, 9, 0], [264, 10, 0], [265, 11, 1], [266, 13, 1], [267, 15, 1], [268, 17, 1],
  [269, 19, 2], [270, 23, 2], [271, 27, 2], [272, 31, 2], [273, 35, 3], [274, 43, 3],
  [275, 51, 3], [276, 59, 3], [277, 67, 4], [278, 83, 4], [279, 99, 4], [280, 115, 4],
  [281, 131, 5], [282, 163, 5], [283, 195, 5], [284, 227, 5], [285, 258, 0],
];

const DIST_TABLE = [
  [0, 1, 0], [1, 2, 0], [2, 3, 0], [3, 4, 0], [4, 5, 1], [5, 7, 1], [6, 9, 2],
  [7, 13, 2], [8, 17, 3], [9, 25, 3], [10, 33, 4], [11, 49, 4], [12, 65, 5],
  [13, 97, 5], [14, 129, 6], [15, 193, 6], [16, 257, 7], [17, 385, 7], [18, 513, 8],
  [19, 769, 8], [20, 1025, 9], [21, 1537, 9], [22, 2049, 10], [23, 3073, 10],
  [24, 4097, 11], [25, 6145, 11], [26, 8193, 12], [27, 12289, 12], [28, 16385, 13],
  [29, 24577, 13],
];

// Lean: TarGz.encodeLenSym — [sym, extraBits, extraVal]
function encodeLenSym(len) {
  if (len === 258) {return [285, 0, 0];}
  for (const [s, base, extra] of LEN_TABLE) {
    if (base <= len && len < base + 2 ** extra) {return [s, extra, len - base];}
  }
  /* node:coverage disable */
  // unreachable: tokenize only emits 3 <= len <= 258.
  return [0, 0, 0];
  /* node:coverage enable */
}

// Lean: TarGz.encodeDistSym
function encodeDistSym(d) {
  for (const [s, base, extra] of DIST_TABLE) {
    if (base <= d && d < base + 2 ** extra) {return [s, extra, d - base];}
  }
  /* node:coverage disable */
  // unreachable: tokenize only emits 1 <= d <= 32768.
  return [0, 0, 0];
  /* node:coverage enable */
}

// Lean: TarGz.lenSymBase / distSymBase
function lenSymBase(sym) {
  for (const [s, base, extra] of LEN_TABLE) {if (s === sym) {return [base, extra];}}
  return null;
}

function distSymBase(sym) {
  for (const [s, base, extra] of DIST_TABLE) {if (s === sym) {return [base, extra];}}
  return null;
}

// Lean: TarGz.LenOk / DistOk (part of the runtime TokUsable check)
function lenOk(len) {
  const [s, e, v] = encodeLenSym(len);
  const b = lenSymBase(s);
  return b !== null && b[0] === len - v && b[1] === e && v < 2 ** e && v <= len && 256 < s;
}

function distOk(d) {
  const [s, e, v] = encodeDistSym(d);
  const b = distSymBase(s);
  return b !== null && b[0] === d - v && b[1] === e && v < 2 ** e && v <= d;
}

// Lean: TarGz.TokUsable
function tokUsable(litC, distC, t) {
  if (t.length === 1) {return symUsable(litC, t[0]);}
  const [len, d] = t;
  return (
    3 <= len && len <= 258 && 1 <= d && d <= 32768 && lenOk(len) && distOk(d) &&
    symUsable(litC, encodeLenSym(len)[0]) && symUsable(distC, encodeDistSym(d)[0])
  );
}

// Lean: TarGz.tokenFreqs (+ the EOB bump from encodeBlockDyn)
function tokenFreqs(toks) {
  const lf = new Array(286).fill(0);
  const df = new Array(30).fill(0);
  for (const t of toks) {
    if (t.length === 1) {lf[t[0]] += 1;}
    else {
      lf[encodeLenSym(t[0])[0]] += 1;
      df[encodeDistSym(t[1])[0]] += 1;
    }
  }
  return [lf, df];
}

// Lean: TarGz.clFreqs
function clFreqs(vals) {
  const f = new Array(19).fill(0);
  for (const v of vals) {f[v] += 1;}
  return f;
}

// Lean: TarGz.clOrder
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

// Lean: TarGz.DynOk — the decidable validity bundle
function dynOk(toks, litLens, distLens, clLens, litC, distC, clC) {
  if (litLens.length !== 286 || distLens.length !== 30 || clLens.length !== 19) {return false;}
  if (!clLens.every((v) => v <= 7)) {return false;}
  if (!prefixFree(15, litC) || !prefixFree(15, distC) || !prefixFree(7, clC)) {return false;}
  if (!symUsable(litC, 256)) {return false;}
  if (!toks.every((t) => tokUsable(litC, distC, t))) {return false;}
  for (const v of litLens.concat(distLens)) {
    if (!(v <= 15 && symUsable(clC, v))) {return false;}
  }
  return true;
}

// Lean: TarGz.writeDynHeader (HCLEN = 15; literal-only CL symbols)
function writeDynHeader(w, litLens, distLens, clLens, clC) {
  writeBits(w, litLens.length - 257, 5);
  writeBits(w, distLens.length - 1, 5);
  writeBits(w, 15, 4);
  for (const i of CL_ORDER) {writeBits(w, clLens[i], 3);}
  for (const v of litLens.concat(distLens)) {encodeSym(w, clC, v);}
}

// Lean: TarGz.encodeTok / encodeTokens
function encodeTokens(w, litC, distC, toks) {
  for (const t of toks) {
    if (t.length === 1) {encodeSym(w, litC, t[0]);}
    else {
      const [ls, le, lv] = encodeLenSym(t[0]);
      const [ds, de, dv] = encodeDistSym(t[1]);
      encodeSym(w, litC, ls);
      writeBits(w, lv, le);
      encodeSym(w, distC, ds);
      writeBits(w, dv, de);
    }
  }
  encodeSym(w, litC, 256);
}

// Lean: TarGz.encodeStoredBlock / encodeStored / storedChunks
// the verified stored fallback: only taken when the
// DynOk runtime check fails, and TarGz.canonical_prefixFree proves the
// PrefixFree component of that check can never fail. Kept (like in the Lean
// model) as belt and suspenders.
/* node:coverage disable */
function writeStored(w, data) {
  let off = 0;
  do {
    const chunk = data.subarray(off, off + 65535);
    const final = off + chunk.length >= data.length;
    writeBits(w, final ? 1 : 0, 1);
    writeBits(w, 0, 2);
    writeBits(w, 0, 5); // blocks start byte-aligned; 5 pad bits after the header
    writeBits(w, chunk.length, 16);
    writeBits(w, 65535 - chunk.length, 16);
    for (const b of chunk) {writeBits(w, b, 8);}
    off += chunk.length;
  } while (off < data.length);
}
/* node:coverage enable */

// Lean: TarGz.encodeBlockDyn + deflate — dynamic block or stored fallback
export function deflate(data) {
  const w = bitWriter();
  const toks = tokenize(data);
  const [lf, df] = tokenFreqs(toks);
  lf[256] += 1;
  const litLens = mkLengths(15, 286, lf);
  const distLens = mkLengths(15, 30, df);
  const clLens = mkLengths(7, 19, clFreqs(litLens.concat(distLens)));
  const litC = canonicalCodes(15, litLens);
  const distC = canonicalCodes(15, distLens);
  const clC = canonicalCodes(7, clLens);
  if (dynOk(toks, litLens, distLens, clLens, litC, distC, clC)) {
    writeBits(w, 1, 1);
    writeBits(w, 2, 2);
    writeDynHeader(w, litLens, distLens, clLens, clC);
    encodeTokens(w, litC, distC, toks);
  } else {
    /* node:coverage disable */
    // see writeStored above.
    writeStored(w, data);
  }
  /* node:coverage enable */
  return finishBits(w);
}

// Lean: TarGz.fixedLitLens / fixedDistLens
const FIXED_LIT_LENS = (() => {
  const l = [];
  for (let i = 0; i < 144; i++) {l.push(8);}
  for (let i = 0; i < 112; i++) {l.push(9);}
  for (let i = 0; i < 24; i++) {l.push(7);}
  for (let i = 0; i < 8; i++) {l.push(8);}
  return l;
})();

const FIXED_DIST_LENS = new Array(30).fill(5);

// Lean: TarGz.readClSeq — full 16/17/18 RLE semantics
function readClSeq(r, clTable, need) {
  const acc = [];
  while (acc.length < need) {
    const s = decodeSym(r, clTable, 7);
    if (s === null) {return null;}
    if (s <= 15) {acc.push(s);}
    else if (s === 16) {
      if (acc.length === 0) {return null;}
      const k = readBits(r, 2);
      if (k === null) {return null;}
      if (!(acc.length + k + 3 <= need)) {return null;}
      const prevv = acc[acc.length - 1];
      for (let i = 0; i < k + 3; i++) {acc.push(prevv);}
    } else if (s === 17) {
      const k = readBits(r, 3);
      if (k === null) {return null;}
      if (!(acc.length + k + 3 <= need)) {return null;}
      for (let i = 0; i < k + 3; i++) {acc.push(0);}
    } else if (s === 18) {
      const k = readBits(r, 7);
      if (k === null) {return null;}
      if (!(acc.length + k + 11 <= need)) {return null;}
      for (let i = 0; i < k + 11; i++) {acc.push(0);}
    } else {return null;}
  }
  return acc;
}

// Lean: TarGz.readDynHeader
function readDynHeader(r) {
  const hlit = readBits(r, 5);
  const hdist = readBits(r, 5);
  const hclen = readBits(r, 4);
  if (hlit === null || hdist === null || hclen === null) {return null;}
  const clLens = new Array(19).fill(0);
  for (let p = 0; p < hclen + 4; p++) {
    const v = readBits(r, 3);
    if (v === null) {return null;}
    clLens[CL_ORDER[p]] = v;
  }
  const clTable = decodeTable(canonicalCodes(7, clLens));
  const combined = readClSeq(r, clTable, hlit + 257 + (hdist + 1));
  if (combined === null) {return null;}
  return [combined.slice(0, hlit + 257), combined.slice(hlit + 257)];
}

// Lean: TarGz.decodeTokens — identical validity conditions to `resolve`
function decodeTokens(r, litTable, distTable_, out) {
  for (;;) {
    const sym = decodeSym(r, litTable, 15);
    if (sym === null) {return false;}
    if (sym === 256) {return true;}
    if (sym < 256) {
      out.push(sym);
      continue;
    }
    const lb = lenSymBase(sym);
    if (lb === null) {return false;}
    const ev = readBits(r, lb[1]);
    if (ev === null) {return false;}
    const len = lb[0] + ev;
    const dsym = decodeSym(r, distTable_, 15);
    if (dsym === null) {return false;}
    const db = distSymBase(dsym);
    if (db === null) {return false;}
    const dv = readBits(r, db[1]);
    if (dv === null) {return false;}
    const dist = db[0] + dv;
    if (!(1 <= dist && dist <= out.length && dist <= 32768 && 3 <= len && len <= 258)) {
      return false;
    }
    // Lean: TarGz.lzCopy — per-byte copy, self-overlap = RLE
    for (let j = 0; j < len; j++) {out.push(out[out.length - dist]);}
  }
}

// Lean: TarGz.inflateLoop / inflate — returns [payload, bytesConsumed] | null
export function inflate(bytes) {
  const r = bitReader(bytes);
  const out = [];
  for (;;) {
    const bfinal = readBits(r, 1);
    const btype = readBits(r, 2);
    if (bfinal === null || btype === null) {return null;}
    if (btype === 0) {
      const pad = (8 - (r.pos % 8)) % 8;
      if (readBits(r, pad) === null) {return null;}
      const len = readBits(r, 16);
      const nlen = readBits(r, 16);
      if (len === null || nlen === null || nlen !== 65535 - len) {return null;}
      for (let i = 0; i < len; i++) {
        const b = readBits(r, 8);
        if (b === null) {return null;}
        out.push(b);
      }
    } else if (btype === 1) {
      const ok = decodeTokens(
        r,
        decodeTable(canonicalCodes(15, FIXED_LIT_LENS)),
        decodeTable(canonicalCodes(15, FIXED_DIST_LENS)),
        out
      );
      if (!ok) {return null;}
    } else if (btype === 2) {
      const hdr = readDynHeader(r);
      if (hdr === null) {return null;}
      const ok = decodeTokens(
        r,
        decodeTable(canonicalCodes(15, hdr[0])),
        decodeTable(canonicalCodes(15, hdr[1])),
        out
      );
      if (!ok) {return null;}
    } else {return null;}
    if (bfinal === 1) {
      return [Uint8Array.from(out), Math.floor((r.pos + 7) / 8)];
    }
  }
}

/* ============================ gzip container =============================
 * Lean: TarGz.Gzip (gzip, gunzip, skipFlagFields; proved gunzip_gzip)
 */

function writeLE32(out, v) {
  out.push(v & 0xff, (v >>> 8) & 0xff, (v >>> 16) & 0xff, (v >>> 24) & 0xff);
}

// Lean: TarGz.gzip — FLG=0, MTIME=0, XFL=0, OS=255 (deterministic)
export function gzip(data) {
  const deflated = deflate(data);
  const out = [0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 255];
  for (const b of deflated) {out.push(b);}
  writeLE32(out, crc32(data));
  writeLE32(out, data.length % 4294967296);
  return Uint8Array.from(out);
}

// Lean: TarGz.gunzip — skips FEXTRA/FNAME/FCOMMENT/FHCRC, verifies CRC+ISIZE
export function gunzip(bytes) {
  if (bytes.length < 10 || bytes[0] !== 0x1f || bytes[1] !== 0x8b || bytes[2] !== 8) {
    return null;
  }
  const flg = bytes[3];
  let p = 10;
  if (flg & 4) {
    if (p + 2 > bytes.length) {return null;}
    const xlen = bytes[p] + 256 * bytes[p + 1];
    p += 2;
    if (p + xlen > bytes.length) {return null;}
    p += xlen;
  }
  if (flg & 8) {
    while (p < bytes.length && bytes[p] !== 0) {p++;}
    if (p >= bytes.length) {return null;}
    p++;
  }
  if (flg & 16) {
    while (p < bytes.length && bytes[p] !== 0) {p++;}
    if (p >= bytes.length) {return null;}
    p++;
  }
  if (flg & 2) {
    if (p + 2 > bytes.length) {return null;}
    p += 2;
  }
  const res = inflate(bytes.subarray(p));
  if (res === null) {return null;}
  const [payload, consumed] = res;
  const t = p + consumed;
  if (t + 8 > bytes.length) {return null;}
  const crcv =
    (bytes[t] + 256 * bytes[t + 1] + 65536 * bytes[t + 2] + 16777216 * bytes[t + 3]) >>> 0;
  const isize =
    bytes[t + 4] + 256 * bytes[t + 5] + 65536 * bytes[t + 6] + 16777216 * bytes[t + 7];
  if (crcv !== crc32(payload) || isize !== payload.length % 4294967296) {return null;}
  return payload;
}

/* ============================ USTAR ======================================
 * Lean: TarGz.Tar (mkHeader with checksum-as-spaces splice, tolerant reader;
 * proved untar_tar)
 */

// Lean: TarGz.octEnc — w-1 zero-padded octal digits, then NUL
function octEnc(out, w, n) {
  for (let i = w - 2; i >= 0; i--) {out.push(0x30 + (Math.floor(n / 8 ** i) % 8));}
  out.push(0);
}

// Lean: TarGz.octDec — tolerant: skip leading spaces, octal digits, ignore rest
function octDec(field) {
  let i = 0;
  while (i < field.length && field[i] === 0x20) {i++;}
  let any = false;
  let v = 0;
  while (i < field.length && 0x30 <= field[i] && field[i] <= 0x37) {
    v = 8 * v + (field[i] - 0x30);
    i++;
    any = true;
  }
  return any ? v : null;
}

function padTo(out, upto) {
  while (out.length < upto) {out.push(0);}
}

// Lean: TarGz.mkHeader / headerFields
function mkHeader(nameBytes, dataLen) {
  const mk = (chk) => {
    const h = [];
    for (const b of nameBytes) {h.push(b);} // name, offset 0
    padTo(h, 100);
    octEnc(h, 8, 0o644); // mode
    octEnc(h, 8, 0); // uid
    octEnc(h, 8, 0); // gid
    octEnc(h, 12, dataLen); // size
    octEnc(h, 12, 0); // mtime
    for (const b of chk) {h.push(b);} // chksum (8 bytes)
    h.push(0x30); // typeflag '0'
    padTo(h, 257);
    h.push(0x75, 0x73, 0x74, 0x61, 0x72, 0x00, 0x30, 0x30); // "ustar\0" "00"
    padTo(h, 329); // uname(32) + gname(32), NUL
    octEnc(h, 8, 0); // devmajor
    octEnc(h, 8, 0); // devminor
    padTo(h, 512); // prefix(155) + pad(12)
    return h;
  };
  const spaces = mk([0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20]);
  let sum = 0;
  for (const b of spaces) {sum += b;}
  const chk = [];
  octEnc(chk, 7, sum);
  chk.push(0x20);
  return mk(chk);
}

// Lean: TarGz.ValidEntry
function validEntry(nameBytes, data) {
  return (
    nameBytes.length > 0 &&
    nameBytes.length <= 100 &&
    !nameBytes.includes(0) &&
    data.length < 8 ** 11
  );
}

// Lean: TarGz.tarBytes — entries: [{ name: Uint8Array, data: Uint8Array }]
export function tar(entries) {
  const out = [];
  for (const e of entries) {
    for (const b of mkHeader(e.name, e.data.length)) {out.push(b);}
    for (const b of e.data) {out.push(b);}
    padTo(out, out.length + ((512 - (e.data.length % 512)) % 512));
  }
  for (let i = 0; i < 1024; i++) {out.push(0);}
  return Uint8Array.from(out);
}

// Lean: TarGz.untarBytes / untar — tolerant ustar reader (prefix join,
// checksum verify, skips dirs / pax x,g / GNU L,K / other typeflags)
export function untar(bytes) {
  const entries = [];
  let off = 0;
  for (;;) {
    const header = bytes.subarray(off, off + 512);
    if (header.length < 512) {return null;}
    if (header.every((b) => b === 0)) {return entries;}
    const size = octDec(header.subarray(124, 136));
    const stored = octDec(header.subarray(148, 156));
    if (size === null || stored === null) {return null;}
    let sum = 0;
    for (let i = 0; i < 512; i++) {sum += i >= 148 && i < 156 ? 0x20 : header[i];}
    if (sum !== stored) {return null;}
    const bodyOff = off + 512;
    const padded = Math.floor((size + 511) / 512) * 512;
    const tf = header[156];
    if (tf === 0x30 || tf === 0x00) {
      let nameEnd = 0;
      while (nameEnd < 100 && header[nameEnd] !== 0) {nameEnd++;}
      const rawName = Array.from(header.subarray(0, nameEnd));
      let preEnd = 345;
      while (preEnd < 500 && header[preEnd] !== 0) {preEnd++;}
      const prefixF = Array.from(header.subarray(345, preEnd));
      const name = prefixF.length === 0 ? rawName : prefixF.concat([0x2f], rawName);
      entries.push({
        name: Uint8Array.from(name),
        data: bytes.slice(bodyOff, bodyOff + size),
      });
    }
    off = bodyOff + padded;
  }
}

/* ============================ Top level ==================================
 * Lean: TarGz.Correctness (create / extract; proved extract_create)
 */

const utf8encode = (s) => new TextEncoder().encode(s);
const utf8decode = (b) => new TextDecoder("utf-8", { fatal: false }).decode(b);

// entries: [{ name: string | Uint8Array, data: Uint8Array }]
export function create(entries) {
  const es = entries.map((e) => ({
    name: typeof e.name === "string" ? utf8encode(e.name) : e.name,
    data: e.data,
  }));
  for (const e of es) {
    if (!validEntry(e.name, e.data)) {
      throw new Error(`invalid entry name/data: ${utf8decode(e.name)}`);
    }
  }
  return gzip(tar(es));
}

// returns [{ name: string, nameBytes: Uint8Array, data: Uint8Array }] | null
export function extract(bytes) {
  const payload = gunzip(bytes);
  if (payload === null) {return null;}
  const es = untar(payload);
  if (es === null) {return null;}
  return es.map((e) => ({ name: utf8decode(e.name), nameBytes: e.name, data: e.data }));
}

/* ================================= CLI ================================== */
// the CLI is exercised end-to-end by the spawned
// differential and interop test suites (child processes are invisible to
// in-process V8 coverage).
/* node:coverage disable */

const USAGE = `usage:
  node targz.mjs c <out.tar.gz> <files...>    create archive
  node targz.mjs x <archive.tar.gz> [-C dir]  extract archive
  node targz.mjs t <archive.tar.gz>           list contents`;

function safeRelative(name) {
  if (name.startsWith("/") || name.startsWith("\\") || /^[A-Za-z]:/.test(name)) {return false;}
  return name.split("/").every((seg) => seg !== ".." && seg !== "");
}

async function runCli() {
  const fs = await import("node:fs");
  const path = await import("node:path");
  const [cmd, ...rest] = process.argv.slice(2);
  if (cmd === undefined) {
    console.log(USAGE);
    process.exit(0);
  }
  if (cmd === "c" && rest.length >= 2) {
    const [out, ...files] = rest;
    const entries = files.map((f) => ({
      name: f.replaceAll("\\", "/"),
      data: new Uint8Array(fs.readFileSync(f)),
    }));
    fs.writeFileSync(out, create(entries));
    return;
  }
  if ((cmd === "x" || cmd === "t") && rest.length >= 1) {
    const archive = rest[0];
    let dir = ".";
    const ci = rest.indexOf("-C");
    if (ci >= 0 && rest[ci + 1]) {dir = rest[ci + 1];}
    const entries = extract(new Uint8Array(fs.readFileSync(archive)));
    if (entries === null) {
      console.error("error: not a valid .tar.gz archive (or checksum mismatch)");
      process.exit(1);
    }
    for (const e of entries) {
      if (cmd === "t") {
        console.log(e.name);
        continue;
      }
      if (!safeRelative(e.name)) {
        console.error(`error: refusing unsafe path: ${e.name}`);
        process.exit(1);
      }
      const target = path.join(dir, ...e.name.split("/"));
      fs.mkdirSync(path.dirname(target), { recursive: true });
      fs.writeFileSync(target, e.data);
    }
    return;
  }
  console.error(USAGE);
  process.exit(1);
}

// Node-only entry detection; in a browser this whole block is inert.
if (typeof process !== "undefined" && process.versions?.node && process.argv?.[1]) {
  const { pathToFileURL } = await import("node:url");
  if (import.meta.url === pathToFileURL(process.argv[1]).href) {
    await runCli();
  }
}
