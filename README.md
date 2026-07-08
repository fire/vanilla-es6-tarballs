# vanilla-es6-tarballs

A **dependency-free tar + gzip implementation in a single ES6 file**
([`targz.mjs`](targz.mjs)), built *proof-first*: the algorithms are modeled
and machine-verified in **Lean 4** (core only — no Mathlib, no `sorry`, no
`native_decide`), then transcribed line-by-line to JavaScript. The DEFLATE
encoder emits **real dynamic-Huffman blocks** (greedy hash-chain LZ77 +
per-block Huffman tables), and the decoder handles all three block types
(stored / fixed / dynamic), so archives interoperate with `gzip`, zlib, and
`tar`/bsdtar.

```
node targz.mjs c out.tar.gz file1.txt some/dir        # create (dirs recurse, mtimes preserved)
node targz.mjs x out.tar.gz -C dest                   # extract (restores dirs + mtimes)
node targz.mjs t out.tar.gz                           # list
node targz.mjs x untrusted.tgz --max-size 100000000   # decompression-bomb cap
```

Or as a library (browser or Node — the core is pure `Uint8Array` code with
zero imports):

```js
import { create, extract, gzip, gunzip, deflate, inflate, crc32 } from "./targz.mjs";
const archive = create([
  { name: "docs/", dir: true, mtime: 1700000000 },
  { name: "docs/hello.txt", data: new TextEncoder().encode("hi\n"), mode: 0o644 },
]);
const entries = extract(archive, { maxBytes: 1 << 30 });
// [{ name, nameBytes, data, mode, mtime, dir }] or null
```

## The proofs

The Lean model lives in [`TarGz/`](TarGz/); `lake build` checks everything,
including compile-time `#guard` test vectors ([`Tests/Vectors.lean`](Tests/Vectors.lean))
and `#guard_msgs` axiom snapshots ([`Tests/Axioms.lean`](Tests/Axioms.lean))
that fail the build if any theorem ever picks up an axiom beyond
`propext`, `Classical.choice`, `Quot.sound`.

**Headline theorem** (`TarGz/Correctness.lean`):

```lean
theorem extract_create (es : List TarEntry) (h : ∀ e ∈ es, ValidEntry e) :
    extract (create es) = some es
```

Composed from, per layer:

| Theorem | Meaning |
| --- | --- |
| `untar_tar` | USTAR writer/reader round trip, incl. octal fields, the checksum-as-spaces splice, 512-byte framing |
| `gunzip_gzip` | gzip container framing, CRC-32 and ISIZE verification |
| `inflate_deflate_append` | `inflate (deflate d ++ rest) = some (d, rest)` — the DEFLATE round trip, dynamic block *and* stored fallback |
| `decodeTokens_encodeTokens` | Huffman-coded LZ77 token stream round trip |
| `readDynHeader_writeDynHeader` | dynamic block header (HLIT/HDIST/HCLEN, code-length code) round trip |
| `decodeSym_encodeSym` | canonical-Huffman decode∘encode = id for **any** prefix-free assignment |
| `resolve_tokenize` | LZ77 detokenization reconstructs the input (overlap copies included), independent of the match-finder heuristics |
| `crc32_eq_spec` | the table-driven CRC-32 equals the bit-serial specification |
| `canonical_prefixFree` | the canonical code of **any** Kraft-valid length list is prefix-free (interval argument) |

**Proof-carrying runtime checks.** The heuristic parts (Huffman code-length
assignment, hash-chain match finding) are deliberately *outside* the trusted
story: the encoder re-validates their output at runtime with decidable
predicates (`PrefixFree`, `WFLens`-style bounds, `DynOk`, and per-token
`TokUsable` incl. the length/distance symbol tables), and falls back to
verified stored blocks if a check ever fails. That makes the headline
theorems **unconditional** without proving anything about heuristic quality.
On top of that, `canonical_prefixFree` (TarGz/CanonicalPF.lean) proves
structurally that the canonical code of any Kraft-valid length assignment is
prefix-free — so the `PrefixFree` half of the runtime check can never fail
and the fallback it guards is dead code (kept as belt and suspenders).

## The transcription

`targz.mjs` mirrors the Lean model function-by-function (each is annotated
`// Lean: TarGz.…`). Two categories of divergence, both enforced by
**byte-identical differential tests** against the compiled Lean CLI
(`lake exe targz` vs `node targz.mjs` on the same inputs):

- representation: bit-accumulator writer / positional reader instead of
  `List Bool`; typed arrays and a `(len<<16|code)` `Map` instead of lists;
- everything else is intentionally deterministic (stable sorts, fixed
  tie-breaking, mode `0644`, mtime 0, `FLG=0`/`OS=255`) so the two
  implementations produce identical archives.

## Scope and format notes

- Creation: USTAR files **and directories** with **mode and mtime**
  (defaults `0644`/`0755`, mtime 0 — identical input entries always produce
  identical archive bytes), names ≤ 100 bytes (UTF-8), one gzip member. The
  DEFLATE encoder emits a single final dynamic-Huffman block, or stored
  blocks when those are strictly smaller (tiny/incompressible inputs), which
  bounds worst-case expansion to 5 bytes + 0.008%.
- Extraction: stored + fixed + dynamic blocks; gzip optional header fields
  (FEXTRA/FNAME/FCOMMENT/FHCRC) skipped; CRC-32 + ISIZE verified per member;
  **multi-member gzip concatenated** (pigz-style); tar header checksums
  verified; file/directory entries returned with mode + mtime; long names
  via ustar `prefix`, **pax `path`**, and **GNU `L`** entries; **GNU
  base-256 (binary) size fields** read. pax `g`, GNU `K`, links, devices,
  sparse files, and xattrs are skipped.
- Untrusted input: `extract`/`gunzip`/`inflate` accept `{ maxBytes }` as a
  decompression-bomb cap (`--max-size` on the CLI).
- The CLI refuses unsafe extraction paths (absolute, drive-letter, `..`) and
  canonicalizes modes to `0644`/`0755` on create for cross-platform
  byte-determinism (the library preserves whatever mode you pass).
- Reader-side tolerances beyond the verified model (pax/GNU long names,
  base-256 sizes, multi-member gzip) are deliberate supersets: the Lean
  theorems cover everything this implementation can *produce* plus the
  standard ustar/octal/single-member subset it reads back.

## Testing

```powershell
lake build            # proofs + #guard vectors + axiom snapshots + Lean CLI
npm run test:coverage # + built-in V8 coverage (~99.7% lines, 100% functions;
                      # the verified stored fallback and the CLI are annotated)
node --test test/     # JS round trips, node:zlib cross-reference (both
                      # directions incl. stored blocks and FEXTRA/FNAME
                      # headers), tar.exe (bsdtar) interop both directions,
                      # Lean-vs-JS byte-identical differential tests
npx playwright test   # the vanilla ES6 core in real Chromium: import,
                      # round trips, corruption rejection
scripts\ci.ps1        # all of the above + sorry/native_decide hygiene
```

`package.json` has **zero runtime dependencies** — `@playwright/test` is the
only dev dependency; `node:zlib` is used purely as an independent reference
implementation inside the test suite.

## Repository layout

```
targz.mjs                 the deliverable: single-file ES6 library + CLI
TarGz/                    Lean 4 model + proofs (Bits, Crc32, Huffman,
                          HuffLen, Lz77, Deflate, Gzip, Tar, Correctness)
Main.lean                 Lean CLI twin (differential-test reference)
Tests/                    #guard vectors + axiom snapshots (built by lake)
test/                     node --test suites
playwright/               browser suite + harness page
scripts/                  dep-free static server, hygiene check, ci.ps1
```
