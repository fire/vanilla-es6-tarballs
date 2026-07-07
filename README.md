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
node targz.mjs c out.tar.gz file1.txt dir/file2.bin   # create
node targz.mjs x out.tar.gz -C dest                   # extract
node targz.mjs t out.tar.gz                           # list
```

Or as a library (browser or Node — the core is pure `Uint8Array` code with
zero imports):

```js
import { create, extract, gzip, gunzip, deflate, inflate, crc32 } from "./targz.mjs";
const archive = create([{ name: "hello.txt", data: new TextEncoder().encode("hi\n") }]);
const entries = extract(archive); // [{ name, nameBytes, data }] or null
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

**Proof-carrying runtime checks.** The heuristic parts (Huffman code-length
assignment, hash-chain match finding) are deliberately *outside* the trusted
story: the encoder re-validates their output at runtime with decidable
predicates (`PrefixFree`, `WFLens`-style bounds, `DynOk`, and per-token
`TokUsable` incl. the length/distance symbol tables), and falls back to
verified stored blocks if a check ever fails. That makes the headline
theorems **unconditional** without proving anything about heuristic quality.
(The remaining "nice to have" structural theorem — that the canonical code of
any Kraft-valid length assignment is always prefix-free, i.e. the fallback is
dead code — is quality, not correctness.)

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

- Creation: USTAR, regular files only, names ≤ 100 bytes (UTF-8), one gzip
  member, a single final dynamic-Huffman DEFLATE block (stored blocks as the
  verified fallback), all-19 CL lengths with literal-only code-length symbols
  (legal DEFLATE; the *decoder* handles the full 16/17/18 RLE).
- Extraction: stored + fixed + dynamic blocks; gzip optional header fields
  (FEXTRA/FNAME/FCOMMENT/FHCRC) skipped; CRC-32 + ISIZE verified; ustar
  `prefix` field joined; header checksums verified; pax `x`/`g`, GNU `L`/`K`,
  directories and other typeflags are skipped (long-name entries are not
  reconstructed).
- The CLI refuses unsafe extraction paths (absolute, drive-letter, `..`).

## Testing

```powershell
lake build            # proofs + #guard vectors + axiom snapshots + Lean CLI
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
