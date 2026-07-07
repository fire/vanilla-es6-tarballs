import TarGz

/-!
Golden test vectors. `lake build` elaborates every `#guard`, so building this
module IS the Lean test run.
-/

namespace Tests

open TarGz

-- 5 = 0b101, LSB first
#guard natBitsLE 3 5 = [true, false, true]
#guard readBitsLE 3 [true, false, true, true] = some (5, [true])
#guard bitsToBytes (natBitsLE 8 0xAB) = [0xAB]
#guard bytesToBits [0x01] = [true, false, false, false, false, false, false, false]
#guard readLE32 (writeLE32 0xDEADBEEF) = some (0xDEADBEEF, [])

/-! ## CRC-32 check vector ("123456789" → 0xCBF43926) -/

#guard crc32 [0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39] = 0xCBF43926
#guard crc32Spec [0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39] = 0xCBF43926

/-! ## Canonical Huffman codes -/

-- Small sanity vector: lens [2,1,3,3] → positional (len, code) pairs.
#guard canonicalCodes 3 [2,1,3,3] = [(2,2),(1,0),(3,6),(3,7)]

-- RFC 1951 §3.2.6 fixed literal/length table spot checks:
--   symbols 0..143   → 8-bit codes 0x30..0xBF
--   symbols 144..255 → 9-bit codes 0x190..0x1FF
--   symbols 256..279 → 7-bit codes 0x00..0x17
--   symbols 280..287 → 8-bit codes 0xC0..0xC7
#guard (canonicalCodes 15 fixedLitLens)[0]!   = (8, 0x30)
#guard (canonicalCodes 15 fixedLitLens)[143]! = (8, 0xBF)
#guard (canonicalCodes 15 fixedLitLens)[144]! = (9, 0x190)
#guard (canonicalCodes 15 fixedLitLens)[255]! = (9, 0x1FF)
#guard (canonicalCodes 15 fixedLitLens)[256]! = (7, 0x00)
#guard (canonicalCodes 15 fixedLitLens)[279]! = (7, 0x17)
#guard (canonicalCodes 15 fixedLitLens)[280]! = (8, 0xC0)
#guard (canonicalCodes 15 fixedLitLens)[287]! = (8, 0xC7)

/-! ## Round trips (tiny inputs; a repeat so LZ77 emits a back-reference) -/

private def rtData : List UInt8 := [1,2,3,4,1,2,3,4,1,2,3,4,5,6]

#guard decide (inflate (deflate rtData) = some (rtData, []))
#guard decide (gunzip (gzip rtData) = some rtData)

-- One-entry tar.gz round trip; name "a.txt" as explicit UTF-8 bytes.
private def rtEntry : TarEntry := ⟨[0x61,0x2E,0x74,0x78,0x74], rtData⟩

#guard decide (extract (create [rtEntry]) = some [rtEntry])

/-! ## Empty cases -/

#guard decide (inflate (deflate []) = some ([], []))
#guard decide (extract (create []) = some [])

end Tests
