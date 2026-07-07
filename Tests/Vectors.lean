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

end Tests
