import TarGz.Bits

/-!
# CRC-32 (reflected, polynomial 0xEDB88320)

`crcByte`/`crc32Spec` is the bit-serial specification. `crc32` is the
table-driven implementation that the ES6 program transcribes. The headline
result `crc32_eq_spec` proves the classic table identity
`crcStep8 x = (x >>> 8) ^^^ crcStep8 (x &&& 0xFF)` and lifts it to the fold,
using only kernel-checked `decide` so the axiom audit stays clean.
-/

namespace TarGz

def crcPoly : UInt32 := 0xEDB88320

def crcBitStep (c : UInt32) : UInt32 :=
  if c &&& 1 == 1 then (c >>> 1) ^^^ crcPoly else c >>> 1

def crcStep8 (c : UInt32) : UInt32 :=
  crcBitStep (crcBitStep (crcBitStep (crcBitStep
    (crcBitStep (crcBitStep (crcBitStep (crcBitStep c)))))))

/-- Spec: bit-serial CRC-32 update by one byte. -/
def crcByte (c : UInt32) (b : UInt8) : UInt32 :=
  crcStep8 (c ^^^ b.toUInt32)

def crc32Spec (bs : List UInt8) : UInt32 :=
  (bs.foldl crcByte 0xFFFFFFFF) ^^^ 0xFFFFFFFF

def crcTable : Array UInt32 :=
  Array.ofFn (n := 256) fun i => crcStep8 (UInt32.ofNat i.val)

/-- Table-driven update — the form the ES6 program transcribes. -/
def crc32Update (c : UInt32) (b : UInt8) : UInt32 :=
  (c >>> 8) ^^^ crcTable[((c ^^^ b.toUInt32) &&& 0xFF).toNat]!

def crc32 (bs : List UInt8) : UInt32 :=
  (bs.foldl crc32Update 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-! ## The table identity -/

private theorem shiftRight_xor (a b k : UInt32) :
    (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  refine UInt32.toBitVec_inj.mp ?_
  simp
  ext i hi
  simp

private theorem and_one_xor {hi : UInt32} (lo : UInt32) (h : hi &&& 1 = 0) :
    (hi ^^^ lo) &&& 1 = lo &&& 1 := by
  refine UInt32.toBitVec_inj.mp ?_
  have h' : hi.toBitVec &&& 1#32 = 0#32 := by
    have := congrArg UInt32.toBitVec h
    simpa using this
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_xor]
  ext i hi32
  simp [Bool.and_xor_distrib_right]
  by_cases hz : i = 0
  · subst hz
    have h0 : hi.toBitVec[0] = false := by
      have := congrArg (fun v => v.getLsbD 0) h'
      simpa using this
    simp [h0]
  · simp [hz]

private theorem crcBitStep_split {hi : UInt32} (lo : UInt32) (h : hi &&& 1 = 0) :
    crcBitStep (hi ^^^ lo) = (hi >>> 1) ^^^ crcBitStep lo := by
  unfold crcBitStep
  rw [and_one_xor lo h]
  by_cases hb : (lo &&& 1 == 1)
  · simp [hb, shiftRight_xor, UInt32.xor_assoc]
  · simp [hb, shiftRight_xor]
  -- hb rewriting: `lo &&& 1 == 1` is a Bool; simp [hb] closes the if

/-- The high part `x &&& 0xFFFFFF00`, all parity facts, and shift folding. -/
private theorem mask_and_one_0 (x : UInt32) : (x &&& 0xFFFFFF00) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  rw [BitVec.getElem_eq_testBit_toNat] at hm
  exact absurd hm (by decide)

private theorem mask_parity_1 (x : UInt32) :
    ((x &&& 0xFFFFFF00) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_parity_2 (x : UInt32) :
    (((x &&& 0xFFFFFF00) >>> 1) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_parity_3 (x : UInt32) :
    ((((x &&& 0xFFFFFF00) >>> 1) >>> 1) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_parity_4 (x : UInt32) :
    (((((x &&& 0xFFFFFF00) >>> 1) >>> 1) >>> 1) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_parity_5 (x : UInt32) :
    ((((((x &&& 0xFFFFFF00) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_parity_6 (x : UInt32) :
    (((((((x &&& 0xFFFFFF00) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_parity_7 (x : UInt32) :
    ((((((((x &&& 0xFFFFFF00) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) &&& 1 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro _ hm hz
  subst hz
  exact absurd hm (by decide)

private theorem mask_shift8_fold (x : UInt32) :
    (((((((((x &&& 0xFFFFFF00) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1) >>> 1)
      = x >>> 8 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp
  intro hx
  by_cases hc : 8 + i < 32
  · have key : ∀ j : Fin 32, 8 ≤ j.val → (4294967040#32).getLsbD j.val = true := by decide
    exact key ⟨8 + i, hc⟩ (Nat.le_add_right 8 i)
  · rw [BitVec.getLsbD_of_ge x.toBitVec (8 + i) (by omega)] at hx
    exact absurd hx (by simp)

private theorem crcStep8_split (x : UInt32) :
    crcStep8 x = (x >>> 8) ^^^ crcStep8 (x &&& 0xFF) := by
  have hdecomp : (x &&& 0xFFFFFF00) ^^^ (x &&& 0xFF) = x := by
    refine UInt32.toBitVec_inj.mp ?_
    refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
    simp only [UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_ofNat,
      BitVec.getLsbD_xor, BitVec.getLsbD_and]
    have key : ∀ (j : Fin 32) (b : Bool),
        (b && (4294967040#32).getLsbD j.val ^^ b && (255#32).getLsbD j.val) = b := by
      decide
    exact key ⟨i, hi⟩ (x.toBitVec.getLsbD i)
  conv => lhs; rw [← hdecomp]
  unfold crcStep8
  rw [crcBitStep_split _ (mask_and_one_0 x),
      crcBitStep_split _ (mask_parity_1 x),
      crcBitStep_split _ (mask_parity_2 x),
      crcBitStep_split _ (mask_parity_3 x),
      crcBitStep_split _ (mask_parity_4 x),
      crcBitStep_split _ (mask_parity_5 x),
      crcBitStep_split _ (mask_parity_6 x),
      crcBitStep_split _ (mask_parity_7 x),
      mask_shift8_fold x]

/-! ## Table lookup and the fold -/

private theorem crcTable_size : crcTable.size = 256 := by
  simp [crcTable]

private theorem crcTable_get (i : Nat) (h : i < 256) :
    crcTable[i]'(by rw [crcTable_size]; exact h) = crcStep8 (UInt32.ofNat i) := by
  simp [crcTable, Array.getElem_ofFn]

private theorem uint8_toUInt32_shiftRight8 (b : UInt8) : b.toUInt32 >>> 8 = 0 := by
  refine UInt32.toBitVec_inj.mp ?_
  ext i h
  simp

private theorem crc32Update_eq_crcByte (c : UInt32) (b : UInt8) :
    crc32Update c b = crcByte c b := by
  unfold crc32Update crcByte
  have hlt : ((c ^^^ b.toUInt32) &&& 0xFF).toNat < 256 := by
    rw [UInt32.toNat_and]
    have h255 : (0xFF : UInt32).toNat = 255 := rfl
    rw [h255]
    have := Nat.and_le_right (n := (c ^^^ b.toUInt32).toNat) (m := 255)
    omega
  rw [getElem!_pos crcTable _ (by rw [crcTable_size]; exact hlt)]
  rw [crcTable_get _ hlt, UInt32.ofNat_toNat]
  rw [crcStep8_split (c ^^^ b.toUInt32)]
  rw [shiftRight_xor, uint8_toUInt32_shiftRight8, UInt32.xor_zero]

theorem crc32_eq_spec (bs : List UInt8) : crc32 bs = crc32Spec bs := by
  unfold crc32 crc32Spec
  have h : crc32Update = crcByte :=
    funext fun c => funext fun b => crc32Update_eq_crcByte c b
  rw [h]

#guard crc32Spec [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xCBF43926
#guard crc32 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xCBF43926

end TarGz
