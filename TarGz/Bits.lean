/-!
# LSB-first bit layer for DEFLATE

DEFLATE (RFC 1951 §3.1.1) packs data elements into bytes starting from the
least significant bit. Huffman codewords are the exception: they are packed
starting from the most significant bit of the code (`msbBits`).

The bit stream is modeled as `List Bool`. Encoders emit bit lists; decoders
follow the parser-with-leftover discipline `input → Option (value × rest)`,
so every round-trip lemma has the compositional shape
`decode (encode x ++ rest) = some (x, rest)`.
-/

namespace TarGz

abbrev BitStream := List Bool

/-- Numeric value of an LSB-first bit list. -/
def bitsVal : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsVal bs + b.toNat

/-- The `k` low bits of `n`, least significant first. -/
def natBitsLE : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: natBitsLE k (n / 2)

/-- Read `k` bits (LSB first) as a number. -/
def readBitsLE : Nat → BitStream → Option (Nat × BitStream)
  | 0, bits => some (0, bits)
  | _ + 1, [] => none
  | k + 1, b :: bits =>
    (readBitsLE k bits).map fun (n, rest) => (2 * n + b.toNat, rest)

/-- `len` bits of `code`, most significant first (Huffman codewords). -/
def msbBits : Nat → Nat → List Bool
  | 0, _ => []
  | l + 1, code => (code / 2 ^ l % 2 == 1) :: msbBits l code

/-- 8 bits of a byte, LSB first. -/
def byteToBits (b : UInt8) : List Bool := natBitsLE 8 b.toNat

def bytesToBits (bs : List UInt8) : List Bool := bs.flatMap byteToBits

/-- Pack bits into bytes, zero-padding the final partial byte. -/
def bitsToBytes : List Bool → List UInt8
  | [] => []
  | b :: bs =>
    UInt8.ofNat (bitsVal ((b :: bs).take 8)) :: bitsToBytes ((b :: bs).drop 8)
  termination_by l => l.length
  decreasing_by simp; omega

def writeLE16 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256)]

def readLE16 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: rest => some (a.toNat + 256 * b.toNat, rest)
  | _ => none

def writeLE32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
   UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256)]

def readLE32 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest =>
    some (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat, rest)
  | _ => none

/-! ## Lengths -/

@[simp] theorem natBitsLE_length (k n : Nat) : (natBitsLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [natBitsLE, ih]

@[simp] theorem msbBits_length (l code : Nat) : (msbBits l code).length = l := by
  induction l generalizing code with
  | zero => rfl
  | succ l ih => simp [msbBits, ih]

@[simp] theorem byteToBits_length (b : UInt8) : (byteToBits b).length = 8 := by
  simp [byteToBits]

@[simp] theorem bytesToBits_nil : bytesToBits [] = [] := rfl

@[simp] theorem bytesToBits_cons (b : UInt8) (bs : List UInt8) :
    bytesToBits (b :: bs) = byteToBits b ++ bytesToBits bs := by
  simp [bytesToBits]

@[simp] theorem bytesToBits_append (a b : List UInt8) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits]

@[simp] theorem bytesToBits_length (bs : List UInt8) :
    (bytesToBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b t ih => simp [ih]; omega

theorem bitsToBytes_length (l : List Bool) :
    (bitsToBytes l).length = (l.length + 7) / 8 := by
  fun_induction bitsToBytes l with
  | case1 => rfl
  | case2 b bs ih =>
    simp only [List.length_cons, ih, List.length_drop]
    omega

/-! ## Round trips -/

@[simp] theorem natBitsLE_zero_val (k : Nat) :
    natBitsLE k 0 = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [natBitsLE, ih, List.replicate_succ]

/-- The workhorse: every fixed-width LSB-first field round-trips. -/
theorem readBitsLE_append {k n : Nat} {r : BitStream} (h : n < 2 ^ k) :
    readBitsLE k (natBitsLE k n ++ r) = some (n, r) := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst this
    rfl
  | succ k ih =>
    have h2 : n / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at h
      omega
    simp only [natBitsLE, List.cons_append, readBitsLE, ih h2, Option.map_some]
    have : 2 * (n / 2) + ((n % 2 == 1) : Bool).toNat = n := by
      rcases Nat.mod_two_eq_zero_or_one n with h1 | h1 <;> simp [h1] <;> omega
    rw [this]

theorem bitsVal_lt (l : List Bool) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal]
  | cons b t ih =>
    simp only [bitsVal, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem natBitsLE_bitsVal {k : Nat} {l : List Bool} (h : l.length ≤ k) :
    natBitsLE k (bitsVal l) = l ++ List.replicate (k - l.length) false := by
  induction l generalizing k with
  | nil => simp [bitsVal]
  | cons b t ih =>
    match k with
    | 0 => simp at h
    | k + 1 =>
      simp only [bitsVal, natBitsLE, List.length_cons, List.cons_append,
        Nat.succ_sub_succ]
      have hmod : (2 * bitsVal t + b.toNat) % 2 = b.toNat := by
        cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      have hdiv : (2 * bitsVal t + b.toNat) / 2 = bitsVal t := by
        cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      have hb : ((2 * bitsVal t + b.toNat) % 2 == 1) = b := by
        rw [hmod]; cases b <;> rfl
      have ht : t.length ≤ k := by
        simp only [List.length_cons] at h; omega
      rw [hb, hdiv, ih ht]

/-- A byte built from at most 8 bits unpacks to those bits plus zero padding. -/
theorem byteToBits_ofNat_bitsVal {l : List Bool} (h : l.length ≤ 8) :
    byteToBits (UInt8.ofNat (bitsVal l)) = l ++ List.replicate (8 - l.length) false := by
  have hval : bitsVal l < 256 := by
    have h1 := bitsVal_lt l
    have h2 : (2 : Nat) ^ l.length ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) h
    have h3 : (2 : Nat) ^ 8 = 256 := rfl
    omega
  have hto : (UInt8.ofNat (bitsVal l)).toNat = bitsVal l := by simp; omega
  simp only [byteToBits]
  rw [hto, natBitsLE_bitsVal h]

/-- Unpacking after packing appends only zero padding to the next byte. -/
theorem bytesToBits_bitsToBytes (l : List Bool) :
    bytesToBits (bitsToBytes l) = l ++ List.replicate ((8 - l.length % 8) % 8) false := by
  fun_induction bitsToBytes l with
  | case1 => rfl
  | case2 b bs ih =>
    by_cases hc : (b :: bs).length ≤ 8
    · -- final (possibly partial) byte; the recursive call is on []
      rw [List.take_of_length_le hc, List.drop_eq_nil_of_le hc]
      simp only [bitsToBytes, bytesToBits_cons, bytesToBits_nil, List.append_nil]
      rw [byteToBits_ofNat_bitsVal hc]
      have hcount : 8 - (b :: bs).length = (8 - (b :: bs).length % 8) % 8 := by
        have hc' : (b :: bs).length = bs.length + 1 := List.length_cons ..
        rw [hc'] at hc ⊢
        omega
      rw [hcount]
    · -- a full byte was cut off the front
      have htake8 : ((b :: bs).take 8).length ≤ 8 := by
        simp only [List.length_take]
        omega
      simp only [bytesToBits_cons]
      rw [ih, byteToBits_ofNat_bitsVal htake8]
      have h8 : ((b :: bs).take 8).length = 8 := by
        simp only [List.length_take]
        omega
      rw [h8, Nat.sub_self, List.replicate_zero, List.append_nil,
        ← List.append_assoc, List.take_append_drop]
      have hcnt : ((b :: bs).drop 8).length % 8 = (b :: bs).length % 8 := by
        rw [List.length_drop]
        omega
      rw [hcnt]

theorem readLE16_writeLE16 {n : Nat} {r : List UInt8} (h : n < 2 ^ 16) :
    readLE16 (writeLE16 n ++ r) = some (n, r) := by
  simp [writeLE16, readLE16]
  omega

theorem readLE32_writeLE32 {n : Nat} {r : List UInt8} (h : n < 2 ^ 32) :
    readLE32 (writeLE32 n ++ r) = some (n, r) := by
  simp [writeLE32, readLE32]
  omega

end TarGz
