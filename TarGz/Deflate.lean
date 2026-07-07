import TarGz.Huffman
import TarGz.HuffLen
import TarGz.Lz77

/-!
# DEFLATE (RFC 1951)

This milestone: stored (uncompressed) blocks and the block-dispatch loop.
Fixed- and dynamic-Huffman branches land on top of the same loop.

The decoder tracks its absolute bit position as `total - bits.length`
(`total` = length of the whole stream), so the stored-block byte alignment is
pure length arithmetic and the parser stays in leftover style.
-/

namespace TarGz

/-! ## Length/distance symbol coding (RFC 1951 §3.2.5) -/

/-- (symbol, base, extraBits) for match lengths 3..258. -/
def lenTable : List (Nat × Nat × Nat) :=
  [(257, 3, 0), (258, 4, 0), (259, 5, 0), (260, 6, 0), (261, 7, 0), (262, 8, 0),
   (263, 9, 0), (264, 10, 0), (265, 11, 1), (266, 13, 1), (267, 15, 1), (268, 17, 1),
   (269, 19, 2), (270, 23, 2), (271, 27, 2), (272, 31, 2), (273, 35, 3), (274, 43, 3),
   (275, 51, 3), (276, 59, 3), (277, 67, 4), (278, 83, 4), (279, 99, 4), (280, 115, 4),
   (281, 131, 5), (282, 163, 5), (283, 195, 5), (284, 227, 5), (285, 258, 0)]

/-- (symbol, base, extraBits) for match distances 1..32768. -/
def distTable : List (Nat × Nat × Nat) :=
  [(0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 4, 0), (4, 5, 1), (5, 7, 1), (6, 9, 2),
   (7, 13, 2), (8, 17, 3), (9, 25, 3), (10, 33, 4), (11, 49, 4), (12, 65, 5),
   (13, 97, 5), (14, 129, 6), (15, 193, 6), (16, 257, 7), (17, 385, 7), (18, 513, 8),
   (19, 769, 8), (20, 1025, 9), (21, 1537, 9), (22, 2049, 10), (23, 3073, 10),
   (24, 4097, 11), (25, 6145, 11), (26, 8193, 12), (27, 12289, 12), (28, 16385, 13),
   (29, 24577, 13)]

/-- length → (symbol, extraBits, extraVal). -/
def encodeLenSym (len : Nat) : Nat × Nat × Nat :=
  if len = 258 then (285, 0, 0)
  else
    match lenTable.find? fun e => e.2.1 ≤ len && len < e.2.1 + 2 ^ e.2.2 with
    | some e => (e.1, e.2.2, len - e.2.1)
    | none => (0, 0, 0)

/-- distance → (symbol, extraBits, extraVal). -/
def encodeDistSym (d : Nat) : Nat × Nat × Nat :=
  match distTable.find? fun e => e.2.1 ≤ d && d < e.2.1 + 2 ^ e.2.2 with
  | some e => (e.1, e.2.2, d - e.2.1)
  | none => (0, 0, 0)

def lenSymBase (sym : Nat) : Option (Nat × Nat) :=
  (lenTable.find? fun e => e.1 == sym).map fun e => (e.2.1, e.2.2)

def distSymBase (sym : Nat) : Option (Nat × Nat) :=
  (distTable.find? fun e => e.1 == sym).map fun e => (e.2.1, e.2.2)

/-- Everything the decoder-side round trip needs from the length coding. -/
def LenOk (len : Nat) : Prop :=
  lenSymBase (encodeLenSym len).1
      = some (len - (encodeLenSym len).2.2, (encodeLenSym len).2.1) ∧
    (encodeLenSym len).2.2 < 2 ^ (encodeLenSym len).2.1 ∧
    (encodeLenSym len).2.2 ≤ len ∧ 256 < (encodeLenSym len).1

instance (len : Nat) : Decidable (LenOk len) := by unfold LenOk; infer_instance

def DistOk (d : Nat) : Prop :=
  distSymBase (encodeDistSym d).1
      = some (d - (encodeDistSym d).2.2, (encodeDistSym d).2.1) ∧
    (encodeDistSym d).2.2 < 2 ^ (encodeDistSym d).2.1 ∧
    (encodeDistSym d).2.2 ≤ d

instance (d : Nat) : Decidable (DistOk d) := by unfold DistOk; infer_instance

set_option maxRecDepth 8192 in
theorem lenOk_all : ∀ len, 3 ≤ len → len ≤ 258 → LenOk len := by
  have h : ∀ i : Fin 256, LenOk (i.val + 3) := by decide
  intro len h3 h258
  have := h ⟨len - 3, by omega⟩
  simpa [show len - 3 + 3 = len from by omega] using this

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem distOk_all : ∀ d, 1 ≤ d → d ≤ 32768 → DistOk d := by
  have h : ∀ i : Fin 32768, DistOk (i.val + 1) := by decide
  intro d h1 h32
  have := h ⟨d - 1, by omega⟩
  simpa [show d - 1 + 1 = d from by omega] using this

/-! ## Token codec -/

/-- Symbol is present and used in a code assignment. -/
def SymUsable (codes : List (Nat × Nat)) (s : Nat) : Prop :=
  s < codes.length ∧ (codes[s]!).1 ≠ 0

instance (codes : List (Nat × Nat)) (s : Nat) : Decidable (SymUsable codes s) := by
  unfold SymUsable; infer_instance

theorem decodeSym_encodeSym' {maxLen : Nat} {codes : List (Nat × Nat)} {s : Nat}
    (hpf : PrefixFree maxLen codes) (hu : SymUsable codes s) (r : BitStream) :
    decodeSym codes maxLen (encodeSym codes s ++ r) = some (s, r) := by
  refine decodeSym_encodeSym hpf hu.1 ?_ r
  have h2 := hu.2
  rwa [getElem!_pos codes s hu.1] at h2

def encodeTok (litC distC : List (Nat × Nat)) : Tok → List Bool
  | Tok.lit b => encodeSym litC b.toNat
  | Tok.ref len d =>
    encodeSym litC (encodeLenSym len).1
      ++ natBitsLE (encodeLenSym len).2.1 (encodeLenSym len).2.2
      ++ encodeSym distC (encodeDistSym d).1
      ++ natBitsLE (encodeDistSym d).2.1 (encodeDistSym d).2.2

def encodeTokens (litC distC : List (Nat × Nat)) (toks : List Tok) : List Bool :=
  toks.flatMap (encodeTok litC distC) ++ encodeSym litC 256

def TokUsable (litC distC : List (Nat × Nat)) : Tok → Prop
  | Tok.lit b => SymUsable litC b.toNat
  | Tok.ref len d =>
    3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ d ∧ d ≤ 32768 ∧
    SymUsable litC (encodeLenSym len).1 ∧ SymUsable distC (encodeDistSym d).1

instance (litC distC : List (Nat × Nat)) (t : Tok) :
    Decidable (TokUsable litC distC t) := by
  cases t <;> (unfold TokUsable; infer_instance)

/-- Decode Huffman-coded tokens until end-of-block, replaying `lzCopy` with
the same validity conditions as `resolve`. -/
def decodeTokens (litC distC : List (Nat × Nat)) :
    Nat → BitStream → List UInt8 → Option (List UInt8 × BitStream)
  | 0, _, _ => none
  | fuel + 1, bits, out =>
    match decodeSym litC 15 bits with
    | none => none
    | some (sym, bits1) =>
      if sym = 256 then some (out, bits1)
      else if sym < 256 then
        decodeTokens litC distC fuel bits1 (out ++ [UInt8.ofNat sym])
      else
        match lenSymBase sym with
        | none => none
        | some (base, extra) =>
          match readBitsLE extra bits1 with
          | none => none
          | some (ev, bits2) =>
            match decodeSym distC 15 bits2 with
            | none => none
            | some (dsym, bits3) =>
              match distSymBase dsym with
              | none => none
              | some (dbase, dextra) =>
                match readBitsLE dextra bits3 with
                | none => none
                | some (dv, bits4) =>
                  if 1 ≤ dbase + dv ∧ dbase + dv ≤ out.length ∧
                      dbase + dv ≤ 32768 ∧ 3 ≤ base + ev ∧ base + ev ≤ 258 then
                    decodeTokens litC distC fuel bits4
                      (lzCopy out (dbase + dv) (base + ev))
                  else none

/-- Split into stored-block payload chunks (each ≤ 65535 bytes, ≥ 1 chunk). -/
def storedChunks (l : List UInt8) : List (List UInt8) :=
  if _h : l.length ≤ 65535 then [l]
  else l.take 65535 :: storedChunks (l.drop 65535)
  termination_by l.length
  decreasing_by simp; omega

/-- One stored block: BFINAL, BTYPE=00, 5 pad bits (blocks are emitted
byte-aligned by construction), LEN, NLEN (ones' complement), raw bytes. -/
def encodeStoredBlock (final : Bool) (chunk : List UInt8) : List Bool :=
  natBitsLE 1 (if final then 1 else 0) ++ natBitsLE 2 0 ++ natBitsLE 5 0 ++
  natBitsLE 16 chunk.length ++ natBitsLE 16 (65535 - chunk.length) ++
  chunk.flatMap fun b => natBitsLE 8 b.toNat

def encodeStored : List (List UInt8) → List Bool
  | [] => []
  | [c] => encodeStoredBlock true c
  | c :: c' :: cs => encodeStoredBlock false c ++ encodeStored (c' :: cs)

/-- Read `n` raw bytes from the (byte-aligned) bit stream. -/
def readStoredBody : Nat → BitStream → Option (List UInt8 × BitStream)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
    match readBitsLE 8 bits with
    | none => none
    | some (v, rest) =>
      match readStoredBody n rest with
      | none => none
      | some (chunk, rest2) => some (UInt8.ofNat v :: chunk, rest2)

/-- Block loop. `total` is the bit length of the whole stream, so the current
absolute bit position is `total - bits.length`. Returns (payload, leftover
bits) after the final block. -/
def inflateLoop : Nat → Nat → BitStream → List UInt8 →
    Option (List UInt8 × BitStream)
  | 0, _, _, _ => none
  | fuel + 1, total, bits, out =>
    match readBitsLE 1 bits with
    | none => none
    | some (bfinal, bits1) =>
      match readBitsLE 2 bits1 with
      | none => none
      | some (btype, bits2) =>
        if btype = 0 then
          match readBitsLE ((8 - (total - bits2.length) % 8) % 8) bits2 with
          | none => none
          | some (_, bits3) =>
            match readBitsLE 16 bits3 with
            | none => none
            | some (len, bits4) =>
              match readBitsLE 16 bits4 with
              | none => none
              | some (nlen, bits5) =>
                if nlen ≠ 65535 - len then none
                else
                  match readStoredBody len bits5 with
                  | none => none
                  | some (chunk, bits6) =>
                    if bfinal = 1 then some (out ++ chunk, bits6)
                    else inflateLoop fuel total bits6 (out ++ chunk)
        else none  -- BTYPE 01/10 (fixed/dynamic) land in a later milestone

/-- Compress. (This milestone: stored blocks only; the dynamic-Huffman
encoder replaces this definition later, keeping stored as its fallback.) -/
def deflate (d : List UInt8) : List UInt8 :=
  bitsToBytes (encodeStored (storedChunks d))

/-- Decompress; returns the payload and the remaining input bytes after the
final block (the deflate stream always ends on a byte boundary here). -/
def inflate (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let bits := bytesToBits bs
  match inflateLoop (bits.length + 1) bits.length bits [] with
  | none => none
  | some (out, rest) =>
    some (out, bs.drop ((bits.length - rest.length + 7) / 8))

/-! ## Stored-block round trip -/

theorem storedChunks_flatten (l : List UInt8) : (storedChunks l).flatten = l := by
  fun_induction storedChunks l with
  | case1 l h => simp
  | case2 l h ih => simp [ih]

theorem storedChunks_le (l : List UInt8) :
    ∀ c ∈ storedChunks l, c.length ≤ 65535 := by
  fun_induction storedChunks l with
  | case1 l h => simp; omega
  | case2 l h ih =>
    intro c hc
    simp at hc
    rcases hc with hc | hc
    · subst hc
      simp
      omega
    · exact ih c hc

theorem storedChunks_ne_nil (l : List UInt8) : storedChunks l ≠ [] := by
  fun_induction storedChunks l with
  | case1 l h => simp
  | case2 l h ih => simp

private theorem sum_map_const8 (chunk : List UInt8) :
    (chunk.map fun _ => (8 : Nat)).sum = 8 * chunk.length := by
  induction chunk with
  | nil => rfl
  | cons b t ih => simp [ih]; omega

theorem encodeStoredBlock_length (final : Bool) (chunk : List UInt8) :
    (encodeStoredBlock final chunk).length = 40 + 8 * chunk.length := by
  simp [encodeStoredBlock, sum_map_const8]
  omega

theorem readStoredBody_append (chunk : List UInt8) (r : BitStream) :
    readStoredBody chunk.length
      ((chunk.flatMap fun b => natBitsLE 8 b.toNat) ++ r) = some (chunk, r) := by
  induction chunk with
  | nil => rfl
  | cons b t ih =>
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc]
    have hb : b.toNat < 2 ^ 8 := by
      have := UInt8.toNat_lt b
      simpa using this
    simp only [readStoredBody, readBitsLE_append hb, ih, UInt8.ofNat_toNat]

/-- Decoding one emitted stored block: consumes exactly the block, appends its
chunk, and either stops (final) or hands the tail to the loop. -/
private theorem inflateLoop_stored_step (final : Bool) (c : List UInt8)
    (rest : BitStream) (fuel total : Nat) (out : List UInt8)
    (hc : c.length ≤ 65535)
    (hlen : (encodeStoredBlock final c ++ rest).length ≤ total)
    (halign : (total - (encodeStoredBlock final c ++ rest).length) % 8 = 0) :
    inflateLoop (fuel + 1) total (encodeStoredBlock final c ++ rest) out =
      if final then some (out ++ c, rest)
      else inflateLoop fuel total rest (out ++ c) := by
  have H : (encodeStoredBlock final c ++ rest).length
      = 40 + 8 * c.length + rest.length := by
    simp [encodeStoredBlock_length]
  rw [H] at hlen halign
  simp only [encodeStoredBlock, List.append_assoc]
  simp only [inflateLoop]
  have hfin : (if final then 1 else 0) < 2 ^ 1 := by
    cases final <;> decide
  rw [readBitsLE_append hfin]
  simp only []
  rw [readBitsLE_append (show 0 < 2 ^ 2 by decide)]
  simp only []
  have hlen2 : (natBitsLE 5 0 ++ (natBitsLE 16 c.length ++
      (natBitsLE 16 (65535 - c.length) ++
        ((c.flatMap fun b => natBitsLE 8 b.toNat) ++ rest)))).length
      = 37 + 8 * c.length + rest.length := by
    simp [sum_map_const8]
    omega
  rw [hlen2]
  have hpad : (8 - (total - (37 + 8 * c.length + rest.length)) % 8) % 8 = 5 := by
    omega
  rw [hpad]
  rw [readBitsLE_append (show 0 < 2 ^ 5 by decide)]
  simp only []
  rw [readBitsLE_append (show c.length < 2 ^ 16 by omega)]
  simp only []
  rw [readBitsLE_append (show 65535 - c.length < 2 ^ 16 by omega)]
  simp only []
  rw [if_neg (show ¬(65535 - c.length ≠ 65535 - c.length) from fun h => h rfl)]
  rw [readStoredBody_append]
  cases final with
  | false => simp
  | true => simp

theorem encodeStored_length_ge (cs : List (List UInt8)) :
    cs.length ≤ (encodeStored cs).length := by
  fun_induction encodeStored cs with
  | case1 => simp
  | case2 c =>
    simp [encodeStoredBlock_length]
    omega
  | case3 c c' cs ih =>
    simp only [List.length_cons, List.length_append, encodeStoredBlock_length] at *
    omega

theorem inflateLoop_encodeStored (cs : List (List UInt8)) :
    ∀ (fuel total : Nat) (out : List UInt8) (r : BitStream),
      cs ≠ [] →
      (∀ c ∈ cs, c.length ≤ 65535) →
      cs.length ≤ fuel →
      (encodeStored cs ++ r).length ≤ total →
      (total - (encodeStored cs ++ r).length) % 8 = 0 →
      inflateLoop fuel total (encodeStored cs ++ r) out
        = some (out ++ cs.flatten, r) := by
  induction cs with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons c cs ih =>
    intro fuel total out r _ hbound hfuel hlen halign
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := by
      refine ⟨fuel - 1, ?_⟩
      simp only [List.length_cons] at hfuel
      omega
    cases cs with
    | nil =>
      rw [show encodeStored [c] = encodeStoredBlock true c from rfl] at hlen halign ⊢
      rw [inflateLoop_stored_step true c r f total out (hbound c (by simp)) hlen halign]
      simp
    | cons c' cs' =>
      rw [show encodeStored (c :: c' :: cs')
          = encodeStoredBlock false c ++ encodeStored (c' :: cs') from rfl]
        at hlen halign ⊢
      rw [List.append_assoc] at hlen halign ⊢
      rw [inflateLoop_stored_step false c _ f total out (hbound c (by simp)) hlen halign]
      simp only [Bool.false_eq_true, if_false]
      rw [ih f total (out ++ c) r (by simp)
        (fun x hx => hbound x (by simp [hx]))
        (by simp only [List.length_cons] at hfuel ⊢; omega)
        (by
          simp only [List.length_append, encodeStoredBlock_length] at hlen ⊢
          omega)
        (by
          simp only [List.length_append, encodeStoredBlock_length] at halign hlen ⊢
          omega)]
      simp

/-- Interim headline (stored blocks): decompressing a compressed stream with
anything appended yields the payload and exactly the appended bytes. -/
theorem inflate_deflate_append (d trailer : List UInt8) :
    inflate (deflate d ++ trailer) = some (d, trailer) := by
  unfold inflate deflate
  simp only [bytesToBits_append, bytesToBits_bitsToBytes, List.append_assoc]
  have hloop := inflateLoop_encodeStored (storedChunks d)
    ((encodeStored (storedChunks d)
        ++ (List.replicate ((8 - (encodeStored (storedChunks d)).length % 8) % 8) false
        ++ bytesToBits trailer)).length + 1)
    ((encodeStored (storedChunks d)
        ++ (List.replicate ((8 - (encodeStored (storedChunks d)).length % 8) % 8) false
        ++ bytesToBits trailer)).length)
    []
    (List.replicate ((8 - (encodeStored (storedChunks d)).length % 8) % 8) false
        ++ bytesToBits trailer)
    (storedChunks_ne_nil d) (storedChunks_le d)
    (by
      have := encodeStored_length_ge (storedChunks d)
      simp only [List.length_append]
      omega)
    (by omega)
    (by omega)
  rw [hloop]
  simp only [List.nil_append, storedChunks_flatten]
  have hconsumed :
      ((encodeStored (storedChunks d)
          ++ (List.replicate ((8 - (encodeStored (storedChunks d)).length % 8) % 8) false
          ++ bytesToBits trailer)).length
        - (List.replicate ((8 - (encodeStored (storedChunks d)).length % 8) % 8) false
          ++ bytesToBits trailer).length + 7) / 8
      = (bitsToBytes (encodeStored (storedChunks d))).length := by
    rw [bitsToBytes_length]
    simp only [List.length_append]
    omega
  rw [hconsumed]
  rw [List.drop_left]

end TarGz
