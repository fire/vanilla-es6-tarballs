-- SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
-- SPDX-License-Identifier: MIT

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

/-! ## Token codec

`LenOk`/`DistOk` are folded into the runtime-checked `TokUsable` predicate
below (checked by the encoder per token), so no universal theorem about the
symbol tables is needed — the same proof-carrying-runtime-check architecture
as `PrefixFree`. -/

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
    3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ d ∧ d ≤ 32768 ∧ LenOk len ∧ DistOk d ∧
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

/-! ## Token-stream round trip -/

theorem encodeSym_length_pos {codes : List (Nat × Nat)} {s : Nat}
    (hu : SymUsable codes s) : 1 ≤ (encodeSym codes s).length := by
  obtain ⟨hs, hne⟩ := hu
  rw [getElem!_pos codes s hs] at hne
  obtain ⟨⟨l, c⟩, he⟩ : ∃ p : Nat × Nat, codes[s] = p := ⟨codes[s], rfl⟩
  rw [he] at hne
  have hl : l ≠ 0 := by simpa using hne
  simp only [encodeSym, List.getElem?_eq_getElem hs, he]
  simp [msbBits_length]
  omega

theorem encodeTokens_length_ge {litC distC : List (Nat × Nat)} (toks : List Tok)
    (htu : ∀ t ∈ toks, TokUsable litC distC t) (heob : SymUsable litC 256) :
    toks.length + 1 ≤ (encodeTokens litC distC toks).length := by
  induction toks with
  | nil =>
    simp only [encodeTokens, List.flatMap_nil, List.nil_append, List.length_nil]
    have := encodeSym_length_pos heob
    omega
  | cons t ts ih =>
    have ht := htu t (by simp)
    have hts := ih fun x hx => htu x (by simp [hx])
    have h1 : 1 ≤ (encodeTok litC distC t).length := by
      match t with
      | Tok.lit b =>
        exact encodeSym_length_pos ht
      | Tok.ref len d =>
        obtain ⟨_, _, _, _, _, _, huL, _⟩ := ht
        have := encodeSym_length_pos huL
        simp only [encodeTok, List.length_append]
        omega
    simp only [encodeTokens, List.flatMap_cons, List.length_cons,
      List.length_append] at hts ⊢
    omega

theorem decodeTokens_encodeTokens {litC distC : List (Nat × Nat)}
    (hpfL : PrefixFree 15 litC) (hpfD : PrefixFree 15 distC)
    (heob : SymUsable litC 256) :
    ∀ (toks : List Tok) (out final : List UInt8) (r : BitStream) (fuel : Nat),
      (∀ t ∈ toks, TokUsable litC distC t) →
      resolve toks out = some final →
      toks.length + 1 ≤ fuel →
      decodeTokens litC distC fuel (encodeTokens litC distC toks ++ r) out
        = some (final, r) := by
  intro toks
  induction toks with
  | nil =>
    intro out final r fuel _ hres hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [resolve] at hres
    injection hres with hfin
    subst hfin
    simp only [encodeTokens, List.flatMap_nil, List.nil_append]
    simp only [decodeTokens]
    rw [decodeSym_encodeSym' hpfL heob]
    simp
  | cons t ts ih =>
    intro out final r fuel htu hres hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have ht := htu t (by simp)
    have hts : ∀ x ∈ ts, TokUsable litC distC x := fun x hx => htu x (by simp [hx])
    have hfuel' : ts.length + 1 ≤ f := by
      simp only [List.length_cons] at hfuel
      omega
    match t with
    | Tok.lit b =>
      rw [resolve_lit] at hres
      have hb : b.toNat < 256 := by
        have := UInt8.toNat_lt b
        simpa using this
      simp only [encodeTokens, List.flatMap_cons, encodeTok, List.append_assoc]
      simp only [decodeTokens]
      rw [decodeSym_encodeSym' hpfL ht]
      simp only []
      rw [if_neg (by omega : ¬ b.toNat = 256), if_pos hb, UInt8.ofNat_toNat]
      have := ih (out ++ [b]) final r f hts hres hfuel'
      simpa [encodeTokens, List.append_assoc] using this
    | Tok.ref len d =>
      obtain ⟨h3, h258, hd1, hd32, hlok, hdok, huL, huD⟩ := ht
      have hgt : 256 < (encodeLenSym len).1 := hlok.2.2.2
      rw [resolve_ref] at hres
      simp only [encodeTokens, List.flatMap_cons, encodeTok, List.append_assoc]
      simp only [decodeTokens]
      rw [decodeSym_encodeSym' hpfL huL]
      simp only []
      rw [if_neg (by omega : ¬ (encodeLenSym len).1 = 256),
        if_neg (by omega : ¬ (encodeLenSym len).1 < 256)]
      rw [hlok.1]
      simp only []
      rw [readBitsLE_append hlok.2.1]
      simp only []
      rw [decodeSym_encodeSym' hpfD huD]
      simp only []
      rw [hdok.1]
      simp only []
      rw [readBitsLE_append hdok.2.1]
      simp only []
      have hlen : len - (encodeLenSym len).2.2 + (encodeLenSym len).2.2 = len := by
        have := hlok.2.2.1
        omega
      have hdist : d - (encodeDistSym d).2.2 + (encodeDistSym d).2.2 = d := by
        have := hdok.2.2
        omega
      rw [hlen, hdist]
      split at hres
      · rename_i hcond
        rw [if_pos hcond]
        have := ih (lzCopy out d len) final r f hts hres hfuel'
        simpa [encodeTokens, List.append_assoc] using this
      · exact absurd hres (by simp)

/-! ## Dynamic block header (RFC 1951 §3.2.7)

All 19 CL code lengths are transmitted (HCLEN = 15) and the code-length
sequence is emitted with literal CL symbols only — legal DEFLATE, chosen to
keep the proof surface small. The decoder handles the full 16/17/18 RLE for
foreign streams. -/

def clOrder : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def writeDynHeader (litLens distLens clLens : List Nat)
    (clC : List (Nat × Nat)) : List Bool :=
  natBitsLE 5 (litLens.length - 257) ++ natBitsLE 5 (distLens.length - 1) ++
  natBitsLE 4 15 ++
  ((clOrder.map fun i => clLens[i]!).flatMap fun v => natBitsLE 3 v) ++
  ((litLens ++ distLens).flatMap fun v => encodeSym clC v)

/-- Read `k` 3-bit values. -/
def read3s : Nat → BitStream → Option (List Nat × BitStream)
  | 0, bits => some ([], bits)
  | k + 1, bits =>
    match readBitsLE 3 bits with
    | none => none
    | some (v, bits1) =>
      match read3s k bits1 with
      | none => none
      | some (vs, bits2) => some (v :: vs, bits2)

/-- Decode `need` code lengths with the full 16/17/18 RLE semantics. -/
def readClSeq (clC : List (Nat × Nat)) :
    Nat → BitStream → List Nat → Option (List Nat × BitStream)
  | 0, bits, acc => some (acc.reverse, bits)
  | need + 1, bits, acc =>
    match decodeSym clC 7 bits with
    | none => none
    | some (s, bits1) =>
      if s ≤ 15 then readClSeq clC need bits1 (s :: acc)
      else if s = 16 then
        match acc.head? with
        | none => none
        | some prevv =>
          match readBitsLE 2 bits1 with
          | none => none
          | some (k, bits2) =>
            if _h : k + 3 ≤ need + 1 then
              readClSeq clC (need + 1 - (k + 3)) bits2
                (List.replicate (k + 3) prevv ++ acc)
            else none
      else if s = 17 then
        match readBitsLE 3 bits1 with
        | none => none
        | some (k, bits2) =>
          if _h : k + 3 ≤ need + 1 then
            readClSeq clC (need + 1 - (k + 3)) bits2
              (List.replicate (k + 3) 0 ++ acc)
          else none
      else if s = 18 then
        match readBitsLE 7 bits1 with
        | none => none
        | some (k, bits2) =>
          if _h : k + 11 ≤ need + 1 then
            readClSeq clC (need + 1 - (k + 11)) bits2
              (List.replicate (k + 11) 0 ++ acc)
          else none
      else none
  termination_by need => need
  decreasing_by all_goals omega

def readDynHeader (bits : BitStream) :
    Option ((List Nat × List Nat) × BitStream) :=
  match readBitsLE 5 bits with
  | none => none
  | some (hlit, b1) =>
    match readBitsLE 5 b1 with
    | none => none
    | some (hdist, b2) =>
      match readBitsLE 4 b2 with
      | none => none
      | some (hclen, b3) =>
        match read3s (hclen + 4) b3 with
        | none => none
        | some (raw, b4) =>
          let clLens := raw.zipIdx.foldl
            (fun acc p => acc.set clOrder[p.2]! p.1) (List.replicate 19 0)
          match readClSeq (canonicalCodes 7 clLens)
              (hlit + 257 + (hdist + 1)) b4 [] with
          | none => none
          | some (combined, b5) =>
            some ((combined.take (hlit + 257), combined.drop (hlit + 257)), b5)

theorem read3s_append :
    ∀ (vs : List Nat) (r : BitStream), (∀ v ∈ vs, v < 8) →
      read3s vs.length ((vs.flatMap fun v => natBitsLE 3 v) ++ r) = some (vs, r) := by
  intro vs
  induction vs with
  | nil => intro r _; rfl
  | cons v t ih =>
    intro r hv
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc]
    simp only [read3s]
    rw [readBitsLE_append (show v < 2 ^ 3 from by have := hv v (by simp); simpa using this)]
    simp only []
    rw [ih r fun x hx => hv x (by simp [hx])]

theorem readClSeq_lits {clC : List (Nat × Nat)} (hpf : PrefixFree 7 clC) :
    ∀ (vals acc : List Nat) (r : BitStream),
      (∀ v ∈ vals, v ≤ 15 ∧ SymUsable clC v) →
      readClSeq clC vals.length ((vals.flatMap fun v => encodeSym clC v) ++ r) acc
        = some (acc.reverse ++ vals, r) := by
  intro vals
  induction vals with
  | nil => intro acc r _; simp [readClSeq]
  | cons v t ih =>
    intro acc r hv
    have hv1 := hv v (by simp)
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc]
    simp only [readClSeq]
    rw [decodeSym_encodeSym' hpf hv1.2]
    simp only []
    rw [if_pos hv1.1]
    rw [ih (v :: acc) r fun x hx => hv x (by simp [hx])]
    simp

private theorem cons_of_length_succ :
    ∀ (l : List Nat) (n : Nat), l.length = n + 1 →
      ∃ a t, l = a :: t ∧ t.length = n := by
  intro l n h
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

theorem readDynHeader_writeDynHeader
    (litLens distLens clLens : List Nat)
    (hlit : litLens.length = 286) (hdist : distLens.length = 30)
    (hcl : clLens.length = 19)
    (hclmax : ∀ v ∈ clLens, v ≤ 7)
    (hpfC : PrefixFree 7 (canonicalCodes 7 clLens))
    (hvals : ∀ v ∈ litLens ++ distLens,
      v ≤ 15 ∧ SymUsable (canonicalCodes 7 clLens) v)
    (r : BitStream) :
    readDynHeader
        (writeDynHeader litLens distLens clLens (canonicalCodes 7 clLens) ++ r)
      = some ((litLens, distLens), r) := by
  obtain ⟨a0, l, rfl, hcl⟩ := cons_of_length_succ clLens 18 (by omega)
  obtain ⟨a1, l, rfl, hcl⟩ := cons_of_length_succ l 17 (by omega)
  obtain ⟨a2, l, rfl, hcl⟩ := cons_of_length_succ l 16 (by omega)
  obtain ⟨a3, l, rfl, hcl⟩ := cons_of_length_succ l 15 (by omega)
  obtain ⟨a4, l, rfl, hcl⟩ := cons_of_length_succ l 14 (by omega)
  obtain ⟨a5, l, rfl, hcl⟩ := cons_of_length_succ l 13 (by omega)
  obtain ⟨a6, l, rfl, hcl⟩ := cons_of_length_succ l 12 (by omega)
  obtain ⟨a7, l, rfl, hcl⟩ := cons_of_length_succ l 11 (by omega)
  obtain ⟨a8, l, rfl, hcl⟩ := cons_of_length_succ l 10 (by omega)
  obtain ⟨a9, l, rfl, hcl⟩ := cons_of_length_succ l 9 (by omega)
  obtain ⟨a10, l, rfl, hcl⟩ := cons_of_length_succ l 8 (by omega)
  obtain ⟨a11, l, rfl, hcl⟩ := cons_of_length_succ l 7 (by omega)
  obtain ⟨a12, l, rfl, hcl⟩ := cons_of_length_succ l 6 (by omega)
  obtain ⟨a13, l, rfl, hcl⟩ := cons_of_length_succ l 5 (by omega)
  obtain ⟨a14, l, rfl, hcl⟩ := cons_of_length_succ l 4 (by omega)
  obtain ⟨a15, l, rfl, hcl⟩ := cons_of_length_succ l 3 (by omega)
  obtain ⟨a16, l, rfl, hcl⟩ := cons_of_length_succ l 2 (by omega)
  obtain ⟨a17, l, rfl, hcl⟩ := cons_of_length_succ l 1 (by omega)
  obtain ⟨a18, l, rfl, hcl⟩ := cons_of_length_succ l 0 (by omega)
  have hnil : l = [] := by
    cases l with
    | nil => rfl
    | cons a t => simp at hcl
  subst hnil
  -- the 19 raw 3-bit values in clOrder position order
  have hraw : (clOrder.map fun i =>
      ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
        a15, a16, a17, a18] : List Nat)[i]!)
      = [a16, a17, a18, a0, a8, a7, a9, a6, a10, a5, a11, a4, a12, a3, a13,
         a2, a14, a1, a15] := by
    simp [clOrder]
  have hbound : ∀ v ∈ [a16, a17, a18, a0, a8, a7, a9, a6, a10, a5, a11, a4,
      a12, a3, a13, a2, a14, a1, a15], v < 8 := by
    intro v hv
    have : v ∈ [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
        a14, a15, a16, a17, a18] := by
      simp at hv ⊢
      rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    have := hclmax v this
    omega
  simp only [writeDynHeader, hraw, hlit, hdist, List.append_assoc]
  simp only [readDynHeader]
  rw [readBitsLE_append (show 286 - 257 < 2 ^ 5 by decide)]
  simp only []
  rw [readBitsLE_append (show 30 - 1 < 2 ^ 5 by decide)]
  simp only []
  rw [readBitsLE_append (show 15 < 2 ^ 4 by decide)]
  simp only []
  rw [show (15 + 4 : Nat)
      = ([a16, a17, a18, a0, a8, a7, a9, a6, a10, a5, a11, a4, a12, a3, a13,
          a2, a14, a1, a15] : List Nat).length from by simp]
  rw [read3s_append _ _ hbound]
  simp only []
  -- the clOrder scatter rebuilds the original length list
  have hscatter :
      (([a16, a17, a18, a0, a8, a7, a9, a6, a10, a5, a11, a4, a12, a3, a13,
         a2, a14, a1, a15] : List Nat).zipIdx.foldl
        (fun acc p => acc.set clOrder[p.2]! p.1) (List.replicate 19 0))
      = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
         a15, a16, a17, a18] := by
    simp [clOrder, List.zipIdx, List.set]
  rw [hscatter]
  have hneed : (286 - 257 + 257 + (30 - 1 + 1) : Nat)
      = (litLens ++ distLens).length := by
    simp [hlit, hdist]
  rw [hneed]
  rw [readClSeq_lits hpfC (litLens ++ distLens) [] r hvals]
  simp only [List.reverse_nil, List.nil_append]
  have htake : (litLens ++ distLens).take (286 - 257 + 257) = litLens := by
    have : (286 - 257 + 257 : Nat) = litLens.length := by omega
    rw [this, List.take_left]
  have hdrop : (litLens ++ distLens).drop (286 - 257 + 257) = distLens := by
    have : (286 - 257 + 257 : Nat) = litLens.length := by omega
    rw [this, List.drop_left]
  rw [htake, hdrop]

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

/-- Fixed-Huffman code lengths (RFC 1951 §3.2.6); decode-side only. -/
def fixedLitLens : List Nat :=
  List.replicate 144 8 ++ List.replicate 112 9 ++
  List.replicate 24 7 ++ List.replicate 8 8

def fixedDistLens : List Nat := List.replicate 30 5

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
        else if btype = 1 then
          match decodeTokens (canonicalCodes 15 fixedLitLens)
              (canonicalCodes 15 fixedDistLens) (bits2.length + 1) bits2 out with
          | none => none
          | some (out', bits3) =>
            if bfinal = 1 then some (out', bits3)
            else inflateLoop fuel total bits3 out'
        else if btype = 2 then
          match readDynHeader bits2 with
          | none => none
          | some ((lLens, dLens), bits3) =>
            match decodeTokens (canonicalCodes 15 lLens)
                (canonicalCodes 15 dLens) (bits3.length + 1) bits3 out with
            | none => none
            | some (out', bits4) =>
              if bfinal = 1 then some (out', bits4)
              else inflateLoop fuel total bits4 out'
        else none

/-! ## Dynamic-block encoder with proof-carrying runtime validation -/

def bumpFreq (freqs : List Nat) (s : Nat) : List Nat :=
  freqs.set s (freqs[s]! + 1)

def tokenFreqs (toks : List Tok) : List Nat × List Nat :=
  toks.foldl
    (fun acc t =>
      match t with
      | Tok.lit b => (bumpFreq acc.1 b.toNat, acc.2)
      | Tok.ref len d =>
        (bumpFreq acc.1 (encodeLenSym len).1, bumpFreq acc.2 (encodeDistSym d).1))
    (List.replicate 286 0, List.replicate 30 0)

def clFreqs (vals : List Nat) : List Nat :=
  vals.foldl bumpFreq (List.replicate 19 0)

/-- The decidable validity bundle the encoder checks at runtime. When it
holds, the dynamic block round-trips (see `inflateLoop_dyn`); when the
heuristics ever produced something invalid, `deflate` falls back to stored
blocks — so the headline theorems are unconditional. -/
def DynOk (toks : List Tok) (litLens distLens clLens : List Nat) : Prop :=
  litLens.length = 286 ∧ distLens.length = 30 ∧ clLens.length = 19 ∧
  (∀ v ∈ clLens, v ≤ 7) ∧
  PrefixFree 15 (canonicalCodes 15 litLens) ∧
  PrefixFree 15 (canonicalCodes 15 distLens) ∧
  PrefixFree 7 (canonicalCodes 7 clLens) ∧
  SymUsable (canonicalCodes 15 litLens) 256 ∧
  (∀ t ∈ toks, TokUsable (canonicalCodes 15 litLens) (canonicalCodes 15 distLens) t) ∧
  (∀ v ∈ litLens ++ distLens, v ≤ 15 ∧ SymUsable (canonicalCodes 7 clLens) v)

instance (toks : List Tok) (litLens distLens clLens : List Nat) :
    Decidable (DynOk toks litLens distLens clLens) := by
  unfold DynOk
  infer_instance

def encodeBlockDyn (d : List UInt8) : Option (List Bool) :=
  let toks := tokenize d
  let fr := tokenFreqs toks
  let litLens := mkLengths 15 286 (bumpFreq fr.1 256)
  let distLens := mkLengths 15 30 fr.2
  let clLens := mkLengths 7 19 (clFreqs (litLens ++ distLens))
  if DynOk toks litLens distLens clLens then
    some (natBitsLE 1 1 ++ natBitsLE 2 2 ++
      writeDynHeader litLens distLens clLens (canonicalCodes 7 clLens) ++
      encodeTokens (canonicalCodes 15 litLens) (canonicalCodes 15 distLens) toks)
  else none

/-- Compress: one final dynamic-Huffman block, with a stored-block fallback
should the runtime validity check ever fail. -/
def deflate (d : List UInt8) : List UInt8 :=
  match encodeBlockDyn d with
  | some bits => bitsToBytes bits
  | none => bitsToBytes (encodeStored (storedChunks d))

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

/-- One dynamic block round-trips whenever the encoder's runtime check let it
through. -/
theorem inflateLoop_dyn (d : List UInt8) (bits : List Bool)
    (h : encodeBlockDyn d = some bits) (fuel total : Nat) (r : BitStream) :
    inflateLoop (fuel + 1) total (bits ++ r) [] = some (d, r) := by
  unfold encodeBlockDyn at h
  simp only [] at h
  split at h
  case isFalse => exact absurd h (by simp)
  case isTrue hdyn =>
    obtain ⟨h286, h30, h19, hclmax, hpfL, hpfD, hpfC, heob, htoks, hvals⟩ := hdyn
    injection h with h
    subst h
    simp only [List.append_assoc]
    simp only [inflateLoop]
    rw [readBitsLE_append (show 1 < 2 ^ 1 by decide)]
    simp only []
    rw [readBitsLE_append (show 2 < 2 ^ 2 by decide)]
    simp only []
    rw [readDynHeader_writeDynHeader _ _ _ h286 h30 h19 hclmax hpfC hvals]
    simp only []
    have hfuel : (tokenize d).length + 1
        ≤ (encodeTokens (canonicalCodes 15 (mkLengths 15 286 (bumpFreq (tokenFreqs (tokenize d)).1 256)))
            (canonicalCodes 15 (mkLengths 15 30 (tokenFreqs (tokenize d)).2))
            (tokenize d) ++ r).length + 1 := by
      have := encodeTokens_length_ge (tokenize d) htoks heob
      simp only [List.length_append]
      omega
    rw [decodeTokens_encodeTokens hpfL hpfD heob (tokenize d) [] d r _
      htoks (resolve_tokenize d) hfuel]
    simp only []
    rfl

/-- Shared wrapper: byte-level `inflate` of a packed bit stream plus trailer,
given the loop result on the exact instance the wrapper produces. -/
theorem inflate_bitsToBytes (d : List UInt8) (enc : List Bool)
    (trailer : List UInt8)
    (hloop : ∀ r : BitStream,
      inflateLoop ((enc ++ r).length + 1) (enc ++ r).length (enc ++ r) []
        = some (d, r)) :
    inflate (bitsToBytes enc ++ trailer) = some (d, trailer) := by
  unfold inflate
  simp only [bytesToBits_append, bytesToBits_bitsToBytes, List.append_assoc]
  rw [hloop (List.replicate ((8 - enc.length % 8) % 8) false ++ bytesToBits trailer)]
  simp only []
  have hconsumed :
      ((enc ++ (List.replicate ((8 - enc.length % 8) % 8) false
          ++ bytesToBits trailer)).length
        - (List.replicate ((8 - enc.length % 8) % 8) false
          ++ bytesToBits trailer).length + 7) / 8
      = (bitsToBytes enc).length := by
    rw [bitsToBytes_length]
    simp only [List.length_append]
    omega
  rw [hconsumed]
  rw [List.drop_left]

/-- Headline: decompressing a compressed stream with anything appended yields
the payload and exactly the appended bytes — dynamic block or stored
fallback alike. -/
theorem inflate_deflate_append (d trailer : List UInt8) :
    inflate (deflate d ++ trailer) = some (d, trailer) := by
  unfold deflate
  cases hdyn : encodeBlockDyn d with
  | some bits =>
    simp only []
    apply inflate_bitsToBytes
    intro r
    exact inflateLoop_dyn d bits hdyn (bits ++ r).length (bits ++ r).length r
  | none =>
    simp only []
    apply inflate_bitsToBytes
    intro r
    have hloop := inflateLoop_encodeStored (storedChunks d)
      ((encodeStored (storedChunks d) ++ r).length + 1)
      ((encodeStored (storedChunks d) ++ r).length)
      [] r
      (storedChunks_ne_nil d) (storedChunks_le d)
      (by
        have := encodeStored_length_ge (storedChunks d)
        simp only [List.length_append]
        omega)
      (by omega)
      (by omega)
    simpa [storedChunks_flatten] using hloop

end TarGz
