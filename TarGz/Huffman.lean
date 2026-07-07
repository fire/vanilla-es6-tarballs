import TarGz.Bits

/-!
# Canonical Huffman codes (RFC 1951 §3.2.2)

A code assignment is a positional list `codes : List (Nat × Nat)` — entry `s`
is `(len, code)` for symbol `s`, with `len = 0` marking an unused symbol.

* `canonicalCodes` builds the RFC 1951 canonical assignment from code lengths.
* `PrefixFree` is the decidable validity predicate the encoder checks at
  runtime (carrying the proof into the round trip), so the headline theorems
  do not depend on `canonicalCodes`' internals.
* `decodeSym_encodeSym` is the generic round trip for ANY prefix-free
  assignment.
-/

namespace TarGz

/-- `p` is a numeric bit-prefix of `q` (codewords read MSB-first). -/
def NumPrefix (p q : Nat × Nat) : Prop :=
  p.1 ≤ q.1 ∧ q.2 / 2 ^ (q.1 - p.1) = p.2

instance : DecidablePred fun pq : (Nat × Nat) × (Nat × Nat) => NumPrefix pq.1 pq.2 :=
  fun _ => by unfold NumPrefix; infer_instance

/-- Validity of a code assignment: used codes fit their length, lengths are
bounded by `maxLen`, and no used codeword is a bit-prefix of another
(which also rules out duplicates, since every pair is a prefix of itself). -/
def PrefixFree (maxLen : Nat) (codes : List (Nat × Nat)) : Prop :=
  (∀ p ∈ codes, p.1 ≠ 0 → p.1 ≤ maxLen ∧ p.2 < 2 ^ p.1) ∧
  (∀ i, (hi : i < codes.length) → ∀ j, (hj : j < codes.length) → i ≠ j →
    (codes[i]).1 ≠ 0 → (codes[j]).1 ≠ 0 → ¬ NumPrefix codes[i] codes[j])

instance (maxLen : Nat) (codes : List (Nat × Nat)) :
    Decidable (PrefixFree maxLen codes) := by
  unfold PrefixFree NumPrefix
  infer_instance

/-- Emit the codeword for symbol `s` (empty for unknown/unused symbols;
the encoder only calls this under a `PrefixFree` check plus usage evidence). -/
def encodeSym (codes : List (Nat × Nat)) (s : Nat) : List Bool :=
  match codes[s]? with
  | some (l, c) => msbBits l c
  | none => []

/-- First symbol whose entry is exactly `(len, code)`. -/
def findSym : List (Nat × Nat) → Nat → Nat → Option Nat
  | [], _, _ => none
  | p :: rest, len, code =>
    if p.1 = len ∧ p.2 = code then some 0
    else (findSym rest len code).map (· + 1)

/-- Bit-by-bit canonical decode: consume a bit, extend the accumulator
MSB-first, look the `(depth, acc)` pair up, recurse until `maxLen`. -/
def decodeSymAux (codes : List (Nat × Nat)) (maxLen : Nat) :
    Nat → Nat → BitStream → Option (Nat × BitStream)
  | k, acc, bits =>
    if _hk : maxLen ≤ k then none
    else match bits with
      | [] => none
      | b :: rest =>
        let acc' := 2 * acc + b.toNat
        match findSym codes (k + 1) acc' with
        | some s => some (s, rest)
        | none => decodeSymAux codes maxLen (k + 1) acc' rest
  termination_by k _ _ => maxLen - k
  decreasing_by omega

def decodeSym (codes : List (Nat × Nat)) (maxLen : Nat) (bits : BitStream) :
    Option (Nat × BitStream) :=
  decodeSymAux codes maxLen 0 0 bits

/-! ## Canonical construction from code lengths -/

/-- Assign codes to `(len, idx)` pairs sorted by length (stable), walking the
`[0, 2^maxLen)` address space: `code = start / 2^(maxLen-len)`. Extensionally
the RFC 1951 `next_code` algorithm. -/
def assignCodes (maxLen : Nat) : Nat → List (Nat × Nat) → List ((Nat × Nat) × Nat)
  | _, [] => []
  | start, (l, i) :: rest =>
    ((l, i), start / 2 ^ (maxLen - l)) :: assignCodes maxLen (start + 2 ^ (maxLen - l)) rest

/-- Canonical codes for a code-length sequence (positional: entry `s` is
symbol `s`). Unused symbols get `(0, 0)`. -/
def canonicalCodes (maxLen : Nat) (lens : List Nat) : List (Nat × Nat) :=
  let used := lens.zipIdx.filter fun p => p.1 ≠ 0
  let sorted := used.mergeSort fun a b => a.1 ≤ b.1
  let assigned := assignCodes maxLen 0 sorted
  lens.zipIdx.map fun (l, i) =>
    if l = 0 then (0, 0)
    else match assigned.find? fun q => q.1.2 == i with
      | some q => (l, q.2)
      | none => (0, 0)

/-- Kraft mass of a length assignment, scaled by `2^maxLen`. -/
def kraftSum (maxLen : Nat) (lens : List Nat) : Nat :=
  (lens.map fun l => if l = 0 then 0 else 2 ^ (maxLen - l)).sum

/-- Well-formed lengths: bounded and satisfying Kraft's inequality. -/
def WFLens (maxLen : Nat) (lens : List Nat) : Prop :=
  (∀ l ∈ lens, l ≤ maxLen) ∧ kraftSum maxLen lens ≤ 2 ^ maxLen

instance (maxLen : Nat) (lens : List Nat) : Decidable (WFLens maxLen lens) := by
  unfold WFLens
  infer_instance

/-! ## findSym specification -/

theorem findSym_none {codes : List (Nat × Nat)} {len code : Nat}
    (h : ∀ i, (hi : i < codes.length) → ¬(codes[i].1 = len ∧ codes[i].2 = code)) :
    findSym codes len code = none := by
  induction codes with
  | nil => rfl
  | cons p rest ih =>
    simp only [findSym]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [if_neg h0]
    rw [ih fun i hi => by
      have := h (i + 1) (by simp only [List.length_cons]; omega)
      simpa using this]
    rfl

theorem findSym_some {codes : List (Nat × Nat)} {len code : Nat} {s : Nat}
    (hs : s < codes.length) (hmatch : codes[s].1 = len ∧ codes[s].2 = code)
    (huniq : ∀ i, (hi : i < codes.length) → i ≠ s →
      ¬(codes[i].1 = len ∧ codes[i].2 = code)) :
    findSym codes len code = some s := by
  induction codes generalizing s with
  | nil => simp at hs
  | cons p rest ih =>
    match s with
    | 0 =>
      simp only [List.getElem_cons_zero] at hmatch
      simp only [findSym, if_pos hmatch]
    | s + 1 =>
      have hhead : ¬(p.1 = len ∧ p.2 = code) := by
        have := huniq 0 (by simp) (by omega)
        simpa using this
      simp only [findSym, if_neg hhead]
      rw [ih (s := s) (by simpa using hs)
        (by simpa using hmatch)
        (fun i hi hne => by
          have := huniq (i + 1) (by simp only [List.length_cons]; omega) (by omega)
          simpa using this)]
      rfl

/-! ## Generic round trip -/

private theorem div_pow_step (c mm : Nat) :
    2 * (c / 2 ^ (mm + 1)) + c / 2 ^ mm % 2 = c / 2 ^ mm := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

private theorem toNat_mod_two (x : Nat) : ((x % 2 == 1) : Bool).toNat = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- Walking the codeword of symbol `s` from `m` bits remaining: no strict
prefix hits the table (prefix-freeness), the full codeword hits exactly `s`. -/
private theorem decodeSymAux_spec {maxLen : Nat} {codes : List (Nat × Nat)}
    {s l c : Nat} (hpf : PrefixFree maxLen codes) (hs : s < codes.length)
    (hentry : codes[s] = (l, c)) (hlmax : l ≤ maxLen) (r : BitStream) :
    ∀ m, 1 ≤ m → m ≤ l →
      decodeSymAux codes maxLen (l - m) (c / 2 ^ m) (msbBits m c ++ r) =
        some (s, r) := by
  have hsl : (codes[s]).1 = l := by rw [hentry]
  have hsc : (codes[s]).2 = c := by rw [hentry]
  intro m
  induction m with
  | zero => omega
  | succ mm ihm =>
    intro _ hml
    have hguard : ¬ (maxLen ≤ l - (mm + 1)) := by omega
    simp only [decodeSymAux, dif_neg hguard, msbBits, List.cons_append]
    have hacc : 2 * (c / 2 ^ (mm + 1)) + ((c / 2 ^ mm % 2 == 1) : Bool).toNat
        = c / 2 ^ mm := by
      rw [toNat_mod_two]
      exact div_pow_step c mm
    rw [hacc]
    match hmm : mm with
    | 0 =>
      -- last bit: the full codeword must resolve to s
      have hk1 : l - 1 + 1 = l := by omega
      rw [hk1]
      have hfind : findSym codes l (c / 2 ^ 0) = some s := by
        simp only [Nat.pow_zero, Nat.div_one]
        apply findSym_some hs ⟨hsl, hsc⟩
        intro i hi hne hmatch
        obtain ⟨h1, h2⟩ := hmatch
        -- another entry equal to (l, c) would be a mutual prefix
        refine hpf.2 i hi s hs hne (by rw [h1]; omega) (by rw [hsl]; omega) ?_
        refine ⟨by rw [h1, hsl]; omega, ?_⟩
        rw [h1, h2, hsl, hsc]
        simp
      rw [hfind]
      simp [msbBits]
    | mm' + 1 =>
      -- strict prefix: the table must miss
      have hfind : findSym codes (l - (mm' + 1 + 1) + 1) (c / 2 ^ (mm' + 1)) = none := by
        apply findSym_none
        intro i hi hmatch
        obtain ⟨h1, h2⟩ := hmatch
        have hne : i ≠ s := by
          intro heq
          subst heq
          omega
        refine hpf.2 i hi s hs hne (by rw [h1]; omega) (by rw [hsl]; omega) ?_
        refine ⟨?_, ?_⟩
        · rw [h1, hsl]
          omega
        · rw [h1, h2, hsl, hsc]
          have harg : l - (l - (mm' + 1 + 1) + 1) = mm' + 1 := by omega
          rw [harg]
      rw [hfind]
      have hk : l - (mm' + 1 + 1) + 1 = l - (mm' + 1) := by omega
      rw [hk]
      exact ihm (by omega) (by omega)

/-- Round trip: decoding the emitted codeword of a used symbol returns that
symbol and consumes exactly the codeword — for ANY prefix-free assignment. -/
theorem decodeSym_encodeSym {maxLen : Nat} {codes : List (Nat × Nat)} {s : Nat}
    (hpf : PrefixFree maxLen codes) (hs : s < codes.length)
    (hused : (codes[s]).1 ≠ 0) (r : BitStream) :
    decodeSym codes maxLen (encodeSym codes s ++ r) = some (s, r) := by
  have hmem : codes[s] ∈ codes := List.getElem_mem hs
  have hbounds := hpf.1 codes[s] hmem hused
  obtain ⟨⟨l, c⟩, hentry⟩ : ∃ p : Nat × Nat, codes[s] = p := ⟨codes[s], rfl⟩
  rw [hentry] at hused hbounds
  have hl0 : l ≠ 0 := by simpa using hused
  have hlm : l ≤ maxLen := by simpa using hbounds.1
  have hcb : c < 2 ^ l := by simpa using hbounds.2
  have henc : encodeSym codes s = msbBits l c := by
    simp only [encodeSym, List.getElem?_eq_getElem hs, hentry]
  rw [henc]
  unfold decodeSym
  have hspec := decodeSymAux_spec hpf hs hentry hlm r l (by omega) (by omega)
  rw [Nat.sub_self, Nat.div_eq_of_lt hcb] at hspec
  exact hspec

end TarGz
