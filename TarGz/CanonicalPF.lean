-- SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
-- SPDX-License-Identifier: MIT

import TarGz.Huffman

/-!
# The canonical construction is prefix-free

`canonical_prefixFree`: the RFC 1951 canonical code assignment of ANY
Kraft-valid length list is prefix-free. This retires the encoder's runtime
`PrefixFree` check as a mere belt-and-suspenders measure — the stored-block
fallback it guards is dead code.

Proof via the interval model: entry `(l, c)` occupies
`[c·2^(maxLen-l), (c+1)·2^(maxLen-l))` inside `[0, 2^maxLen)`. The
`assignCodes` fold makes the intervals consecutive; sortedness (widths
nonincreasing) makes every start divisible by its own width, so the division
is exact; Kraft's inequality makes everything fit. A prefix relation forces
the later interval's start inside the earlier interval — contradicting
consecutiveness.
-/

namespace TarGz

/-- Sum of the widths of the first `k` queue entries. -/
private def prefW (maxLen : Nat) (q : List (Nat × Nat)) (k : Nat) : Nat :=
  ((q.take k).map fun p => 2 ^ (maxLen - p.1)).sum

/-! ## List generalities -/

private theorem perm_sum {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih₁ ih₂ => omega

private theorem dvd_listSum {d : Nat} {l : List Nat} (h : ∀ x ∈ l, d ∣ x) :
    d ∣ l.sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.sum_cons]
    exact Nat.dvd_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-! ## prefW and assignCodes structure -/

private theorem prefW_succ (maxLen : Nat) (q : List (Nat × Nat)) (k : Nat)
    (hk : k < q.length) :
    prefW maxLen q (k + 1) = prefW maxLen q k + 2 ^ (maxLen - (q[k]).1) := by
  unfold prefW
  rw [List.map_take, List.map_take, List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hk)]
  simp

private theorem prefW_mono (maxLen : Nat) (q : List (Nat × Nat)) (k : Nat) :
    ∀ k', k ≤ k' → k' ≤ q.length → prefW maxLen q k ≤ prefW maxLen q k' := by
  intro k'
  induction k' with
  | zero =>
    intro h _
    have hk0 : k = 0 := by omega
    subst hk0
    exact Nat.le_refl _
  | succ kk ih =>
    intro hle hlen
    by_cases heq : k = kk + 1
    · subst heq
      exact Nat.le_refl _
    · have h1 : prefW maxLen q k ≤ prefW maxLen q kk := ih (by omega) (by omega)
      rw [prefW_succ maxLen q kk (by omega)]
      exact Nat.le_trans h1 (Nat.le_add_right _ _)

private theorem assignCodes_length (maxLen : Nat) :
    ∀ (q : List (Nat × Nat)) (start : Nat),
      (assignCodes maxLen start q).length = q.length := by
  intro q
  induction q with
  | nil => intro start; rfl
  | cons p rest ih =>
    intro start
    obtain ⟨l, i⟩ := p
    simp [assignCodes, ih]

private theorem assignCodes_getElem (maxLen : Nat) :
    ∀ (q : List (Nat × Nat)) (start k : Nat) (hk : k < q.length),
      (assignCodes maxLen start q)[k]'(by rw [assignCodes_length]; exact hk)
        = (q[k], (start + prefW maxLen q k) / 2 ^ (maxLen - (q[k]).1)) := by
  intro q
  induction q with
  | nil => intro start k hk; simp at hk
  | cons p rest ih =>
    intro start k hk
    obtain ⟨l, i⟩ := p
    match k with
    | 0 =>
      simp [assignCodes, prefW]
    | k + 1 =>
      simp only [assignCodes, List.getElem_cons_succ]
      rw [ih (start + 2 ^ (maxLen - l)) k (by simpa using hk)]
      have hpw : prefW maxLen ((l, i) :: rest) (k + 1)
          = 2 ^ (maxLen - l) + prefW maxLen rest k := by
        unfold prefW
        simp [List.take_succ_cons]
      rw [hpw, ← Nat.add_assoc]

/-! ## The interval argument -/

/-- Everything the interval argument needs about the sorted used queue. -/
private structure QOk (maxLen : Nat) (q : List (Nat × Nat)) : Prop where
  sorted : List.Pairwise (fun a b => a.1 ≤ b.1) q
  pos : ∀ p ∈ q, p.1 ≠ 0
  le : ∀ p ∈ q, p.1 ≤ maxLen
  kraft : prefW maxLen q q.length ≤ 2 ^ maxLen

private theorem width_dvd_prefW {maxLen : Nat} {q : List (Nat × Nat)}
    (hq : QOk maxLen q) (k : Nat) (hk : k < q.length) :
    2 ^ (maxLen - (q[k]).1) ∣ prefW maxLen q k := by
  apply dvd_listSum
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨j, hj, hpe⟩ := List.mem_iff_getElem.mp hp
  subst hpe
  rw [List.getElem_take]
  have hjk : j < k := by
    simp only [List.length_take] at hj
    omega
  have hjq : j < q.length := by omega
  have hle := List.pairwise_iff_getElem.mp hq.sorted j k hjq hk hjk
  exact Nat.pow_dvd_pow 2 (by omega)

private theorem prefW_add_width_le {maxLen : Nat} {q : List (Nat × Nat)}
    (hq : QOk maxLen q) (k : Nat) (hk : k < q.length) :
    prefW maxLen q k + 2 ^ (maxLen - (q[k]).1) ≤ 2 ^ maxLen := by
  rw [← prefW_succ maxLen q k hk]
  exact Nat.le_trans
    (prefW_mono maxLen q (k + 1) q.length (by omega) (Nat.le_refl _)) hq.kraft

private theorem code_lt {maxLen : Nat} {q : List (Nat × Nat)}
    (hq : QOk maxLen q) (k : Nat) (hk : k < q.length) :
    prefW maxLen q k / 2 ^ (maxLen - (q[k]).1) < 2 ^ (q[k]).1 := by
  have halign := Nat.div_mul_cancel (width_dvd_prefW hq k hk)
  have hle := prefW_add_width_le hq k hk
  have hsplit : 2 ^ maxLen = 2 ^ (q[k]).1 * 2 ^ (maxLen - (q[k]).1) := by
    rw [← Nat.pow_add]
    congr 1
    have := hq.le q[k] (List.getElem_mem hk)
    omega
  rw [hsplit] at hle
  rcases Nat.lt_or_ge (prefW maxLen q k / 2 ^ (maxLen - (q[k]).1)) (2 ^ (q[k]).1)
    with h | hcon
  · exact h
  · exfalso
    have h1 := Nat.mul_le_mul_right (2 ^ (maxLen - (q[k]).1)) hcon
    rw [halign] at h1
    have hw := Nat.two_pow_pos (maxLen - (q[k]).1)
    omega

private theorem div_bounds {a m c : Nat} (hm : 0 < m) (h : a / m = c) :
    m * c ≤ a ∧ a < m * c + m := by
  have hdm := Nat.div_add_mod a m
  have hmod := Nat.mod_lt a hm
  rw [h] at hdm
  omega

/-- Prefix relation places interval 2's start inside interval 1. -/
private theorem prefix_interval {S1 S2 w1 w2 m c1 c2 : Nat}
    (hw : w1 = m * w2) (hm : 0 < m) (hw2 : 0 < w2)
    (ha1 : c1 * w1 = S1) (ha2 : c2 * w2 = S2)
    (hdiv : c2 / m = c1) : S1 ≤ S2 ∧ S2 < S1 + w1 := by
  obtain ⟨hd1, hd2⟩ := div_bounds hm hdiv
  have hS1 : S1 = m * c1 * w2 := by
    rw [← ha1, hw, ← Nat.mul_assoc, Nat.mul_comm c1 m]
  have h1 := Nat.mul_le_mul_right w2 hd1
  have h2 := (Nat.mul_lt_mul_right hw2).mpr hd2
  rw [Nat.add_mul] at h2
  constructor
  · omega
  · omega

private theorem no_prefix_forward {maxLen : Nat} {q : List (Nat × Nat)}
    (hq : QOk maxLen q) (k1 k2 : Nat) (h12 : k1 < k2) (hk2 : k2 < q.length) :
    ¬ NumPrefix ((q[k1]'(by omega)).1,
        prefW maxLen q k1 / 2 ^ (maxLen - (q[k1]'(by omega)).1))
      ((q[k2]).1, prefW maxLen q k2 / 2 ^ (maxLen - (q[k2]).1)) := by
  have hk1 : k1 < q.length := by omega
  intro hnp
  obtain ⟨hle, hdiv⟩ := hnp
  simp only at hle hdiv
  have halign1 := Nat.div_mul_cancel (width_dvd_prefW hq k1 hk1)
  have halign2 := Nat.div_mul_cancel (width_dvd_prefW hq k2 hk2)
  have hS : prefW maxLen q k1 + 2 ^ (maxLen - (q[k1]).1) ≤ prefW maxLen q k2 := by
    rw [← prefW_succ maxLen q k1 hk1]
    exact prefW_mono maxLen q (k1 + 1) k2 (by omega) (by omega)
  have hml2 := hq.le q[k2] (List.getElem_mem hk2)
  have hwsplit : 2 ^ (maxLen - (q[k1]).1)
      = 2 ^ ((q[k2]).1 - (q[k1]).1) * 2 ^ (maxLen - (q[k2]).1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hint := prefix_interval hwsplit
    (Nat.two_pow_pos ((q[k2]).1 - (q[k1]).1))
    (Nat.two_pow_pos (maxLen - (q[k2]).1))
    halign1 halign2 hdiv
  omega

private theorem no_prefix_backward {maxLen : Nat} {q : List (Nat × Nat)}
    (hq : QOk maxLen q) (k1 k2 : Nat) (h12 : k1 < k2) (hk2 : k2 < q.length) :
    ¬ NumPrefix ((q[k2]).1, prefW maxLen q k2 / 2 ^ (maxLen - (q[k2]).1))
      ((q[k1]'(by omega)).1,
        prefW maxLen q k1 / 2 ^ (maxLen - (q[k1]'(by omega)).1)) := by
  have hk1 : k1 < q.length := by omega
  intro hnp
  obtain ⟨hle, hdiv⟩ := hnp
  simp only at hle hdiv
  -- sortedness gives l1 ≤ l2; with l2 ≤ l1 the lengths are equal
  have hsle := List.pairwise_iff_getElem.mp hq.sorted k1 k2 hk1 hk2 h12
  have hll : (q[k1]).1 = (q[k2]).1 := Nat.le_antisymm hsle hle
  rw [hll] at hdiv
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hdiv
  -- equal lengths, equal codes → equal starts, contradicting strict growth
  have halign1 := Nat.div_mul_cancel (width_dvd_prefW hq k1 hk1)
  have halign2 := Nat.div_mul_cancel (width_dvd_prefW hq k2 hk2)
  rw [hll] at halign1
  rw [hdiv] at halign1
  have hS : prefW maxLen q k1 + 2 ^ (maxLen - (q[k1]).1) ≤ prefW maxLen q k2 := by
    rw [← prefW_succ maxLen q k1 hk1]
    exact prefW_mono maxLen q (k1 + 1) k2 (by omega) (by omega)
  rw [hll] at hS
  have hw := Nat.two_pow_pos (maxLen - (q[k2]).1)
  omega

/-! ## The sorted used queue of a length list -/

private def usedOf (lens : List Nat) : List (Nat × Nat) :=
  lens.zipIdx.filter fun p => p.1 ≠ 0

private def sortedOf (lens : List Nat) : List (Nat × Nat) :=
  (usedOf lens).mergeSort fun a b => a.1 ≤ b.1

private theorem mem_usedOf {lens : List Nat} {l i : Nat}
    (hp : (l, i) ∈ usedOf lens) :
    l ≠ 0 ∧ ∃ hi : i < lens.length, l = lens[i]'hi := by
  unfold usedOf at hp
  rw [List.mem_filter] at hp
  obtain ⟨hz, hb⟩ := hp
  have hm := List.mem_zipIdx hz
  obtain ⟨-, hlen, hval⟩ := hm
  simp only [Nat.zero_add] at hlen
  refine ⟨by simpa using hb, by omega, ?_⟩
  simpa using hval

private theorem kraft_usedOf (maxLen : Nat) :
    ∀ (lens : List Nat) (k : Nat),
      (((lens.zipIdx k).filter fun p => p.1 ≠ 0).map
          fun p => 2 ^ (maxLen - p.1)).sum = kraftSum maxLen lens := by
  intro lens
  induction lens with
  | nil => intro k; rfl
  | cons l rest ih =>
    intro k
    rw [List.zipIdx_cons]
    by_cases hz : l = 0
    · subst hz
      simp [kraftSum, List.sum_cons] at ih ⊢
      exact ih (k + 1)
    · simp [hz, kraftSum, List.sum_cons] at ih ⊢
      rw [ih (k + 1)]

private theorem qok_sortedOf {maxLen : Nat} {lens : List Nat}
    (h : WFLens maxLen lens) : QOk maxLen (sortedOf lens) := by
  have hperm : (sortedOf lens).Perm (usedOf lens) := List.mergeSort_perm _ _
  constructor
  · -- sorted by length
    have hp := List.pairwise_mergeSort
      (le := fun a b : Nat × Nat => a.1 ≤ b.1)
      (by intro a b c h1 h2; simp at h1 h2 ⊢; omega)
      (by intro a b; simp; omega)
      (usedOf lens)
    exact hp.imp (by intro a b hab; simpa using hab)
  · intro p hp
    obtain ⟨l, i⟩ := p
    exact (mem_usedOf (hperm.mem_iff.mp hp)).1
  · intro p hp
    obtain ⟨l, i⟩ := p
    obtain ⟨-, hi, hval⟩ := mem_usedOf (hperm.mem_iff.mp hp)
    have hmem : lens[i] ∈ lens := List.getElem_mem hi
    simpa [hval] using h.1 lens[i] hmem
  · -- Kraft fits
    unfold prefW
    rw [List.take_length]
    have hps := perm_sum (List.Perm.map (fun p : Nat × Nat => 2 ^ (maxLen - p.1)) hperm)
    rw [hps]
    have := kraft_usedOf maxLen lens 0
    unfold usedOf
    rw [this]
    exact h.2

/-! ## Characterizing the scattered positional entries -/

private theorem canonicalCodes_length (maxLen : Nat) (lens : List Nat) :
    (canonicalCodes maxLen lens).length = lens.length := by
  simp [canonicalCodes]

private theorem canonicalCodes_getElem_eq (maxLen : Nat) (lens : List Nat)
    (i : Nat) (hi : i < lens.length) :
    (canonicalCodes maxLen lens)[i]'(by rw [canonicalCodes_length]; exact hi)
      = if lens[i] = 0 then (0, 0)
        else
          match (assignCodes maxLen 0 (sortedOf lens)).find?
              fun q => q.1.2 == i with
          | some q => (lens[i], q.2)
          | none => (0, 0) := by
  have hrfl : canonicalCodes maxLen lens
      = lens.zipIdx.map fun p =>
          if p.1 = 0 then (0, 0)
          else
            match (assignCodes maxLen 0 (sortedOf lens)).find?
                fun q => q.1.2 == p.2 with
            | some q => (p.1, q.2)
            | none => (0, 0) := rfl
  simp only [hrfl, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]

/-- Every used position's entry comes from a definite slot of the assigned
list, carrying its own length and index. -/
private theorem canonical_entry (maxLen : Nat) (lens : List Nat) (i : Nat)
    (hi : i < lens.length) (hne : lens[i] ≠ 0) :
    ∃ (k : Nat) (hk : k < (sortedOf lens).length),
      ((sortedOf lens)[k]'hk) = (lens[i], i) ∧
      (canonicalCodes maxLen lens)[i]'(by rw [canonicalCodes_length]; exact hi)
        = (lens[i],
            prefW maxLen (sortedOf lens) k / 2 ^ (maxLen - lens[i])) := by
  -- the entry (lens[i], i) is in the used set, hence in the sorted queue
  have hzmem : (lens[i], i) ∈ lens.zipIdx := by
    refine List.mem_iff_getElem.mpr ⟨i, by simpa [List.length_zipIdx] using hi, ?_⟩
    rw [List.getElem_zipIdx]
    simp
  have hused : (lens[i], i) ∈ usedOf lens := by
    unfold usedOf
    rw [List.mem_filter]
    exact ⟨hzmem, by simpa using hne⟩
  have hsortmem : (lens[i], i) ∈ sortedOf lens :=
    (List.mergeSort_perm _ _).mem_iff.mpr hused
  obtain ⟨k0, hk0, hk0e⟩ := List.mem_iff_getElem.mp hsortmem
  -- the find? in the scatter succeeds
  have hsome : ((assignCodes maxLen 0 (sortedOf lens)).find?
      fun q => q.1.2 == i).isSome := by
    rw [List.find?_isSome]
    refine ⟨(assignCodes maxLen 0 (sortedOf lens))[k0]'(by
      rw [assignCodes_length]; exact hk0), List.getElem_mem _, ?_⟩
    rw [assignCodes_getElem maxLen (sortedOf lens) 0 k0 hk0, hk0e]
    simp
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  have hemem := List.mem_of_find?_eq_some he
  have hepred : e.1.2 = i := by
    have := List.find?_some he
    simpa using this
  obtain ⟨k, hk', hke⟩ := List.mem_iff_getElem.mp hemem
  have hk : k < (sortedOf lens).length := by
    rwa [assignCodes_length] at hk'
  have hkval := assignCodes_getElem maxLen (sortedOf lens) 0 k hk
  rw [hke] at hkval
  -- the sorted entry at k is (lens[i], i)
  have he1 : e.1 = (sortedOf lens)[k]'hk := by rw [hkval]
  have hsk : ((sortedOf lens)[k]'hk) = (lens[i], i) := by
    have hmem2 : ((sortedOf lens)[k]'hk) ∈ usedOf lens :=
      (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem hk)
    obtain ⟨⟨ll, ii⟩, hp⟩ : ∃ p : Nat × Nat, ((sortedOf lens)[k]'hk) = p :=
      ⟨_, rfl⟩
    rw [hp] at hmem2
    obtain ⟨-, hii, hval⟩ := mem_usedOf hmem2
    have hii' : ii = i := by
      have := hepred
      rw [he1, hp] at this
      simpa using this
    subst hii'
    rw [hp]
    have : ll = lens[ii] := hval
    simp [this]
  refine ⟨k, hk, hsk, ?_⟩
  rw [canonicalCodes_getElem_eq maxLen lens i hi, if_neg hne, he]
  simp only []
  have he2 : e.2 = prefW maxLen (sortedOf lens) k / 2 ^ (maxLen - lens[i]) := by
    rw [hkval, hsk]
    simp
  rw [he2]

/-! ## The theorem -/

/-- The RFC 1951 canonical code of any Kraft-valid length assignment is
prefix-free: the encoder's runtime `PrefixFree` check can never fail, so the
stored-block fallback is dead code. -/
theorem canonical_prefixFree (maxLen : Nat) (lens : List Nat)
    (h : WFLens maxLen lens) : PrefixFree maxLen (canonicalCodes maxLen lens) := by
  have hq := qok_sortedOf h
  constructor
  · -- bounds
    intro p hp hne
    obtain ⟨i, hi, hpe⟩ := List.mem_iff_getElem.mp hp
    have hi' : i < lens.length := by
      rwa [canonicalCodes_length] at hi
    by_cases hz : lens[i] = 0
    · exfalso
      apply hne
      rw [← hpe, canonicalCodes_getElem_eq maxLen lens i hi', if_pos hz]
    · obtain ⟨k, hk, hsk, hci⟩ := canonical_entry maxLen lens i hi' hz
      rw [← hpe, hci]
      have hb := code_lt hq k hk
      have hlenmax : lens[i] ≤ maxLen := h.1 lens[i] (List.getElem_mem hi')
      rw [hsk] at hb
      simp only at hb ⊢
      exact ⟨hlenmax, hb⟩
  · -- pairwise prefix-freedom
    intro i hilen j hjlen hij hnei hnej
    have hi' : i < lens.length := by rwa [canonicalCodes_length] at hilen
    have hj' : j < lens.length := by rwa [canonicalCodes_length] at hjlen
    have hzi : lens[i] ≠ 0 := by
      intro hz
      apply hnei
      rw [canonicalCodes_getElem_eq maxLen lens i hi', if_pos hz]
    have hzj : lens[j] ≠ 0 := by
      intro hz
      apply hnej
      rw [canonicalCodes_getElem_eq maxLen lens j hj', if_pos hz]
    obtain ⟨ki, hki, hski, hci⟩ := canonical_entry maxLen lens i hi' hzi
    obtain ⟨kj, hkj, hskj, hcj⟩ := canonical_entry maxLen lens j hj' hzj
    have hkij : ki ≠ kj := by
      intro hkk
      subst hkk
      rw [hski] at hskj
      have : i = j := by
        have := congrArg Prod.snd hskj
        simpa using this
      exact hij this
    rw [hci, hcj]
    have h1 : lens[i] = ((sortedOf lens)[ki]'hki).1 := by rw [hski]
    have h2 : lens[j] = ((sortedOf lens)[kj]'hkj).1 := by rw [hskj]
    rw [h1, h2]
    rcases Nat.lt_or_ge ki kj with hlt | hge
    · exact no_prefix_forward hq ki kj hlt hkj
    · have hlt : kj < ki := by omega
      exact no_prefix_backward hq kj ki hlt hki

end TarGz
