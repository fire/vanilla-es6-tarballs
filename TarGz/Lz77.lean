-- SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
-- SPDX-License-Identifier: MIT

import TarGz.Bits

/-!
# LZ77 tokenization (RFC 1951 §4)

`tokenize` is a greedy hash-chain matcher (zlib-shaped: 3-byte hash, bounded
chain walk, window 32768, match length 3..258). The round trip
`resolve_tokenize` depends only on the *verified* postcondition of the match
finder (`MatchSpec`), never on the hash-chain heuristics — any finder
producing verified matches keeps the proof intact.

`resolve` (with its per-byte `lzCopy`, which handles self-overlap naturally)
is exactly the decoder's copy semantics; the dynamic-Huffman decoder reuses
`lzCopy` so this round trip plugs into the DEFLATE one.
-/

namespace TarGz

inductive Tok where
  | lit (b : UInt8)
  | ref (len dist : Nat)
deriving Repr, DecidableEq

/-- Copy `len` bytes from `dist` back, one at a time (self-overlap = RLE). -/
def lzCopy (out : List UInt8) (dist : Nat) : Nat → List UInt8
  | 0 => out
  | len + 1 => lzCopy (out ++ [out[out.length - dist]!]) dist len

/-- Decoder semantics of a token stream. -/
def resolve : List Tok → List UInt8 → Option (List UInt8)
  | [], out => some out
  | Tok.lit b :: ts, out => resolve ts (out ++ [b])
  | Tok.ref len dist :: ts, out =>
    if 1 ≤ dist ∧ dist ≤ out.length ∧ dist ≤ 32768 ∧ 3 ≤ len ∧ len ≤ 258 then
      resolve ts (lzCopy out dist len)
    else none

/-- Length of the common run starting at `src`/`pos` (≤ fuel). -/
def matchLen (data : Array UInt8) : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | src, pos, fuel + 1 =>
    if data[src]! = data[pos]! then 1 + matchLen data (src + 1) (pos + 1) fuel
    else 0

def hash3 (a b c : UInt8) : Nat :=
  ((a.toNat <<< 10) ^^^ (b.toNat <<< 5) ^^^ c.toNat) &&& 32767

/-- Walk the hash chain (bounded), keeping the longest verified match. -/
def chainWalk (data : Array UInt8) (pos : Nat) (prev : Array Nat) :
    Nat → Nat → Nat × Nat → Nat × Nat
  | _, 0, best => best
  | cand, tries + 1, best =>
    if cand < pos ∧ pos - cand ≤ 32768 then
      let l := matchLen data cand pos (min 258 (data.size - pos))
      let best' := if l > best.1 then (l, pos - cand) else best
      chainWalk data pos prev prev[cand]! tries best'
    else best

/-- Greedy tokenizer. `head`/`prev` are the hash-chain state (sentinel =
`data.size`, i.e. "no entry"). -/
def tokenizeGo (data : Array UInt8) (head prev : Array Nat) (pos : Nat) :
    List Tok :=
  if h : pos < data.size then
    if h3 : pos + 3 ≤ data.size then
      let hsh := hash3 data[pos]! data[pos + 1]! data[pos + 2]!
      let cand := head[hsh]!
      let best := chainWalk data pos prev cand 32 (0, 0)
      let head' := head.set! hsh pos
      let prev' := prev.set! pos cand
      if hb : 3 ≤ best.1 then
        Tok.ref best.1 best.2 :: tokenizeGo data head' prev' (pos + best.1)
      else
        Tok.lit data[pos]! :: tokenizeGo data head' prev' (pos + 1)
    else
      Tok.lit data[pos]! :: tokenizeGo data head prev (pos + 1)
  else []
  termination_by data.size - pos
  decreasing_by
    all_goals first
    | omega
    | (have hb' : 3 ≤ (chainWalk data pos prev
          (head[hash3 data[pos]! data[pos + 1]! data[pos + 2]!]!) 32 (0, 0)).fst := hb
       omega)

def tokenize (d : List UInt8) : List Tok :=
  let data := d.toArray
  tokenizeGo data (Array.replicate 32768 data.size)
    (Array.replicate data.size data.size) 0

/-! ## Match-finder specification -/

theorem matchLen_le (data : Array UInt8) (src pos fuel : Nat) :
    matchLen data src pos fuel ≤ fuel := by
  induction fuel generalizing src pos with
  | zero => simp [matchLen]
  | succ f ih =>
    simp only [matchLen]
    split
    · have := ih (src + 1) (pos + 1)
      omega
    · omega

theorem matchLen_spec (data : Array UInt8) (fuel : Nat) :
    ∀ src pos j, j < matchLen data src pos fuel →
      data[src + j]! = data[pos + j]! := by
  induction fuel with
  | zero => intro src pos j h; simp [matchLen] at h
  | succ f ih =>
    intro src pos j h
    simp only [matchLen] at h
    split at h
    · rename_i heq
      match j with
      | 0 => simpa using heq
      | j + 1 =>
        have := ih (src + 1) (pos + 1) j (by omega)
        have h1 : src + 1 + j = src + (j + 1) := by omega
        have h2 : pos + 1 + j = pos + (j + 1) := by omega
        rw [h1, h2] at this
        exact this
    · omega

/-- Verified-match invariant: what the round trip needs from the finder. -/
def MatchSpec (data : Array UInt8) (pos : Nat) (b : Nat × Nat) : Prop :=
  b = (0, 0) ∨
  (1 ≤ b.2 ∧ b.2 ≤ pos ∧ b.2 ≤ 32768 ∧ b.1 ≤ 258 ∧ pos + b.1 ≤ data.size ∧
    ∀ j < b.1, data[pos - b.2 + j]! = data[pos + j]!)

theorem chainWalk_spec (data : Array UInt8) (pos : Nat) (prev : Array Nat) :
    ∀ (tries cand : Nat) (best : Nat × Nat), MatchSpec data pos best →
      MatchSpec data pos (chainWalk data pos prev cand tries best) := by
  intro tries
  induction tries with
  | zero => intro cand best hb; simpa [chainWalk] using hb
  | succ t ih =>
    intro cand best hb
    simp only [chainWalk]
    split
    · rename_i hc
      apply ih
      split
      · right
        have hle := matchLen_le data cand pos (min 258 (data.size - pos))
        refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
        intro j hj
        have hm := matchLen_spec data (min 258 (data.size - pos)) cand pos j hj
        have hidx : pos - (pos - cand) = cand := by omega
        simp only [hidx]
        exact hm
      · exact hb
    · exact hb

/-! ## Reconstruction -/

private theorem toList_getElem! (a : Array UInt8) (i : Nat) (h : i < a.size) :
    a.toList[i]! = a[i]! := by
  rw [getElem!_pos a.toList i (by simpa using h), getElem!_pos a i h]
  simp

private theorem take_snoc (l : List UInt8) (n : Nat) (h : n < l.length) :
    l.take n ++ [l[n]!] = l.take (n + 1) := by
  rw [getElem!_pos l n h, List.take_add_one, List.getElem?_eq_getElem h]
  rfl

private theorem take_getElem! (l : List UInt8) (n i : Nat) (hi : i < n)
    (hn : n ≤ l.length) : (l.take n)[i]! = l[i]! := by
  rw [getElem!_pos (l.take n) i (by simp [List.length_take]; omega),
    getElem!_pos l i (by omega)]
  simp [List.getElem_take]

/-- The overlap-copy lemma: copying `l` bytes from `d` back extends the
committed prefix by exactly the next `l` bytes of the source. -/
theorem lzCopy_take (data : Array UInt8) :
    ∀ (l pos d : Nat), 1 ≤ d → d ≤ pos → pos + l ≤ data.size →
      (∀ j < l, data[pos - d + j]! = data[pos + j]!) →
      lzCopy (data.toList.take pos) d l = data.toList.take (pos + l) := by
  intro l
  induction l with
  | zero => intro pos d _ _ _ _; simp [lzCopy]
  | succ ll ih =>
    intro pos d hd1 hdp hsz hmatch
    simp only [lzCopy]
    have hlen : (data.toList.take pos).length = pos := by
      simp [List.length_take]
      omega
    rw [hlen]
    have hel : (data.toList.take pos)[pos - d]! = data[pos]! := by
      rw [take_getElem! _ _ _ (by omega) (by simp; omega)]
      rw [toList_getElem! data (pos - d) (by omega)]
      have := hmatch 0 (by omega)
      simpa using this
    rw [hel]
    have hpos : data[pos]! = data.toList[pos]! :=
      (toList_getElem! data pos (by omega)).symm
    rw [hpos, take_snoc _ _ (by simp; omega)]
    have hrec := ih (pos + 1) d hd1 (by omega) (by omega) (fun j hj => by
      have := hmatch (j + 1) (by omega)
      have h1 : pos - d + (j + 1) = pos + 1 - d + j := by omega
      have h2 : pos + (j + 1) = pos + 1 + j := by omega
      rw [h1, h2] at this
      exact this)
    rw [hrec]
    congr 1
    omega

theorem resolve_lit (b : UInt8) (ts : List Tok) (out : List UInt8) :
    resolve (Tok.lit b :: ts) out = resolve ts (out ++ [b]) := rfl

theorem resolve_ref (len dist : Nat) (ts : List Tok) (out : List UInt8) :
    resolve (Tok.ref len dist :: ts) out =
      if 1 ≤ dist ∧ dist ≤ out.length ∧ dist ≤ 32768 ∧ 3 ≤ len ∧ len ≤ 258 then
        resolve ts (lzCopy out dist len)
      else none := rfl

private theorem take_snoc_arr (a : Array UInt8) (n : Nat) (h : n < a.size) :
    a.toList.take n ++ [a[n]!] = a.toList.take (n + 1) := by
  rw [← toList_getElem! a n h]
  exact take_snoc _ _ (by rw [Array.length_toList]; exact h)

theorem resolve_tokenizeGo (data : Array UInt8) (head prev : Array Nat)
    (pos : Nat) (hpos : pos ≤ data.size) :
    resolve (tokenizeGo data head prev pos) (data.toList.take pos)
      = some data.toList := by
  revert hpos
  fun_induction tokenizeGo data head prev pos with
  | case1 head prev pos h h3 hsh cand best head' prev' hb ih =>
    -- verified match accepted
    intro hpos
    have hspec : MatchSpec data pos best :=
      chainWalk_spec data pos prev 32 cand (0, 0) (Or.inl rfl)
    clear_value prev' head' best cand hsh
    rcases hspec with hz | ⟨hd1, hdp, hdw, hl258, hsz, hm⟩
    · rw [hz] at hb
      simp at hb
    · rw [resolve_ref]
      rw [if_pos ⟨hd1, by simp [List.length_take]; omega, hdw, hb, hl258⟩]
      rw [lzCopy_take data best.1 pos best.2 hd1 hdp hsz hm]
      exact ih (by omega)
  | case2 head prev pos h h3 hsh cand best head' prev' hb ih =>
    -- no acceptable match: literal
    intro hpos
    rw [resolve_lit]
    rw [take_snoc_arr data pos h]
    exact ih h
  | case3 head prev pos h h3 ih =>
    -- tail too short for a match: literal
    intro hpos
    rw [resolve_lit]
    rw [take_snoc_arr data pos h]
    exact ih h
  | case4 head prev pos h =>
    -- pos ≥ size: token list is empty, prefix is everything
    intro hpos
    rw [List.take_of_length_le (by simp; omega)]
    rfl

/-- Headline for this module: detokenizing the greedy tokenization
reconstructs the input exactly. -/
theorem resolve_tokenize (d : List UInt8) : resolve (tokenize d) [] = some d := by
  unfold tokenize
  have := resolve_tokenizeGo d.toArray
    (Array.replicate 32768 d.toArray.size)
    (Array.replicate d.toArray.size d.toArray.size) 0 (by omega)
  simpa using this

end TarGz
