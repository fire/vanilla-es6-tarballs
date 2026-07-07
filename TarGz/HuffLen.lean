import TarGz.Huffman

/-!
# Code-length heuristic (proof-light by design)

`mkLengths` builds Huffman code lengths from symbol frequencies: true Huffman
tree by repeated min-pairing, with frequency-halving retries if the depth
limit is exceeded. **No theorem depends on this module**: the encoder
validates the result at runtime with the decidable `WFLens`/`PrefixFree`
checks and falls back to stored blocks, so the headline round trip is
unconditional. Determinism matters (byte-identical ES6 differential tests):
insertion is stable (before the first strictly-greater frequency).
-/

namespace TarGz

inductive HTree where
  | leaf (sym : Nat)
  | node (l r : HTree)

/-- Insert before the first entry with strictly greater weight (stable). -/
def wqInsert (w : Nat) (t : HTree) : List (Nat × HTree) → List (Nat × HTree)
  | [] => [(w, t)]
  | (w', t') :: rest =>
    if w < w' then (w, t) :: (w', t') :: rest
    else (w', t') :: wqInsert w t rest

/-- Pair the two lightest until one tree remains. -/
def buildTree : List (Nat × HTree) → Option HTree
  | [] => none
  | [(_, t)] => some t
  | (w1, t1) :: (w2, t2) :: rest =>
    buildTree (wqInsert (w1 + w2) (HTree.node t1 t2) rest)
  termination_by q => q.length
  decreasing_by
    have h : (wqInsert (w1 + w2) (HTree.node t1 t2) rest).length = rest.length + 1 := by
      induction rest with
      | nil => rfl
      | cons p r ih =>
        simp only [wqInsert]
        split
        · simp
        · simp [ih]
    rw [h, List.length_cons, List.length_cons]
    omega

/-- Depth of every leaf. -/
def treeDepths (acc : List (Nat × Nat)) : HTree → Nat → List (Nat × Nat)
  | HTree.leaf s, d => (s, d) :: acc
  | HTree.node l r, d => treeDepths (treeDepths acc l (d + 1)) r (d + 1)

def maxDepth : List (Nat × Nat) → Nat
  | [] => 0
  | (_, d) :: rest => max d (maxDepth rest)

/-- Lengths from one tree-building attempt (`none` if depth-limited). -/
def tryLengths (maxLen n : Nat) (freqs : List Nat) : Option (List Nat) :=
  let used := (freqs.zipIdx.filter fun p => p.1 ≠ 0).map fun p => (p.1, HTree.leaf p.2)
  -- queue must be weight-sorted: insert one by one (freq order is stable)
  let queue := used.foldl (fun q p => wqInsert p.1 p.2 q) []
  match buildTree queue with
  | none => none
  | some t =>
    match used with
    | [_] => some ((List.range n).map fun s => if freqs[s]! ≠ 0 then 1 else 0)
    | _ =>
      let depths := treeDepths [] t 0
      if maxDepth depths ≤ maxLen then
        some ((List.range n).map fun s =>
          match depths.find? fun p => p.1 == s with
          | some p => p.2
          | none => 0)
      else none

/-- Bump the first `k` frequencies so at least two symbols are used
(always-complete codes; decoders accept them and no special cases arise). -/
def ensureTwoUsed (freqs : List Nat) : List Nat :=
  match (freqs.zipIdx.filter fun p => p.1 ≠ 0).length with
  | 0 => match freqs with
    | a :: b :: rest => (a + 1) :: (b + 1) :: rest
    | l => l.map (· + 1)
  | 1 => match freqs with
    | a :: rest =>
      if a = 0 then (a + 1) :: rest
      else match rest with
        | b :: rest' => a :: (b + 1) :: rest'
        | [] => [a]
    | [] => []
  | _ => freqs

/-- Frequencies → code lengths (positional, `n` symbols, ≤ `maxLen` bits),
with ≤ 4 frequency-halving retries. Callers re-validate with `WFLens`. -/
def mkLengths (maxLen n : Nat) (freqs0 : List Nat) : List Nat :=
  let freqs := ensureTwoUsed freqs0
  let rec go : Nat → List Nat → List Nat
    | 0, _ => List.replicate n 0
    | retries + 1, fs =>
      match tryLengths maxLen n fs with
      | some lens => lens
      | none => go retries (fs.map fun f => if f = 0 then 0 else f / 2 + 1)
  go 5 freqs

end TarGz
