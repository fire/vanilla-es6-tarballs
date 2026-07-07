import TarGz.Bits

/-!
# Verified USTAR tar writer/reader model

Byte-level model of a USTAR tar archive as `List UInt8`, with a writer
(`tar`/`tarBytes`), a tolerant reader (`untar`/`untarBytes`), and a proved
round-trip theorem `untar_tar : untar (tar es) = some es` for lists of valid
entries.
-/

namespace TarGz

structure TarEntry where
  name : List UInt8
  data : List UInt8
deriving Repr, DecidableEq

def ValidEntry (e : TarEntry) : Prop :=
  0 < e.name.length ∧ e.name.length ≤ 100 ∧ (0 : UInt8) ∉ e.name ∧ e.data.length < 8 ^ 11

instance (e : TarEntry) : Decidable (ValidEntry e) := by
  unfold ValidEntry; infer_instance

/-- Right-pad a field to width `w` with NUL bytes. -/
def padField (w : Nat) (bs : List UInt8) : List UInt8 := bs ++ List.replicate (w - bs.length) 0

/-- `w - 1` zero-padded octal digits, then a NUL terminator. -/
def octEnc (w n : Nat) : List UInt8 :=
  ((List.range (w - 1)).reverse.map fun i => UInt8.ofNat (0x30 + n / 8 ^ i % 8)) ++ [0]

/-- Tolerant octal field decoder: skip leading spaces, read octal digits, ignore the rest. -/
def octDec (field : List UInt8) : Option Nat :=
  let digits := (field.dropWhile (· == 0x20)).takeWhile fun b => 0x30 ≤ b && b ≤ 0x37
  if digits.isEmpty then none
  else some (digits.foldl (fun a b => 8 * a + (b.toNat - 0x30)) 0)

def sumBytes (bs : List UInt8) : Nat := (bs.map (·.toNat)).sum

/-- The USTAR header, as a list of fields (with the checksum field passed in). -/
def headerFields (e : TarEntry) (chk : List UInt8) : List (List UInt8) :=
  [padField 100 e.name,          -- name       offset 0
   octEnc 8 0o644,               -- mode       offset 100
   octEnc 8 0,                   -- uid        offset 108
   octEnc 8 0,                   -- gid        offset 116
   octEnc 12 e.data.length,      -- size       offset 124
   octEnc 12 0,                  -- mtime      offset 136
   chk,                          -- chksum     offset 148 (8 bytes)
   [0x30],                       -- typeflag   offset 156
   padField 100 [],              -- linkname   offset 157
   [0x75, 0x73, 0x74, 0x61, 0x72, 0x00, 0x30, 0x30],  -- "ustar\0" + "00", offset 257
   padField 32 [], padField 32 [],                     -- uname/gname
   octEnc 8 0, octEnc 8 0,                             -- devmajor/devminor
   padField 155 [],                                    -- prefix     offset 345
   List.replicate 12 0]                                -- pad to 512

def headerRaw (e : TarEntry) (chk : List UInt8) : List UInt8 := (headerFields e chk).flatten

def spaces8 : List UInt8 := List.replicate 8 0x20

/-- Header with the real checksum spliced in: 6 octal digits, NUL, space. -/
def mkHeader (e : TarEntry) : List UInt8 :=
  headerRaw e (octEnc 7 (sumBytes (headerRaw e spaces8)) ++ [0x20])

def padTo512 (bs : List UInt8) : List UInt8 := bs ++ List.replicate ((512 - bs.length % 512) % 512) 0

def entryBytes (e : TarEntry) : List UInt8 := mkHeader e ++ padTo512 e.data

def tarBytes (es : List TarEntry) : List UInt8 := (es.map entryBytes).flatten ++ List.replicate 1024 0

/-- Fuel-based tar reader, tolerant of foreign ustar archives. -/
def untarBytes : Nat → List UInt8 → Option (List TarEntry)
  | 0, _ => none
  | fuel + 1, bytes =>
    let header := bytes.take 512
    if header.length < 512 then none
    else if header.all (· == 0) then some []       -- terminator
    else
      match octDec ((header.drop 124).take 12) with
      | none => none
      | some size =>
        match octDec ((header.drop 148).take 8) with
        | none => none
        | some stored =>
          if sumBytes (header.take 148 ++ spaces8 ++ header.drop 156) ≠ stored then none
          else
            let body := bytes.drop 512
            let padded := (size + 511) / 512 * 512
            let rest := body.drop padded
            let tf := header[156]!
            if tf == 0x30 || tf == 0x00 then
              let rawName := (header.take 100).takeWhile (fun b => b != 0)
              let prefixF := ((header.drop 345).take 155).takeWhile (fun b => b != 0)
              let name := if prefixF.isEmpty then rawName else prefixF ++ [0x2F] ++ rawName
              match untarBytes fuel rest with
              | none => none
              | some es => some ({ name := name, data := body.take size } :: es)
            else
              match untarBytes fuel rest with   -- skip dirs, pax x/g, GNU L/K, everything else
              | none => none
              | some es => some es

def untar (bytes : List UInt8) : Option (List TarEntry) := untarBytes (bytes.length / 512 + 1) bytes

def tar := tarBytes

/-! ## Octal encoding: digits and the decode/encode round trip -/

/-- The digit part of `octEnc`: `k` zero-padded octal digits of `n`, most significant first. -/
def octDigits (k n : Nat) : List UInt8 :=
  (List.range k).reverse.map fun i => UInt8.ofNat (0x30 + n / 8 ^ i % 8)

theorem octEnc_eq (w n : Nat) : octEnc w n = octDigits (w - 1) n ++ [0] := rfl

theorem octDigits_succ (k n : Nat) :
    octDigits (k + 1) n = UInt8.ofNat (0x30 + n / 8 ^ k % 8) :: octDigits k n := by
  simp [octDigits, List.range_succ, List.reverse_append]

@[simp] theorem octDigits_length (k n : Nat) : (octDigits k n).length = k := by
  simp [octDigits]

@[simp] theorem octEnc_length (w n : Nat) : (octEnc w n).length = w - 1 + 1 := by
  simp [octEnc]

theorem octDigits_mem_range {k n : Nat} {b : UInt8} (hb : b ∈ octDigits k n) :
    0x30 ≤ b.toNat ∧ b.toNat ≤ 0x37 := by
  simp only [octDigits, List.mem_map, List.mem_reverse, List.mem_range] at hb
  obtain ⟨i, _, rfl⟩ := hb
  simp
  omega

theorem foldl_octDigits (k acc n : Nat) :
    (octDigits k n).foldl (fun a b => 8 * a + (b.toNat - 0x30)) acc = acc * 8 ^ k + n % 8 ^ k := by
  induction k generalizing acc with
  | zero => simp [octDigits, Nat.mod_one]
  | succ k ih =>
    rw [octDigits_succ, List.foldl_cons, ih]
    have hd : (UInt8.ofNat (0x30 + n / 8 ^ k % 8)).toNat = 0x30 + n / 8 ^ k % 8 := by
      simp; omega
    rw [hd, Nat.mod_pow_succ, Nat.pow_succ]
    simp only [Nat.add_sub_cancel_left, Nat.add_mul]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm]

theorem takeWhile_append_of_all {α} {p : α → Bool} {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, p x = true) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    have ha : p a = true := h a (List.mem_cons_self ..)
    simp [ha, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem octDigits_ne_space {k n : Nat} {b : UInt8} (hb : b ∈ octDigits k n) :
    (b == 0x20) = false := by
  have h := octDigits_mem_range hb
  rw [beq_eq_false_iff_ne]
  intro heq
  subst heq
  simp at h

theorem octDigits_isDigit {k n : Nat} {b : UInt8} (hb : b ∈ octDigits k n) :
    (0x30 ≤ b && b ≤ 0x37) = true := by
  have h := octDigits_mem_range hb
  simp [UInt8.le_iff_toNat_le]
  omega

/-- The octal round trip tolerates arbitrary junk after the encoded field. -/
theorem octDec_octEnc_append (w n : Nat) (hw : 1 < w) (h : n < 8 ^ (w - 1)) (tl : List UInt8) :
    octDec (octEnc w n ++ tl) = some n := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := rfl
  have h' : n < 8 ^ (k + 1) := by rw [hk] at h; exact h
  have hmem : UInt8.ofNat (0x30 + n / 8 ^ k % 8) ∈ octDigits (k + 1) n := by
    rw [octDigits_succ]; exact List.mem_cons_self ..
  have hspace := octDigits_ne_space hmem
  have hdigit := octDigits_isDigit hmem
  have htail : ∀ x ∈ octDigits k n, (0x30 ≤ x && x ≤ 0x37) = true := fun x hx =>
    octDigits_isDigit (by rw [octDigits_succ]; exact List.mem_cons_of_mem _ hx)
  have htake0 : ((0 : UInt8) :: tl).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = [] := by
    rw [List.takeWhile_cons, if_neg (by decide)]
  have hspace' : ¬((UInt8.ofNat (0x30 + n / 8 ^ k % 8) == 0x20) = true) := by
    rw [hspace]; exact Bool.false_ne_true
  have hempty : ¬((octDigits (k + 1) n).isEmpty = true) := by
    rw [octDigits_succ]; simp
  simp only [octDec, octEnc_eq, hk, octDigits_succ]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [List.dropWhile_cons, if_neg hspace']
  rw [List.takeWhile_cons, if_pos hdigit]
  rw [takeWhile_append_of_all htail, htake0, List.append_nil]
  rw [← octDigits_succ]
  rw [if_neg hempty]
  rw [foldl_octDigits]
  simp [Nat.mod_eq_of_lt h']

/-- Octal decode/encode round trip. Note the strengthened hypothesis `1 < w`:
for `w = 1` the encoding is just a NUL byte and decodes to `none`. -/
theorem octDec_octEnc (w n : Nat) (hw : 1 < w) (h : n < 8 ^ (w - 1)) :
    octDec (octEnc w n) = some n := by
  have := octDec_octEnc_append w n hw h []
  rwa [List.append_nil] at this

/-! ## Byte sums -/

theorem sumBytes_append (a b : List UInt8) : sumBytes (a ++ b) = sumBytes a + sumBytes b := by
  simp [sumBytes]

theorem sumBytes_le (bs : List UInt8) : sumBytes bs ≤ 255 * bs.length := by
  induction bs with
  | nil => simp [sumBytes]
  | cons b bs ih =>
    have hb : b.toNat < 2 ^ 8 := UInt8.toNat_lt b
    simp only [sumBytes, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-! ## Header structure: `headerRaw e chk = hdrA e ++ (chk ++ hdrB)` -/

theorem padField_length {w : Nat} {bs : List UInt8} (h : bs.length ≤ w) :
    (padField w bs).length = w := by
  simp [padField]; omega

/-- The checksum field of `mkHeader`. -/
def mkChk (e : TarEntry) : List UInt8 :=
  octEnc 7 (sumBytes (headerRaw e spaces8)) ++ [0x20]

theorem mkChk_length (e : TarEntry) : (mkChk e).length = 8 := by
  simp [mkChk]

theorem mkHeader_def (e : TarEntry) : mkHeader e = headerRaw e (mkChk e) := rfl

/-- Bytes of the header strictly before the checksum field (offsets 0-147). -/
def hdrA (e : TarEntry) : List UInt8 :=
  padField 100 e.name ++ octEnc 8 0o644 ++ octEnc 8 0 ++ octEnc 8 0 ++
    octEnc 12 e.data.length ++ octEnc 12 0

/-- Bytes of the header strictly after the checksum field (offsets 156-511). -/
def hdrB : List UInt8 :=
  0x30 :: (padField 100 [] ++ [0x75, 0x73, 0x74, 0x61, 0x72, 0x00, 0x30, 0x30] ++
    padField 32 [] ++ padField 32 [] ++ octEnc 8 0 ++ octEnc 8 0 ++ padField 155 [] ++
    List.replicate 12 0)

theorem headerRaw_eq (e : TarEntry) (chk : List UInt8) :
    headerRaw e chk = hdrA e ++ (chk ++ hdrB) := by
  simp [headerRaw, headerFields, hdrA, hdrB, List.flatten_cons, List.append_assoc]

theorem hdrA_length {e : TarEntry} (he : ValidEntry e) : (hdrA e).length = 148 := by
  have h := he.2.1
  simp [hdrA, padField]
  omega

theorem padField_nil (w : Nat) : padField w [] = List.replicate w (0 : UInt8) := by
  simp [padField]

theorem padField_nil_length (w : Nat) : (padField w []).length = w := by
  simp [padField]

theorem hdrB_length : hdrB.length = 356 := by
  simp only [hdrB, List.length_cons, List.length_append, padField_nil_length,
    List.length_replicate, octEnc_length, List.length_nil]

theorem headerRaw_length {e : TarEntry} (he : ValidEntry e) {chk : List UInt8}
    (hc : chk.length = 8) : (headerRaw e chk).length = 512 := by
  rw [headerRaw_eq]
  simp [hdrA_length he, hdrB_length, hc]

theorem mkHeader_length {e : TarEntry} (he : ValidEntry e) : (mkHeader e).length = 512 := by
  rw [mkHeader_def]
  exact headerRaw_length he (mkChk_length e)

theorem mkHeader_eq (e : TarEntry) : mkHeader e = hdrA e ++ (mkChk e ++ hdrB) := by
  rw [mkHeader_def, headerRaw_eq]

/-! ## Field extraction -/

theorem drop_take_append {α} {P F : List α} (Q : List α) {off w : Nat}
    (hP : P.length = off) (hF : F.length = w) :
    ((P ++ (F ++ Q)).drop off).take w = F := by
  rw [List.drop_left' hP, List.take_left' hF]

theorem mkHeader_name_split (e : TarEntry) :
    mkHeader e = padField 100 e.name ++ (octEnc 8 0o644 ++ (octEnc 8 0 ++ (octEnc 8 0 ++
      (octEnc 12 e.data.length ++ (octEnc 12 0 ++ (mkChk e ++ hdrB)))))) := by
  rw [mkHeader_eq]
  simp [hdrA, List.append_assoc]

theorem name_field {e : TarEntry} (he : ValidEntry e) :
    (mkHeader e).take 100 = padField 100 e.name := by
  rw [mkHeader_name_split]
  exact List.take_left' (padField_length he.2.1)

theorem mkHeader_size_split (e : TarEntry) :
    mkHeader e = (padField 100 e.name ++ octEnc 8 0o644 ++ octEnc 8 0 ++ octEnc 8 0) ++
      (octEnc 12 e.data.length ++ (octEnc 12 0 ++ (mkChk e ++ hdrB))) := by
  rw [mkHeader_eq]
  simp [hdrA, List.append_assoc]

theorem size_field {e : TarEntry} (he : ValidEntry e) :
    ((mkHeader e).drop 124).take 12 = octEnc 12 e.data.length := by
  rw [mkHeader_size_split]
  refine drop_take_append _ ?_ ?_
  · simp [padField_length he.2.1]
  · simp

theorem chksum_field {e : TarEntry} (he : ValidEntry e) :
    ((mkHeader e).drop 148).take 8 = mkChk e := by
  rw [mkHeader_eq]
  exact drop_take_append _ (hdrA_length he) (mkChk_length e)

theorem mkHeader_take_148 {e : TarEntry} (he : ValidEntry e) :
    (mkHeader e).take 148 = hdrA e := by
  rw [mkHeader_eq]
  exact List.take_left' (hdrA_length he)

theorem mkHeader_split_156 (e : TarEntry) :
    mkHeader e = (hdrA e ++ mkChk e) ++ hdrB := by
  rw [mkHeader_eq, List.append_assoc]

theorem mkHeader_drop_156 {e : TarEntry} (he : ValidEntry e) :
    (mkHeader e).drop 156 = hdrB := by
  rw [mkHeader_split_156]
  exact List.drop_left' (by simp [hdrA_length he, mkChk_length])

theorem mkHeader_typeflag {e : TarEntry} (he : ValidEntry e) : (mkHeader e)[156]! = 0x30 := by
  have hlen := mkHeader_length he
  have h156 : (hdrA e ++ mkChk e).length = 156 := by
    simp [hdrA_length he, mkChk_length]
  rw [getElem!_pos (mkHeader e) 156 (by omega)]
  simp only [mkHeader_split_156 e]
  rw [List.getElem_append_right (Nat.le_of_eq h156)]
  simp [h156, hdrB]

theorem mkHeader_prefix_split (e : TarEntry) :
    mkHeader e = (hdrA e ++ mkChk e ++ [0x30] ++ padField 100 [] ++
      [0x75, 0x73, 0x74, 0x61, 0x72, 0x00, 0x30, 0x30] ++ padField 32 [] ++ padField 32 [] ++
      octEnc 8 0 ++ octEnc 8 0) ++ (padField 155 [] ++ List.replicate 12 0) := by
  rw [mkHeader_eq]
  simp [hdrB, List.append_assoc]

theorem prefix_field {e : TarEntry} (he : ValidEntry e) :
    ((mkHeader e).drop 345).take 155 = List.replicate 155 0 := by
  rw [mkHeader_prefix_split, ← padField_nil 155]
  refine drop_take_append _ ?_ ?_
  · simp [hdrA_length he, mkChk_length, padField_nil_length]
  · exact padField_nil_length 155

/-! ## The checksum value and its verification -/

theorem spaces8_length : spaces8.length = 8 := rfl

theorem checksum_lt {e : TarEntry} (he : ValidEntry e) :
    sumBytes (headerRaw e spaces8) < 8 ^ 6 := by
  have h1 := sumBytes_le (headerRaw e spaces8)
  rw [headerRaw_length he spaces8_length] at h1
  have h2 : (8 : Nat) ^ 6 = 262144 := by decide
  omega

theorem octDec_mkChk {e : TarEntry} (he : ValidEntry e) :
    octDec (mkChk e) = some (sumBytes (headerRaw e spaces8)) := by
  rw [mkChk]
  exact octDec_octEnc_append 7 _ (by omega) (checksum_lt he) [0x20]

/-- Splicing spaces back into the checksum field recovers the checksummed header. -/
theorem header_checksum {e : TarEntry} (he : ValidEntry e) :
    sumBytes ((mkHeader e).take 148 ++ spaces8 ++ (mkHeader e).drop 156) =
      sumBytes (headerRaw e spaces8) := by
  rw [mkHeader_take_148 he, mkHeader_drop_156 he, headerRaw_eq, List.append_assoc]

/-! ## The header is not the zero terminator -/

theorem mkHeader_not_all_zero {e : TarEntry} (he : ValidEntry e) :
    (mkHeader e).all (· == 0) = false := by
  obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil (List.length_pos_iff.mp he.1)
  have hbmem : b ∈ e.name := by rw [hbl]; exact List.mem_cons_self ..
  have hbne : b ≠ 0 := fun h => he.2.2.1 (h ▸ hbmem)
  rw [List.all_eq_false]
  refine ⟨b, ?_, by simp [hbne]⟩
  rw [mkHeader_name_split, padField]
  exact List.mem_append_left _ (List.mem_append_left _ hbmem)

/-! ## Reader-side name and prefix computations -/

theorem takeWhile_padField_name {e : TarEntry} (he : ValidEntry e) :
    (padField 100 e.name).takeWhile (fun b => b != 0) = e.name := by
  have hall : ∀ x ∈ e.name, (x != 0) = true := by
    intro x hx
    have hne : x ≠ 0 := fun h => he.2.2.1 (h ▸ hx)
    simp [hne]
  rw [padField, takeWhile_append_of_all hall, List.takeWhile_replicate]
  simp

theorem takeWhile_replicate_zero :
    (List.replicate 155 (0 : UInt8)).takeWhile (fun b => b != 0) = [] := by
  rw [List.takeWhile_replicate]
  simp

/-! ## Body padding -/

theorem padTo512_length (bs : List UInt8) :
    (padTo512 bs).length = (bs.length + 511) / 512 * 512 := by
  simp [padTo512]
  omega

theorem padTo512_take (bs rest : List UInt8) :
    (padTo512 bs ++ rest).take bs.length = bs := by
  rw [padTo512, List.append_assoc]
  exact List.take_left' rfl

/-! ## Round trip -/

theorem untarBytes_entry {e : TarEntry} (he : ValidEntry e) (rest : List UInt8) (fuel : Nat) :
    untarBytes (fuel + 1) (entryBytes e ++ rest) = (untarBytes fuel rest).map (e :: ·) := by
  have h512 := mkHeader_length he
  have hassoc : entryBytes e ++ rest = mkHeader e ++ (padTo512 e.data ++ rest) := by
    rw [entryBytes, List.append_assoc]
  rw [hassoc]
  simp only [untarBytes, List.take_left' h512, List.drop_left' h512, h512,
    mkHeader_not_all_zero he, size_field he,
    octDec_octEnc 12 e.data.length (by omega) he.2.2.2,
    chksum_field he, octDec_mkChk he, header_checksum he,
    ne_eq, not_true, if_false, Bool.false_eq_true, Nat.lt_irrefl,
    List.drop_left' (padTo512_length e.data), padTo512_take,
    mkHeader_typeflag he, beq_self_eq_true, Bool.true_or, if_true,
    name_field he, takeWhile_padField_name he, prefix_field he, takeWhile_replicate_zero,
    List.isEmpty_nil]
  cases untarBytes fuel rest <;> rfl

theorem untarBytes_tar (es : List TarEntry) (h : ∀ e ∈ es, ValidEntry e) :
    ∀ fuel, es.length + 1 ≤ fuel → untarBytes fuel (tarBytes es) = some es := by
  induction es with
  | nil =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h0 : tarBytes [] = List.replicate 1024 0 := by
      simp only [tarBytes, List.map_nil, List.flatten_nil, List.nil_append]
    have hmin : min 512 1024 = 512 := by omega
    have htake : (List.replicate 1024 (0 : UInt8)).take 512 = List.replicate 512 0 := by
      rw [List.take_replicate, hmin]
    have hall : (List.replicate 512 (0 : UInt8)).all (· == 0) = true := by
      rw [List.all_replicate, if_neg (by omega)]
      exact beq_self_eq_true 0
    rw [h0]
    simp only [untarBytes, htake, List.length_replicate, Nat.lt_irrefl, if_false, hall,
      if_true]
  | cons e es ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have he : ValidEntry e := h e (List.mem_cons_self ..)
    have htar : tarBytes (e :: es) = entryBytes e ++ tarBytes es := by
      simp only [tarBytes, List.map_cons, List.flatten_cons, List.append_assoc]
    have hf' : es.length + 1 ≤ f := by
      simp only [List.length_cons] at hf; omega
    rw [htar, untarBytes_entry he _ f,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) f hf']
    rfl

theorem tarBytes_length_lower (es : List TarEntry) (h : ∀ e ∈ es, ValidEntry e) :
    512 * es.length + 1024 ≤ (tarBytes es).length := by
  induction es with
  | nil =>
    simp only [tarBytes, List.map_nil, List.flatten_nil, List.nil_append,
      List.length_replicate, List.length_nil]
    omega
  | cons e es ih =>
    have he : ValidEntry e := h e (List.mem_cons_self ..)
    have htar : tarBytes (e :: es) = entryBytes e ++ tarBytes es := by
      simp only [tarBytes, List.map_cons, List.flatten_cons, List.append_assoc]
    have hlen : (entryBytes e).length = 512 + (padTo512 e.data).length := by
      simp only [entryBytes, List.length_append, mkHeader_length he]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [htar]
    simp only [List.length_append, List.length_cons, hlen]
    omega

/-- Round trip: reading back a written archive recovers the entries. -/
theorem untar_tar (es : List TarEntry) (h : ∀ e ∈ es, ValidEntry e) :
    untar (tar es) = some es := by
  show untarBytes ((tarBytes es).length / 512 + 1) (tarBytes es) = some es
  apply untarBytes_tar es h
  have := tarBytes_length_lower es h
  omega

/-! ## Smoke tests -/

#guard untar (tar []) = some []
#guard untar (tar [⟨[0x61], [0x68, 0x69]⟩]) = some [⟨[0x61], [0x68, 0x69]⟩]

end TarGz
