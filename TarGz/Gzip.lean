import TarGz.Deflate
import TarGz.Crc32

/-!
# gzip container (RFC 1952)

Creation is deterministic: single member, `FLG = 0`, `MTIME = 0`, `XFL = 0`,
`OS = 255`. Extraction tolerates the optional header fields real gzip writes
(FEXTRA / FNAME / FCOMMENT / FHCRC are skipped) and verifies CRC32 + ISIZE.
-/

namespace TarGz

def gzipHeader : List UInt8 := [0x1F, 0x8B, 8, 0, 0, 0, 0, 0, 0, 255]

def gzip (d : List UInt8) : List UInt8 :=
  gzipHeader ++ deflate d ++ writeLE32 (crc32 d).toNat
    ++ writeLE32 (d.length % 4294967296)

/-- Drop bytes up to and including the first NUL. -/
def skipZString : List UInt8 → Option (List UInt8)
  | [] => none
  | b :: rest => if b = 0 then some rest else skipZString rest

/-- Skip the optional header fields announced by FLG (RFC 1952 order:
FEXTRA, FNAME, FCOMMENT, FHCRC). -/
def skipFlagFields (flg : UInt8) (bs : List UInt8) : Option (List UInt8) :=
  let stepExtra :=
    if flg &&& 4 = 0 then some bs
    else match readLE16 bs with
      | none => none
      | some (n, r) => if n ≤ r.length then some (r.drop n) else none
  match stepExtra with
  | none => none
  | some bs1 =>
    match (if flg &&& 8 = 0 then some bs1 else skipZString bs1) with
    | none => none
    | some bs2 =>
      match (if flg &&& 16 = 0 then some bs2 else skipZString bs2) with
      | none => none
      | some bs3 =>
        if flg &&& 2 = 0 then some bs3
        else if 2 ≤ bs3.length then some (bs3.drop 2) else none

def gunzip (bs : List UInt8) : Option (List UInt8) :=
  match bs with
  | id1 :: id2 :: cm :: flg :: _m0 :: _m1 :: _m2 :: _m3 :: _xf :: _os :: rest =>
    if id1 = 0x1F ∧ id2 = 0x8B ∧ cm = 8 then
      match skipFlagFields flg rest with
      | none => none
      | some rest1 =>
        match inflate rest1 with
        | none => none
        | some (payload, rest2) =>
          match readLE32 rest2 with
          | none => none
          | some (crcv, rest3) =>
            match readLE32 rest3 with
            | none => none
            | some (isize, _) =>
              if crcv = (crc32 payload).toNat
                  ∧ isize = payload.length % 4294967296
              then some payload
              else none
    else none
  | _ => none

/-! ## Round trip -/

theorem skipFlagFields_zero (bs : List UInt8) : skipFlagFields 0 bs = some bs := rfl

theorem gunzip_gzip (d : List UInt8) : gunzip (gzip d) = some d := by
  have hcrc : (crc32 d).toNat < 2 ^ 32 := by
    have := UInt32.toNat_lt (crc32 d)
    simpa using this
  have hisize : d.length % 4294967296 < 2 ^ 32 := by omega
  have hisize' : readLE32 (writeLE32 (d.length % 4294967296))
      = some (d.length % 4294967296, []) := by
    have := readLE32_writeLE32 (r := []) hisize
    simpa using this
  unfold gzip gzipHeader
  simp only [List.cons_append, List.nil_append]
  unfold gunzip
  simp only [List.append_assoc, skipFlagFields_zero, inflate_deflate_append,
    readLE32_writeLE32 hcrc, hisize']
  simp

end TarGz
