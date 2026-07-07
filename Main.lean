-- SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
-- SPDX-License-Identifier: MIT

import TarGz

/-!
CLI twin of the ES6 `targz.mjs` program, backed by the verified Lean model.

Subcommands:
- `targz c <out> <files...>` — create a .tgz from the given files (in order)
- `targz x <archive> [-C <dir>]` — extract an archive
- `targz t <archive>` — list entry names
-/

open TarGz

def listToByteArray (l : List UInt8) : ByteArray :=
  ByteArray.mk (Array.mk l)

def usage : String :=
  "usage: targz c <out> <files...> | targz x <archive> [-C <dir>] | targz t <archive>"

/-- Entry name for a file argument: backslashes normalized to forward slashes. -/
def entryName (arg : String) : String :=
  arg.replace "\\" "/"

def cmdCreate (out : String) (files : List String) : IO UInt32 := do
  let mut entries : List TarEntry := []
  for f in files do
    let bytes ← IO.FS.readBinFile f
    let e : TarEntry := ⟨(entryName f).toUTF8.toList, bytes.toList⟩
    if _h : ValidEntry e then
      entries := entries ++ [e]
    else
      IO.eprintln s!"targz: invalid entry (name must be 1..100 bytes, no NUL; data < 8^11 bytes): {f}"
      return 1
  IO.FS.writeBinFile out (listToByteArray (create entries))
  return 0

/-- Reject absolute names, drive-letter colons, and `..` path segments. -/
def unsafeName (name : String) : Bool :=
  name.startsWith "/" || name.contains ':' || (name.splitOn "/").any (· == "..")

def cmdExtract (archive : String) (dir : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile archive
  match extract bytes.toList with
  | none =>
    IO.eprintln s!"targz: not a valid .tgz archive: {archive}"
    return 1
  | some entries =>
    for e in entries do
      match String.fromUTF8? (listToByteArray e.name) with
      | none =>
        IO.eprintln "targz: entry name is not valid UTF-8"
        return 1
      | some name =>
        if unsafeName name then
          IO.eprintln s!"targz: refusing to extract unsafe entry name: {name}"
          return 1
        let path := (name.splitOn "/").foldl
          (fun (p : System.FilePath) c => p / System.FilePath.mk c)
          (System.FilePath.mk dir)
        if let some parent := path.parent then
          IO.FS.createDirAll parent
        IO.FS.writeBinFile path (listToByteArray e.data)
    return 0

def cmdList (archive : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile archive
  match extract bytes.toList with
  | none =>
    IO.eprintln s!"targz: not a valid .tgz archive: {archive}"
    return 1
  | some entries =>
    for e in entries do
      match String.fromUTF8? (listToByteArray e.name) with
      | none =>
        IO.eprintln "targz: entry name is not valid UTF-8"
        return 1
      | some name =>
        IO.println name
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println usage
    return 0
  | "c" :: out :: files =>
    cmdCreate out files
  | ["x", archive] =>
    cmdExtract archive "."
  | ["x", archive, "-C", dir] =>
    cmdExtract archive dir
  | ["t", archive] =>
    cmdList archive
  | _ =>
    IO.eprintln usage
    return 1
