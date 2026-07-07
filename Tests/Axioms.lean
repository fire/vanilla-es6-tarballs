import TarGz

/-!
Axiom audit. `#print axioms` output for each headline theorem must mention
nothing beyond `propext`, `Classical.choice`, `Quot.sound` (in particular no
`sorryAx` and no `Lean.ofReduceBool` from `native_decide`). The `#guard_msgs`
snapshots below fail the build if any axiom set ever grows or changes.
-/

/-- info: 'TarGz.extract_create' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TarGz.extract_create

/-- info: 'TarGz.inflate_deflate_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TarGz.inflate_deflate_append

/-- info: 'TarGz.gunzip_gzip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TarGz.gunzip_gzip

/-- info: 'TarGz.untar_tar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TarGz.untar_tar

/-- info: 'TarGz.crc32_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TarGz.crc32_eq_spec

/-- info: 'TarGz.decodeSym_encodeSym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TarGz.decodeSym_encodeSym

/-- info: 'TarGz.resolve_tokenize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms TarGz.resolve_tokenize
