/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.SplitSingle

/-!
# Chunked Single-Block Placement Tests

Positive and negative regression tests for `ProofLib.Placed.Split` (`textOkChunk`, `textOkTail`,
`dataOkChunk`, `dataOkTail`, `dataDisjointROB`, `walk_append`, and `checkDisjoint_spec_chunks`) on a
synthetic 8-word interned library `Gadget` with `adrp; add` linker relaxation and tail-merged
read-only data.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib.Testing.PlacedSplitSingle

open Arm64 Arm64.Process Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection ProofLib.ObjectLoad
  ProofLib.Placed.Split

/-- Little-endian bytes of a list of 32-bit instruction words. -/
def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Names table (strictly increasing): `buf` = 0, `ext` = 1, `f` = 2, `str` = 3, `tab` = 4. -/
def nameChars : List (List Char) :=
  [['b', 'u', 'f'], ['e', 'x', 't'], ['f'], ['s', 't', 'r'], ['t', 'a', 'b']]

/-- The synthetic library; data objects in address order (`tab`, `str`, `buf`). -/
def Gadget : Lib where
  name := "gadget"
  names := nameChars.map String.ofList
  code := wordsLE [0x94000000, 0x90000000, 0x91000000, 0x90000001, 0xF9400021, 0x94000000,
    0xD65F03C0, 0xD503201F]
  symbols := [(2, 0)]
  relocs := [⟨0, .call26, 1, 0, false⟩, ⟨4, .adrpHi21, 0, 0, false⟩, ⟨8, .addLo12, 0, 0, false⟩,
    ⟨12, .adrpHi21, 4, 0, false⟩, ⟨16, .ldst64Lo12, 4, 0, false⟩, ⟨20, .call26, 2, 0, false⟩]
  externs := [1]
  data := [{ sym := 4, align := 8, readOnly := true, bytes := List.replicate 8 0#8,
             relocs := [⟨0, .abs64, 2, 0, false⟩] },
           { sym := 3, align := 4, readOnly := true, bytes := List.replicate 4 0#8 },
           { sym := 0, align := 8, readOnly := false, zeroTail := 8 }]
  exports := [2]

/-- Layout relaxing the `adrp; add` pair at offset 4 to `nop; adr`; `str` at `tab + 4`. -/
def ly : Layout :=
  { base := 0x400000#64, addrs := [0x410000#64, 0x500000#64, 0#64, 0x401004#64, 0x401000#64],
    relax := [4] }

/-- `.symtab` of the image: `f` at the block base. -/
def symChars : List (List Char × BitVec 64) := [(['f'], 0x400000#64)]

/-- Code under `ly` (`bl 0x500000; nop; adr x0, 0x410000; adrp x1, 0x401000; ...; bl 0x400000`). -/
def code : List (BitVec 8) := wordsLE [0x94040000, 0xD503201F, 0x1007FFC0, 0xB0000001,
  0xF9400021, 0x97FFFFFB, 0xD65F03C0, 0xD503201F]

/-- Image with code bytes `c`, `tab`/`str` mapped with `tabPerm`, and `buf` with `bufPerm`. -/
def mkImg (c : List (BitVec 8)) (tabPerm bufPerm : Perm) : ElfImage where
  entry := 0x400000#64
  phdrVaddr := 0x400040#64
  phnum := 3
  segments := [{ start := 0x400000#64, perm := Perm.rx, bytes := c },
    { start := 0x401000#64, perm := tabPerm, bytes := [0#8, 0#8, 0x40#8, 0#8, 0#8, 0#8, 0#8, 0#8] },
    { start := 0x410000#64, perm := bufPerm, bytes := List.replicate 8 0#8 }]
  brkStart := 0x420000#64
  symbols := toStringAssoc symChars

def img : ElfImage := mkImg code Perm.ro Perm.rw

def segLens : List Nat := [32, 8, 8]

def rl : List (Snapshot.Region × Nat) := img.segments.zip segLens

/-! ## End-to-End Chunked Check -/

theorem segLens_eq : img.segments.map (fun r => rLen r.bytes) = segLens := by decide +kernel

/-- Words `[0, 8)`: ends inside the relaxed pair (`prev = true`), 2 relocations consumed. -/
theorem text0 : textOkChunk Gadget ly rl 0 false 0 8 true 2 = true := by decide +kernel
/-- Words `[8, 16)`: 4 relocations consumed. -/
theorem text1 : textOkChunk Gadget ly rl 8 true 2 16 false 4 = true := by decide +kernel
theorem text2 : textOkTail Gadget ly rl 16 false 4 = true := by decide +kernel

theorem data0 : dataOkChunk Gadget ly rl 0 2 = true := by decide +kernel
theorem data1 : dataOkTail Gadget ly rl 2 = true := by decide +kernel

theorem chk_nodup : namesNodup nameChars = true := by decide +kernel
theorem chk_ids : Gadget.idsOk = true := by decide +kernel
theorem chk_ptext : textPlaceableR Gadget ly = true := by decide +kernel
theorem chk_pdata : dataPlaceableR Gadget ly = true := by decide +kernel
theorem chk_exports : exportsOk Gadget ly nameChars (prepareCharAssocVal symChars) = true := by
  decide +kernel
/-- `str` overlaps `tab` (both read-only): accepted. -/
theorem chk_ddisj : dataDisjointROB Gadget ly = true := by decide +kernel

theorem gadget_checked : Gadget.toLib.Placeable (ly.toPlacement Gadget.names) ∧
    Gadget.toLib.InElf img (ly.toPlacement Gadget.names) ∧
    Gadget.toLib.DataDisjoint (ly.toPlacement Gadget.names) :=
  checkDisjoint_spec_chunks (symChars := symChars) rfl rfl segLens_eq chk_nodup chk_ids
    chk_ptext chk_pdata (textOkChunks_cons text0 (textOkChunks_cons text1 (textOkChunks_nil text2)))
    (dataOkChunks_cons data0 (dataOkChunks_nil data1)) chk_exports chk_ddisj

/-! ## `walk_append` -/

example : walk Gadget ly 0 false Gadget.relocs Gadget.code code = true := by
  rw [show Gadget.code = Gadget.code.take 8 ++ Gadget.code.drop 8 from
    (List.take_append_drop _ _).symm]
  exact walk_append (o := 0) (prev' := true) (rs' := Gadget.relocs.drop 2) (by decide +kernel)
    (by decide +kernel)

/-! ## Negative Tests -/

/--
error: Tactic `decide` proved that the proposition
  textOkChunk Gadget ly rl 0 false 0 8 false 2 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunk Gadget ly rl 0 false 0 8 false 2 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunk Gadget ly rl 0 false 0 8 true 3 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunk Gadget ly rl 0 false 0 8 true 3 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunk Gadget ly rl 0 false 0 6 false 2 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunk Gadget ly rl 0 false 0 6 false 2 = true := by decide +kernel

/-- `code` with the `adr` at offset 8 off by one word. -/
def codeBad : List (BitVec 8) := wordsLE [0x94040000, 0xD503201F, 0x1007FFA0, 0xB0000001,
  0xF9400021, 0x97FFFFFB, 0xD65F03C0, 0xD503201F]

def rlBad : List (Snapshot.Region × Nat) := (mkImg codeBad Perm.ro Perm.rw).segments.zip segLens

/-- The first chunk does not cover offset 8 and still passes; the second rejects it. -/
example : textOkChunk Gadget ly rlBad 0 false 0 8 true 2 = true := by decide +kernel

/--
error: Tactic `decide` proved that the proposition
  textOkChunk Gadget ly rlBad 8 true 2 16 false 4 = true
is false
-/
#guard_msgs (error, drop info) in
example : textOkChunk Gadget ly rlBad 8 true 2 16 false 4 = true := by decide +kernel

def rlRO : List (Snapshot.Region × Nat) := (mkImg code Perm.ro Perm.ro).segments.zip segLens

/--
error: Tactic `decide` proved that the proposition
  dataOkTail Gadget ly rlRO 2 = true
is false
-/
#guard_msgs (error, drop info) in
example : dataOkTail Gadget ly rlRO 2 = true := by decide +kernel

/-- `buf` (writable) at `tab + 4`, overlapping `tab` and `str`. -/
def lyOverlap : Layout :=
  { ly with addrs := [0x401004#64, 0x500000#64, 0#64, 0x401004#64, 0x401000#64] }

/--
error: Tactic `decide` proved that the proposition
  dataDisjointROB Gadget lyOverlap = true
is false
-/
#guard_msgs (error, drop info) in
example : dataDisjointROB Gadget lyOverlap = true := by decide +kernel

/-- `buf` disjoint from `tab` and `str` but below them, out of the data list's address order: the
    linear scan fails, and the pairwise fallback accepts it. -/
def lyUnsorted : Layout :=
  { ly with addrs := [0x400800#64, 0x500000#64, 0#64, 0x401004#64, 0x401000#64] }

theorem chk_ddisj_unsorted : dataDisjointROB Gadget lyUnsorted = true := by decide +kernel

/-- `buf` (writable) at `tab - 4`, below `tab` (out of address order) and overlapping it: both the
    scan and the pairwise fallback reject it. -/
def lyUnsortedOverlap : Layout :=
  { ly with addrs := [0x400ffc#64, 0x500000#64, 0#64, 0x401004#64, 0x401000#64] }

/--
error: Tactic `decide` proved that the proposition
  dataDisjointROB Gadget lyUnsortedOverlap = true
is false
-/
#guard_msgs (error, drop info) in
example : dataDisjointROB Gadget lyUnsortedOverlap = true := by decide +kernel

end ProofLib.Testing.PlacedSplitSingle

end
