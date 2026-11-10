/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Split
public meta import ProofLib.Placed.Split
public meta import ProofLib.ProgramReflection

/-!
# Split Kernel Check of a Multi-Block Placement Witness

Regression tests for `ProofLib.Placed.Split`: end-to-end chunked text and data placement checking
(`checkMultiDisjoint_spec_chunks`), `multiPlaceableB_of`, linear data-disjointness scanning
(`dataScanB`, `dataDisjointFastB`), one-pass relocation patching (`patchedDataLin`, `relocsLinOk`),
chunked segment-free index checks (`AllIdxChunks`), `toMultiPlacedLib_of_r`, and negative rejection
cases.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib.Testing.PlacedSplit

open Arm64 Arm64.Process Arm64.Obj Arm64.Obj.Interned ProofLib.ProgramReflection ProofLib.ObjectLoad
  ProofLib.Placed.Split

/-- Little-endian bytes of a list of 32-bit instruction words. -/
def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-! ## End-to-end split check on a 2-block library -/

def alphaNameChars : List (List Char) := [str_chars% "alpha", str_chars% "beta"]

/-- Two one-instruction (`RET`) blocks `alpha` and `beta`, both exported. -/
def alphaL : MultiLib where
  name := "alpha_lib"
  names := ["alpha", "beta"]
  blocks :=
    [ { code := wordsLE [0xd65f03c0#32], symbols := [(0, 0)] }
    , { code := wordsLE [0xd65f03c0#32], symbols := [(1, 0)] } ]
  exports := [0, 1]

theorem alphaL_names : alphaL.names = alphaNameChars.map String.ofList := by rfl_kernel

def alphaLy : MultiLayout where
  bases := [0x400000#64, 0x400004#64]
  addrs := [0x400000#64, 0x400004#64]

def alphaElfSymChars : List (List Char × BitVec 64) :=
  [(str_chars% "alpha", 0x400000#64), (str_chars% "beta", 0x400004#64)]

/-- One `r-x` segment holding both blocks back to back (two `RET`s, little-endian; a byte-list
    literal, as `seg_lens%` requires). -/
def alphaElf : ElfImage :=
  ElfImage.mk 0x400000#64 0x40#64 56 1
    [{ start := 0x400000#64, perm := { r := true, w := false, x := true },
       bytes := [0xc0#8, 0x03#8, 0x5f#8, 0xd6#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] }]
    0x401000#64 (toStringAssoc alphaElfSymChars)

theorem alphaElfSyms_eq : alphaElf.symbols = toStringAssoc alphaElfSymChars := rfl

def alphaL_segLens : List Nat := seg_lens% alphaElf

/-- info: [8] -/
#guard_msgs in
#eval alphaL_segLens

theorem alphaL_segLens_eq : alphaElf.segments.map (fun r => rLen r.bytes) = alphaL_segLens := by
  rfl_kernel

theorem alphaL_text0 : lTextChunk alphaL alphaLy (alphaElf.segments.zip alphaL_segLens) 0 1 = true := by
  rfl_kernel

theorem alphaL_text1 : lTextTail alphaL alphaLy (alphaElf.segments.zip alphaL_segLens) 1 = true := by
  rfl_kernel

theorem alphaL_data : lDataTail alphaL alphaLy (alphaElf.segments.zip alphaL_segLens) 0 = true := by
  rfl_kernel

theorem alphaL_chk_nodup : namesNodup alphaNameChars = true := by decide +kernel
theorem alphaL_chk_ids : alphaL.idsOk = true := by decide +kernel
theorem alphaL_chk_syms : blockSymsMatchB alphaL alphaLy = true := by decide +kernel
theorem alphaL_chk_ptext : textPlaceableAllB alphaL alphaLy = true := by decide +kernel
theorem alphaL_chk_pdisj : blocksDisjointB alphaL alphaLy = true := by decide +kernel
theorem alphaL_chk_psyms : blockSymsNodupB alphaL = true := by decide +kernel
theorem alphaL_chk_pdata : dataPlaceableAllB alphaL alphaLy = true := by decide +kernel
theorem alphaL_chk_pnone : dataNotBlockB alphaL = true := by decide +kernel
theorem alphaL_chk_exports :
    multiExportsOk alphaL alphaLy alphaNameChars (prepareCharAssocVal alphaElfSymChars) = true := by
  decide +kernel
theorem alphaL_chk_ddisj : dataDisjointFastB alphaL alphaLy = true := by decide +kernel

/-- `alphaL` is placeable at `alphaLy`, placed there in `alphaElf`, and its data is disjoint. -/
theorem alphaLib_ok :
    alphaL.toMultiPlacedLib.Placeable (alphaLy.toMultiPlacement alphaL.names) ∧
      alphaL.toMultiPlacedLib.InElf alphaElf (alphaLy.toMultiPlacement alphaL.names) ∧
      alphaL.toMultiPlacedLib.DataDisjoint (alphaLy.toMultiPlacement alphaL.names) :=
  checkMultiDisjoint_spec_chunks alphaL_names alphaElfSyms_eq alphaL_segLens_eq
    (lTextChunks_cons alphaL_text0 (lTextChunks_nil alphaL_text1)) (lDataChunks_nil alphaL_data)
    alphaL_chk_nodup alphaL_chk_ids alphaL_chk_syms alphaL_chk_ptext alphaL_chk_pdisj
    alphaL_chk_psyms alphaL_chk_pdata alphaL_chk_pnone alphaL_chk_exports alphaL_chk_ddisj

/-! ## `multiPlaceableB_of` -/

example : multiPlaceableB alphaL alphaLy = true :=
  multiPlaceableB_of alphaL_chk_ptext alphaL_chk_pdisj alphaL_chk_psyms alphaL_chk_pdata
    alphaL_chk_pnone

/-! ## Linear data-disjointness check -/

/-- `alphaL` with three data objects `x`, `y`, `z` (2, 1 and 1 bytes). -/
def alphaLD (ro : Bool) : MultiLib :=
  { alphaL with
    names := ["alpha", "beta", "x", "y", "z"]
    data :=
      [ { sym := 2, readOnly := ro, bytes := [0#8, 0#8] }
      , { sym := 3, readOnly := ro, bytes := [0#8] }
      , { sym := 4, readOnly := ro, bytes := [0#8] } ] }

/-- `x` at `0x500000`, `y` inside `x` at `0x500001`, `z` at `0x500002`. -/
def alphaLyOverlapD : MultiLayout :=
  { alphaLy with addrs := [0x400000#64, 0x400004#64, 0x500000#64, 0x500001#64, 0x500002#64] }

/-- `x`, `y`, `z` disjoint but out of address order: `z` before `y`. -/
def alphaLyUnsortedD : MultiLayout :=
  { alphaLy with addrs := [0x400000#64, 0x400004#64, 0x500000#64, 0x500003#64, 0x500002#64] }

/-- Read-only objects may overlap (tail-merged bytes): the scan alone accepts them. -/
example : dataScanB 0 0 (dataEntriesL (alphaLD true) alphaLyOverlapD) = true := by decide +kernel

/-- Unsorted disjoint writable objects: the scan rejects them and the pairwise fallback accepts. -/
example : dataScanB 0 0 (dataEntriesL (alphaLD false) alphaLyUnsortedD) = false := by
  decide +kernel
example : dataDisjointFastB (alphaLD false) alphaLyUnsortedD = true := by decide +kernel

example : dataDisjointFastB (alphaLD false) alphaLyUnsortedD =
    multiDataDisjointB (alphaLD false) alphaLyUnsortedD := dataDisjointFastB_eq _ _

/--
error: Tactic `decide` proved that the proposition
  dataDisjointFastB (alphaLD false) alphaLyOverlapD = true
is false
-/
#guard_msgs (error, drop info) in
example : dataDisjointFastB (alphaLD false) alphaLyOverlapD = true := by decide +kernel

/-! ## Linear data relocation patching -/

/-- `alphaL` with a 20-byte data object `p` holding an `abs64` to `alpha`, a `call26` (writes no
    bytes) and a `prel32` to `beta + 4`, in the given relocation order. -/
def alphaLR (rs : List Reloc) : MultiLib :=
  { alphaL with
    names := ["alpha", "beta", "p"]
    data := [{ sym := 2, bytes := List.replicate 20 0xaa#8, zeroTail := 2, relocs := rs }] }

def alphaRelocs : List Reloc :=
  [ { off := 0, kind := .abs64, sym := 0 }
  , { off := 8, kind := .call26, sym := 1 }
  , { off := 12, kind := .prel32, sym := 1, addend := 4 } ]

/-- `p` at `0x500000`. -/
def alphaLyR : MultiLayout :=
  { alphaLy with addrs := [0x400000#64, 0x400004#64, 0x500000#64] }

def alphaDataR (rs : List Reloc) : Data := (alphaLR rs).data.headD default

/-- The single-block view of `alphaLR rs` the data walk patches against. -/
def alphaLibR (rs : List Reloc) : Lib := (alphaLR rs).blockLib { code := [] }

/-- Sorted, disjoint, in-bounds relocations take the one-pass path. -/
example : relocsLinOk 20 0 alphaRelocs = true := by decide +kernel

example : patchedDataLin (alphaLibR alphaRelocs) alphaLyR.dataLayout (alphaDataR alphaRelocs) =
    [0x00#8, 0x00#8, 0x40#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
     0xaa#8, 0xaa#8, 0xaa#8, 0xaa#8,
     0xfc#8, 0xff#8, 0xef#8, 0xff#8,
     0xaa#8, 0xaa#8, 0xaa#8, 0xaa#8, 0x00#8, 0x00#8] := by
  decide +kernel

example : patchedDataLin (alphaLibR alphaRelocs) alphaLyR.dataLayout (alphaDataR alphaRelocs) =
    patchedDataId (alphaLibR alphaRelocs) alphaLyR.dataLayout (alphaDataR alphaRelocs) := by
  decide +kernel

/-- Unsorted relocations fall back to `patchedDataId`, with the same bytes. -/
example : relocsLinOk 20 0 alphaRelocs.reverse = false := by decide +kernel

example : patchedDataLin (alphaLibR alphaRelocs.reverse) alphaLyR.dataLayout (alphaDataR alphaRelocs.reverse) =
    patchedDataId (alphaLibR alphaRelocs) alphaLyR.dataLayout (alphaDataR alphaRelocs) := by
  decide +kernel

/-- An `abs64` at offset 4 overlaps the `abs64` at offset 0. -/
def alphaRelocsOverlap : List Reloc :=
  [ { off := 0, kind := .abs64, sym := 0 }, { off := 4, kind := .abs64, sym := 1 } ]

/--
error: Tactic `decide` proved that the proposition
  relocsLinOk 20 0 alphaRelocsOverlap = true
is false
-/
#guard_msgs (error, drop info) in
example : relocsLinOk 20 0 alphaRelocsOverlap = true := by decide +kernel

/-- A relocation ending past the object (`abs64` at 16 of 20 bytes) is out of bounds. -/
example : relocsLinOk 20 0 [{ off := 16, kind := .abs64, sym := 0 }] = false := by decide +kernel

/-! ## Chunked segment-free checks and library equality -/

/-- `blockSymsMatchB`, `textPlaceableAllB` and `dataNotBlockB` from chunks `[0, 1)` and `[1, end)`. -/
example : blockSymsMatchB alphaL alphaLy = true :=
  blockSymsMatchB_of_chunks (allIdxChunks_cons (s := 0) (t := 1) (by decide +kernel) (allIdxChunks_nil (by decide +kernel)))

example : textPlaceableAllB alphaL alphaLy = true :=
  textPlaceableAllB_of_chunks (allIdxChunks_cons (s := 0) (t := 1) (by decide +kernel) (allIdxChunks_nil (by decide +kernel)))

example : dataNotBlockB (alphaLD true) = true :=
  dataNotBlockB_of_chunks (allIdxChunks_cons (s := 0) (t := 2) (by decide +kernel) (allIdxChunks_nil (by decide +kernel)))

/-- `alphaL.toMultiPlacedLib` written out, as a trusted placed-object file states it. -/
def alphaLib : MultiPlacedLib where
  name := "alpha_lib"
  blocks :=
    [ { code := wordsLE [0xd65f03c0#32], symbols := [("alpha", 0)] }
    , { code := wordsLE [0xd65f03c0#32], symbols := [("beta", 0)] } ]
  exports := ["alpha", "beta"]

/-- The library equality by the kernel-cheap `rGetD` lookups. -/
example : alphaLib = alphaL.toMultiPlacedLib := toMultiPlacedLib_of_r (by rfl_kernel)

example : rGetD [10, 20, 30] 1 0 = 20 := by decide +kernel
example : rGetD [10, 20, 30] 3 0 = 0 := by decide +kernel

/-- A library whose `beta` export is misnamed is not `toMultiPlacedLibR alphaL`. -/
def alphaLibBad : MultiPlacedLib := { alphaLib with exports := ["alpha", "gamma"] }

/--
error: Tactic `decide` proved that the proposition
  alphaLibBad.exports = (toMultiPlacedLibR alphaL).exports
is false
-/
#guard_msgs (error, drop info) in
example : alphaLibBad.exports = (toMultiPlacedLibR alphaL).exports := by decide +kernel

/-- `alphaLy` with `beta`'s address 4 bytes past its block base. -/
def alphaLyBadAddr : MultiLayout := { alphaLy with addrs := [0x400000#64, 0x400008#64] }

/-- The chunk with block `alpha` passes; the tail chunk from block `beta` fails. -/
example : allIdxChunk (blockSymsMatchAt alphaLyBadAddr) alphaL.blocks 0 1 = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  allIdxTail (blockSymsMatchAt alphaLyBadAddr) alphaL.blocks 1 = true
is false
-/
#guard_msgs (error, drop info) in
example : allIdxTail (blockSymsMatchAt alphaLyBadAddr) alphaL.blocks 1 = true := by decide +kernel

/-! ## Negative tests -/

/-- Both blocks at the same base. -/
def alphaLyOverlap : MultiLayout where
  bases := [0x400000#64, 0x400000#64]
  addrs := [0x400000#64, 0x400000#64]

/--
error: Tactic `decide` proved that the proposition
  blocksDisjointB alphaL alphaLyOverlap = true
is false
-/
#guard_msgs (error, drop info) in
example : blocksDisjointB alphaL alphaLyOverlap = true := by decide +kernel

/-- `alphaL` with a data object named `beta`, which block 1 also defines. -/
def alphaLDataClash : MultiLib := { alphaL with data := [{ sym := 1, bytes := [0#8] }] }

/--
error: Tactic `decide` proved that the proposition
  dataNotBlockB alphaLDataClash = true
is false
-/
#guard_msgs (error, drop info) in
example : dataNotBlockB alphaLDataClash = true := by decide +kernel

/-- `.symtab` with `beta` 4 bytes past its block. -/
def alphaElfSymCharsBad : List (List Char × BitVec 64) :=
  [(str_chars% "alpha", 0x400000#64), (str_chars% "beta", 0x400008#64)]

/--
error: Tactic `decide` proved that the proposition
  multiExportsOk alphaL alphaLy alphaNameChars (prepareCharAssocVal alphaElfSymCharsBad) = true
is false
-/
#guard_msgs (error, drop info) in
example :
    multiExportsOk alphaL alphaLy alphaNameChars (prepareCharAssocVal alphaElfSymCharsBad) = true := by
  decide +kernel

/-- Block `beta` at `0x400002`, where the segment holds `5f d6 c0 03`, not its `RET`. -/
def alphaLyShift : MultiLayout where
  bases := [0x400000#64, 0x400002#64]
  addrs := [0x400000#64, 0x400002#64]

/-- The first chunk (block `alpha` only) still passes; the tail chunk from block `1` fails. -/
example : lTextChunk alphaL alphaLyShift (alphaElf.segments.zip alphaL_segLens) 0 1 = true := by
  decide +kernel

/--
error: Tactic `decide` proved that the proposition
  lTextTail alphaL alphaLyShift (alphaElf.segments.zip alphaL_segLens) 1 = true
is false
-/
#guard_msgs (error, drop info) in
example : lTextTail alphaL alphaLyShift (alphaElf.segments.zip alphaL_segLens) 1 = true := by
  decide +kernel

end ProofLib.Testing.PlacedSplit

end
