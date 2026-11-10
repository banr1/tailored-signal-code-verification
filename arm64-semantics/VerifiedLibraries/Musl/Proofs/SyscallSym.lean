/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.ExecHelpersSym
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Relocatable `musl` Syscall Wrapper Blocks

Defines the 11 relocatable `Obj.CodeBlock`s (`muslSysPlacedLib`) and instruction-fetch tables for
`musl` 1.2.5's AArch64 thread-local `errno` (`__errno_location`, `__syscall_ret`), cancellation
trampoline (`sccp`, `__syscall_cp`, `__aio_close`), and file-descriptor wrappers (`close`, `read`,
`write`, `open`, `fstat`, `fstatat`).
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.Musl

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

def muslCode00_errno_location : List (BitVec 8) := wordsLE [
  0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32]

def muslCode01_syscall_ret : List (BitVec 8) := wordsLE [
  0xa9be7bfd#32, 0xb140041f#32, 0x910003fd#32, 0xf9000bf3#32,
  0xaa0003f3#32, 0x54000088#32, 0xf9400bf3#32, 0xa8c27bfd#32,
  0xd65f03c0#32, 0x94000000#32, 0xaa0003e1#32, 0x4b1303f3#32,
  0x92800000#32, 0xb9000033#32, 0x17fffff8#32]

def muslCode02_sccp : List (BitVec 8) := wordsLE [
  0xaa0003e8#32, 0xaa0103e0#32, 0xaa0203e1#32, 0xaa0303e2#32,
  0xaa0403e3#32, 0xaa0503e4#32, 0xaa0603e5#32, 0xd4000001#32,
  0xd65f03c0#32]

def muslCode03_syscall_cp : List (BitVec 8) := wordsLE [
  0x14000000#32]

def muslCode04_aio_close : List (BitVec 8) := wordsLE [
  0xd65f03c0#32]

def muslCode05_close : List (BitVec 8) := wordsLE [
  0xa9bf7bfd#32, 0x910003fd#32, 0x94000000#32, 0x93407c01#32,
  0xd2800006#32, 0xd2800005#32, 0xd2800004#32, 0xd2800003#32,
  0xd2800002#32, 0xd2800720#32, 0x94000000#32, 0x3100101f#32,
  0x1a9f1000#32, 0x93407c00#32, 0x94000000#32, 0xa8c17bfd#32,
  0xd65f03c0#32]

def muslCode06_read : List (BitVec 8) := wordsLE [
  0xa9bf7bfd#32, 0xaa0103e4#32, 0xaa0203e3#32, 0x910003fd#32,
  0x93407c01#32, 0xaa0403e2#32, 0xd2800006#32, 0xd2800005#32,
  0xd2800004#32, 0xd28007e0#32, 0x94000000#32, 0xa8c17bfd#32,
  0x14000000#32]

def muslCode07_write : List (BitVec 8) := wordsLE [
  0xa9bf7bfd#32, 0xaa0103e4#32, 0xaa0203e3#32, 0x910003fd#32,
  0x93407c01#32, 0xaa0403e2#32, 0xd2800006#32, 0xd2800005#32,
  0xd2800004#32, 0xd2800800#32, 0x94000000#32, 0xa8c17bfd#32,
  0x14000000#32]

def muslCode08_open : List (BitVec 8) := wordsLE [
  0xa9bb7bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0x2a0103f3#32,
  0xf90027e2#32, 0xaa0003e2#32, 0x373000d3#32, 0x12122020#32,
  0xd2800004#32, 0x120a6000#32, 0x7150101f#32, 0x54000101#32,
  0xb9404be4#32, 0x910103e1#32, 0x910143e3#32, 0x128000e0#32,
  0xa9020fe3#32, 0xf9001be1#32, 0x29077fe0#32, 0x320f0263#32,
  0xd2800006#32, 0xd2800005#32, 0x92800c61#32, 0x93407c63#32,
  0xd2800700#32, 0x94000000#32, 0x93407c03#32, 0x37f800e0#32,
  0x369800d3#32, 0xd2800328#32, 0xaa0303e0#32, 0xd2800041#32,
  0xd2800022#32, 0xd4000001#32, 0xaa0303e0#32, 0x94000000#32,
  0xf9400bf3#32, 0xa8c57bfd#32, 0xd65f03c0#32]

def muslCode09_fstat : List (BitVec 8) := wordsLE [
  0x37f800c0#32, 0xaa0103e2#32, 0x52820003#32, 0x90000001#32,
  0x91000021#32, 0x14000000#32, 0xa9bf7bfd#32, 0x92800100#32,
  0x910003fd#32, 0x94000000#32, 0xa8c17bfd#32, 0xd65f03c0#32]

def muslCode10_fstatat : List (BitVec 8) := wordsLE [
  0xa9b37bfd#32, 0x93407c06#32, 0x7140047f#32, 0x910003fd#32,
  0xa90153f3#32, 0x7a4008c1#32, 0xaa0203f3#32, 0xaa0103e5#32,
  0x910143e2#32, 0x5400044b#32, 0x39400020#32, 0x35000400#32,
  0xaa0603e0#32, 0xaa0203e1#32, 0xd2800a08#32, 0xd4000001#32,
  0x3100241f#32, 0x540003e1#32, 0xaa0603e0#32, 0xd2800328#32,
  0xd2800021#32, 0xd4000001#32, 0x92800101#32, 0xb7f80760#32,
  0xaa0603e0#32, 0xaa0503e1#32, 0xd28009e8#32, 0xd2820003#32,
  0xd4000001#32, 0x3100581f#32, 0x54000241#32, 0x9100c3f4#32,
  0x2a0603e1#32, 0xaa1403e0#32, 0xf90017e2#32, 0x94000000#32,
  0xaa1403e1#32, 0xd28009e8#32, 0x92800c60#32, 0xd2800003#32,
  0xf94017e2#32, 0xd4000001#32, 0x14000006#32, 0xaa0603e0#32,
  0xaa0503e1#32, 0x93407c63#32, 0xd28009e8#32, 0xd4000001#32,
  0x93407c01#32, 0x35000420#32, 0xf9402be0#32, 0xf9000260#32,
  0xf9402fe0#32, 0xf9000660#32, 0xf94033e0#32, 0xf9000a60#32,
  0xf94037e0#32, 0xf9000e60#32, 0xa9027e7f#32, 0xd2800001#32,
  0xb9408be2#32, 0xf9403be0#32, 0xf9001260#32, 0xa9037e7f#32,
  0xf94043e0#32, 0xf9001a60#32, 0xf9404be0#32, 0xb9003a62#32,
  0xf9002260#32, 0xf9404fe2#32, 0xf9002662#32, 0xf94053e0#32,
  0xf9002a60#32, 0xf94057e2#32, 0xf9002e62#32, 0xf9405be0#32,
  0xf9003260#32, 0xa9077e7f#32, 0xf9405fe2#32, 0xf9003662#32,
  0xf94063e0#32, 0xf9003a60#32, 0xaa0103e0#32, 0x94000000#32,
  0xa94153f3#32, 0xa8cd7bfd#32, 0xd65f03c0#32]

def muslBlk00_errno_location : CodeBlock where
  code := muslCode00_errno_location
  symbols := [("___errno_location", 0), ("__errno_location", 0)]
  relocs := []
  externs := []

def muslBlk01_syscall_ret : CodeBlock where
  code := muslCode01_syscall_ret
  symbols := [("__syscall_ret", 0)]
  relocs := [{ off := 36, kind := .call26, sym := "___errno_location" }]
  externs := ["___errno_location"]

def muslBlk02_sccp : CodeBlock where
  code := muslCode02_sccp
  symbols := [("sccp", 0)]
  relocs := []
  externs := []

def muslBlk03_syscall_cp : CodeBlock where
  code := muslCode03_syscall_cp
  symbols := [("__syscall_cp", 0)]
  relocs := [{ off := 0, kind := .jump26, sym := "sccp" }]
  externs := ["sccp"]

def muslBlk04_aio_close : CodeBlock where
  code := muslCode04_aio_close
  symbols := [("__aio_close", 0)]
  relocs := []
  externs := []

def muslBlk05_close : CodeBlock where
  code := muslCode05_close
  symbols := [("close", 0)]
  relocs := [
    { off := 8, kind := .call26, sym := "__aio_close" },
    { off := 40, kind := .call26, sym := "__syscall_cp" },
    { off := 56, kind := .call26, sym := "__syscall_ret" }]
  externs := ["__aio_close", "__syscall_cp", "__syscall_ret"]

def muslBlk06_read : CodeBlock where
  code := muslCode06_read
  symbols := [("read", 0)]
  relocs := [
    { off := 40, kind := .call26, sym := "__syscall_cp" },
    { off := 48, kind := .jump26, sym := "__syscall_ret" }]
  externs := ["__syscall_cp", "__syscall_ret"]

def muslBlk07_write : CodeBlock where
  code := muslCode07_write
  symbols := [("write", 0)]
  relocs := [
    { off := 40, kind := .call26, sym := "__syscall_cp" },
    { off := 48, kind := .jump26, sym := "__syscall_ret" }]
  externs := ["__syscall_cp", "__syscall_ret"]

def muslBlk08_open : CodeBlock where
  code := muslCode08_open
  symbols := [("open", 0)]
  relocs := [
    { off := 100, kind := .call26, sym := "__syscall_cp" },
    { off := 140, kind := .call26, sym := "__syscall_ret" }]
  externs := ["__syscall_cp", "__syscall_ret"]

def muslBlk09_fstat : CodeBlock where
  code := muslCode09_fstat
  symbols := [("fstat", 0)]
  relocs := [
    { off := 12, kind := .adrpHi21, sym := "muslEmptyCStr" },
    { off := 16, kind := .addLo12, sym := "muslEmptyCStr" },
    { off := 20, kind := .jump26, sym := "fstatat" },
    { off := 36, kind := .call26, sym := "__syscall_ret" }]
  externs := ["fstatat", "__syscall_ret", "muslEmptyCStr"]

def muslBlk10_fstatat : CodeBlock where
  code := muslCode10_fstatat
  symbols := [("fstatat", 0)]
  relocs := [
    { off := 140, kind := .call26, sym := "__procfdname" },
    { off := 332, kind := .call26, sym := "__syscall_ret" }]
  externs := ["__procfdname", "__syscall_ret"]

def muslEmptyCStrData : SymDataInfo :=
  { sym := "muslEmptyCStr", align := 1, readOnly := true, bytes := [0x00#8] }

/-- Composable 11-block `MultiPlacedLib` for `musl` 1.2.5's AArch64 syscall wrappers. -/
def muslSysPlacedLib : MultiPlacedLib where
  name := "musl_sys"
  blocks := [
    muslBlk00_errno_location, muslBlk01_syscall_ret, muslBlk02_sccp,
    muslBlk03_syscall_cp, muslBlk04_aio_close, muslBlk05_close,
    muslBlk06_read, muslBlk07_write, muslBlk08_open,
    muslBlk09_fstat, muslBlk10_fstatat]
  data := [muslEmptyCStrData]
  exports := [
    "___errno_location", "__errno_location", "__syscall_ret",
    "__syscall_cp", "__aio_close", "close", "read", "write",
    "open", "fstat", "fstatat"]

class MuslSysPlacement where
  mpl : MultiPlacement
  placeable : muslSysPlacedLib.Placeable mpl

abbrev muslSysMpl [MuslSysPlacement] : MultiPlacement := MuslSysPlacement.mpl

def muslSysLib00 : PlacedLib := muslSysPlacedLib.blockLib 0
def muslSysPl00 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 0
theorem muslSysPlaceable00 [MuslSysPlacement] : muslSysLib00.Placeable muslSysPl00 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC00 [MuslSysPlacement] : Program := muslSysLib00.program muslSysPl00

def muslSysLib01 : PlacedLib := muslSysPlacedLib.blockLib 1
def muslSysPl01 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 1
theorem muslSysPlaceable01 [MuslSysPlacement] : muslSysLib01.Placeable muslSysPl01 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC01 [MuslSysPlacement] : Program := muslSysLib01.program muslSysPl01

def muslSysLib02 : PlacedLib := muslSysPlacedLib.blockLib 2
def muslSysPl02 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 2
theorem muslSysPlaceable02 [MuslSysPlacement] : muslSysLib02.Placeable muslSysPl02 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC02 [MuslSysPlacement] : Program := muslSysLib02.program muslSysPl02

def muslSysLib03 : PlacedLib := muslSysPlacedLib.blockLib 3
def muslSysPl03 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 3
theorem muslSysPlaceable03 [MuslSysPlacement] : muslSysLib03.Placeable muslSysPl03 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC03 [MuslSysPlacement] : Program := muslSysLib03.program muslSysPl03

def muslSysLib04 : PlacedLib := muslSysPlacedLib.blockLib 4
def muslSysPl04 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 4
theorem muslSysPlaceable04 [MuslSysPlacement] : muslSysLib04.Placeable muslSysPl04 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC04 [MuslSysPlacement] : Program := muslSysLib04.program muslSysPl04

def muslSysLib05 : PlacedLib := muslSysPlacedLib.blockLib 5
def muslSysPl05 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 5
theorem muslSysPlaceable05 [MuslSysPlacement] : muslSysLib05.Placeable muslSysPl05 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC05 [MuslSysPlacement] : Program := muslSysLib05.program muslSysPl05

def muslSysLib06 : PlacedLib := muslSysPlacedLib.blockLib 6
def muslSysPl06 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 6
theorem muslSysPlaceable06 [MuslSysPlacement] : muslSysLib06.Placeable muslSysPl06 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC06 [MuslSysPlacement] : Program := muslSysLib06.program muslSysPl06

def muslSysLib07 : PlacedLib := muslSysPlacedLib.blockLib 7
def muslSysPl07 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 7
theorem muslSysPlaceable07 [MuslSysPlacement] : muslSysLib07.Placeable muslSysPl07 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC07 [MuslSysPlacement] : Program := muslSysLib07.program muslSysPl07

def muslSysLib08 : PlacedLib := muslSysPlacedLib.blockLib 8
def muslSysPl08 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 8
theorem muslSysPlaceable08 [MuslSysPlacement] : muslSysLib08.Placeable muslSysPl08 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC08 [MuslSysPlacement] : Program := muslSysLib08.program muslSysPl08

def muslSysLib09 : PlacedLib := muslSysPlacedLib.blockLib 9
def muslSysPl09 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 9
theorem muslSysPlaceable09 [MuslSysPlacement] : muslSysLib09.Placeable muslSysPl09 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC09 [MuslSysPlacement] : Program := muslSysLib09.program muslSysPl09

def muslSysLib10 : PlacedLib := muslSysPlacedLib.blockLib 10
def muslSysPl10 [MuslSysPlacement] : Placement := muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl 10
theorem muslSysPlaceable10 [MuslSysPlacement] : muslSysLib10.Placeable muslSysPl10 :=
  muslSysPlacedLib.placeable_blockLib (by decide) MuslSysPlacement.placeable
def muslSysPC10 [MuslSysPlacement] : Program := muslSysLib10.program muslSysPl10

set_option maxRecDepth 200000
set_option linter.literalFetch false

def muslSysProg00 : Program := { code := muslBlk00_errno_location.code, symbols := muslBlk00_errno_location.symbols }
def muslSysTree00 : WordTree := word_tree_of% muslSysProg00
theorem muslSys00_code_eq : muslSysLib00.text.code = muslSysTree00.toBytes := by rfl_kernel
theorem muslSys00_tree_size : muslSysTree00.checkSize? = some 3 := by rfl_kernel
def muslSysSymChars00 : List (List Char × Nat) := sym_chars_of% muslSysProg00
theorem muslSys00_symbols_eq : muslSysLib00.text.symbols = toStringSymbols muslSysSymChars00 := by rfl_kernel
theorem muslSys00_symbols_fresh : allFreshCharSymbols muslSysSymChars00 = true := by rfl_kernel

gen_placed_fetches muslSysPC00 muslSysLib00 muslSysTree00 muslSys00_code_eq muslSys00_tree_size
  via_placement muslSysPl00 muslSysPlaceable00 [0x0 → 0x8]
gen_placed_fnOffs muslSysPC00 muslSysLib00 muslSysSymChars00 muslSys00_symbols_eq muslSys00_symbols_fresh

def muslSysProg01 : Program := { code := muslBlk01_syscall_ret.code, symbols := muslBlk01_syscall_ret.symbols }
def muslSysTree01 : WordTree := word_tree_of% muslSysProg01
theorem muslSys01_code_eq : muslSysLib01.text.code = muslSysTree01.toBytes := by rfl_kernel
theorem muslSys01_tree_size : muslSysTree01.checkSize? = some 15 := by rfl_kernel
def muslSysSymChars01 : List (List Char × Nat) := sym_chars_of% muslSysProg01
theorem muslSys01_symbols_eq : muslSysLib01.text.symbols = toStringSymbols muslSysSymChars01 := by rfl_kernel
theorem muslSys01_symbols_fresh : allFreshCharSymbols muslSysSymChars01 = true := by rfl_kernel

gen_placed_fetches muslSysPC01 muslSysLib01 muslSysTree01 muslSys01_code_eq muslSys01_tree_size
  via_placement muslSysPl01 muslSysPlaceable01 [0x0 → 0x38]
gen_placed_fnOffs muslSysPC01 muslSysLib01 muslSysSymChars01 muslSys01_symbols_eq muslSys01_symbols_fresh

def muslSysProg02 : Program := { code := muslBlk02_sccp.code, symbols := muslBlk02_sccp.symbols }
def muslSysTree02 : WordTree := word_tree_of% muslSysProg02
theorem muslSys02_code_eq : muslSysLib02.text.code = muslSysTree02.toBytes := by rfl_kernel
theorem muslSys02_tree_size : muslSysTree02.checkSize? = some 9 := by rfl_kernel
def muslSysSymChars02 : List (List Char × Nat) := sym_chars_of% muslSysProg02
theorem muslSys02_symbols_eq : muslSysLib02.text.symbols = toStringSymbols muslSysSymChars02 := by rfl_kernel
theorem muslSys02_symbols_fresh : allFreshCharSymbols muslSysSymChars02 = true := by rfl_kernel

gen_placed_fetches muslSysPC02 muslSysLib02 muslSysTree02 muslSys02_code_eq muslSys02_tree_size
  via_placement muslSysPl02 muslSysPlaceable02 [0x0 → 0x20]
gen_placed_fnOffs muslSysPC02 muslSysLib02 muslSysSymChars02 muslSys02_symbols_eq muslSys02_symbols_fresh

def muslSysProg03 : Program := { code := muslBlk03_syscall_cp.code, symbols := muslBlk03_syscall_cp.symbols }
def muslSysTree03 : WordTree := word_tree_of% muslSysProg03
theorem muslSys03_code_eq : muslSysLib03.text.code = muslSysTree03.toBytes := by rfl_kernel
theorem muslSys03_tree_size : muslSysTree03.checkSize? = some 1 := by rfl_kernel
def muslSysSymChars03 : List (List Char × Nat) := sym_chars_of% muslSysProg03
theorem muslSys03_symbols_eq : muslSysLib03.text.symbols = toStringSymbols muslSysSymChars03 := by rfl_kernel
theorem muslSys03_symbols_fresh : allFreshCharSymbols muslSysSymChars03 = true := by rfl_kernel

gen_placed_fetches muslSysPC03 muslSysLib03 muslSysTree03 muslSys03_code_eq muslSys03_tree_size
  via_placement muslSysPl03 muslSysPlaceable03 [0x0 → 0x0]
gen_placed_fnOffs muslSysPC03 muslSysLib03 muslSysSymChars03 muslSys03_symbols_eq muslSys03_symbols_fresh

def muslSysProg04 : Program := { code := muslBlk04_aio_close.code, symbols := muslBlk04_aio_close.symbols }
def muslSysTree04 : WordTree := word_tree_of% muslSysProg04
theorem muslSys04_code_eq : muslSysLib04.text.code = muslSysTree04.toBytes := by rfl_kernel
theorem muslSys04_tree_size : muslSysTree04.checkSize? = some 1 := by rfl_kernel
def muslSysSymChars04 : List (List Char × Nat) := sym_chars_of% muslSysProg04
theorem muslSys04_symbols_eq : muslSysLib04.text.symbols = toStringSymbols muslSysSymChars04 := by rfl_kernel
theorem muslSys04_symbols_fresh : allFreshCharSymbols muslSysSymChars04 = true := by rfl_kernel

gen_placed_fetches muslSysPC04 muslSysLib04 muslSysTree04 muslSys04_code_eq muslSys04_tree_size
  via_placement muslSysPl04 muslSysPlaceable04 [0x0 → 0x0]
gen_placed_fnOffs muslSysPC04 muslSysLib04 muslSysSymChars04 muslSys04_symbols_eq muslSys04_symbols_fresh

def muslSysProg05 : Program := { code := muslBlk05_close.code, symbols := muslBlk05_close.symbols }
def muslSysTree05 : WordTree := word_tree_of% muslSysProg05
theorem muslSys05_code_eq : muslSysLib05.text.code = muslSysTree05.toBytes := by rfl_kernel
theorem muslSys05_tree_size : muslSysTree05.checkSize? = some 17 := by rfl_kernel
def muslSysSymChars05 : List (List Char × Nat) := sym_chars_of% muslSysProg05
theorem muslSys05_symbols_eq : muslSysLib05.text.symbols = toStringSymbols muslSysSymChars05 := by rfl_kernel
theorem muslSys05_symbols_fresh : allFreshCharSymbols muslSysSymChars05 = true := by rfl_kernel

gen_placed_fetches muslSysPC05 muslSysLib05 muslSysTree05 muslSys05_code_eq muslSys05_tree_size
  via_placement muslSysPl05 muslSysPlaceable05 [0x0 → 0x40]
gen_placed_fnOffs muslSysPC05 muslSysLib05 muslSysSymChars05 muslSys05_symbols_eq muslSys05_symbols_fresh

def muslSysProg06 : Program := { code := muslBlk06_read.code, symbols := muslBlk06_read.symbols }
def muslSysTree06 : WordTree := word_tree_of% muslSysProg06
theorem muslSys06_code_eq : muslSysLib06.text.code = muslSysTree06.toBytes := by rfl_kernel
theorem muslSys06_tree_size : muslSysTree06.checkSize? = some 13 := by rfl_kernel
def muslSysSymChars06 : List (List Char × Nat) := sym_chars_of% muslSysProg06
theorem muslSys06_symbols_eq : muslSysLib06.text.symbols = toStringSymbols muslSysSymChars06 := by rfl_kernel
theorem muslSys06_symbols_fresh : allFreshCharSymbols muslSysSymChars06 = true := by rfl_kernel

gen_placed_fetches muslSysPC06 muslSysLib06 muslSysTree06 muslSys06_code_eq muslSys06_tree_size
  via_placement muslSysPl06 muslSysPlaceable06 [0x0 → 0x30]
gen_placed_fnOffs muslSysPC06 muslSysLib06 muslSysSymChars06 muslSys06_symbols_eq muslSys06_symbols_fresh

def muslSysProg07 : Program := { code := muslBlk07_write.code, symbols := muslBlk07_write.symbols }
def muslSysTree07 : WordTree := word_tree_of% muslSysProg07
theorem muslSys07_code_eq : muslSysLib07.text.code = muslSysTree07.toBytes := by rfl_kernel
theorem muslSys07_tree_size : muslSysTree07.checkSize? = some 13 := by rfl_kernel
def muslSysSymChars07 : List (List Char × Nat) := sym_chars_of% muslSysProg07
theorem muslSys07_symbols_eq : muslSysLib07.text.symbols = toStringSymbols muslSysSymChars07 := by rfl_kernel
theorem muslSys07_symbols_fresh : allFreshCharSymbols muslSysSymChars07 = true := by rfl_kernel

gen_placed_fetches muslSysPC07 muslSysLib07 muslSysTree07 muslSys07_code_eq muslSys07_tree_size
  via_placement muslSysPl07 muslSysPlaceable07 [0x0 → 0x30]
gen_placed_fnOffs muslSysPC07 muslSysLib07 muslSysSymChars07 muslSys07_symbols_eq muslSys07_symbols_fresh

def muslSysProg08 : Program := { code := muslBlk08_open.code, symbols := muslBlk08_open.symbols }
def muslSysTree08 : WordTree := word_tree_of% muslSysProg08
theorem muslSys08_code_eq : muslSysLib08.text.code = muslSysTree08.toBytes := by rfl_kernel
theorem muslSys08_tree_size : muslSysTree08.checkSize? = some 39 := by rfl_kernel
def muslSysSymChars08 : List (List Char × Nat) := sym_chars_of% muslSysProg08
theorem muslSys08_symbols_eq : muslSysLib08.text.symbols = toStringSymbols muslSysSymChars08 := by rfl_kernel
theorem muslSys08_symbols_fresh : allFreshCharSymbols muslSysSymChars08 = true := by rfl_kernel

gen_placed_fetches muslSysPC08 muslSysLib08 muslSysTree08 muslSys08_code_eq muslSys08_tree_size
  via_placement muslSysPl08 muslSysPlaceable08 [0x0 → 0x98]
gen_placed_fnOffs muslSysPC08 muslSysLib08 muslSysSymChars08 muslSys08_symbols_eq muslSys08_symbols_fresh

def muslSysProg09 : Program := { code := muslBlk09_fstat.code, symbols := muslBlk09_fstat.symbols }
def muslSysTree09 : WordTree := word_tree_of% muslSysProg09
theorem muslSys09_code_eq : muslSysLib09.text.code = muslSysTree09.toBytes := by rfl_kernel
theorem muslSys09_tree_size : muslSysTree09.checkSize? = some 12 := by rfl_kernel
def muslSysSymChars09 : List (List Char × Nat) := sym_chars_of% muslSysProg09
theorem muslSys09_symbols_eq : muslSysLib09.text.symbols = toStringSymbols muslSysSymChars09 := by rfl_kernel
theorem muslSys09_symbols_fresh : allFreshCharSymbols muslSysSymChars09 = true := by rfl_kernel

gen_placed_fetches muslSysPC09 muslSysLib09 muslSysTree09 muslSys09_code_eq muslSys09_tree_size
  via_placement muslSysPl09 muslSysPlaceable09 [0x0 → 0x2c]
gen_placed_fnOffs muslSysPC09 muslSysLib09 muslSysSymChars09 muslSys09_symbols_eq muslSys09_symbols_fresh

def muslSysProg10 : Program := { code := muslBlk10_fstatat.code, symbols := muslBlk10_fstatat.symbols }
def muslSysTree10 : WordTree := word_tree_of% muslSysProg10
theorem muslSys10_code_eq : muslSysLib10.text.code = muslSysTree10.toBytes := by rfl_kernel
theorem muslSys10_tree_size : muslSysTree10.checkSize? = some 87 := by rfl_kernel
def muslSysSymChars10 : List (List Char × Nat) := sym_chars_of% muslSysProg10
theorem muslSys10_symbols_eq : muslSysLib10.text.symbols = toStringSymbols muslSysSymChars10 := by rfl_kernel
theorem muslSys10_symbols_fresh : allFreshCharSymbols muslSysSymChars10 = true := by rfl_kernel

gen_placed_fetches muslSysPC10 muslSysLib10 muslSysTree10 muslSys10_code_eq muslSys10_tree_size
  via_placement muslSysPl10 muslSysPlaceable10 [0x0 → 0x158]
gen_placed_fnOffs muslSysPC10 muslSysLib10 muslSysSymChars10 muslSys10_symbols_eq muslSys10_symbols_fresh

end VerifiedLibraries.Musl
