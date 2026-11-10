/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.ExecSegSym
public import VerifiedLibraries.Musl.Proofs.ExecHelpersSym
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic Rust `std` Helper Blocks

Relocatable `Obj.CodeBlock` definitions, placement typeclass, fetch lemmas, and no-`SVC #0`
certificates (`rustStdPlacedLib`) for `is_interrupted`, `File::open_c`,
`run_with_cstr_allocating::<File>`, `small_probe_read::<File>`, and `Stderr::write_all`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

/-! ## Mangled Rust `std` and `alloc` Symbol Names -/

abbrev isInterruptedSym : String :=
  "_RNvNtNtNtNtCs6NnNJOrmTEL_3std3sys2io5error4unix14is_interrupted"

abbrev fileOpenCSym : String :=
  "_RNvMsi_NtNtNtCs6NnNJOrmTEL_3std3sys2fs4unixNtB5_4File6open_c"

abbrev runWithCstrSym : String :=
  "_RINvNtNtNtCs6NnNJOrmTEL_3std3sys7helpers14small_c_string24run_with_cstr_allocatingNtNtNtB6_2fs4unix4FileEB8_"

abbrev smallProbeReadSym : String :=
  "_RINvNvNtCs6NnNJOrmTEL_3std2io19default_read_to_end16small_probe_readNtNtB6_2fs4FileEB6_"

abbrev stderrWriteAllSym : String :=
  "_RNvXso_NtNtCs6NnNJOrmTEL_3std2io5stdioNtB5_6StderrNtB7_5Write9write_all"

abbrev growOneOsStringSym : String :=
  "_RNvMs4_NtCseaFDvLkwVtE_5alloc7raw_vecINtB5_6RawVecNtNtNtCs6NnNJOrmTEL_3std3ffi6os_str8OsStringE8grow_oneBS_"

abbrev doReserveAndHandleSym : String :=
  "_RINvNvMs2_NtCseaFDvLkwVtE_5alloc7raw_vecINtB8_11RawVecInnerpE7reserve21do_reserve_and_handleNtNtBa_5alloc6GlobalECs6NnNJOrmTEL_3std"

abbrev finishGrowSym : String :=
  "_RNvMs5_NtCseaFDvLkwVtE_5alloc7raw_vecNtB5_11RawVecInner11finish_growCs6NnNJOrmTEL_3std"

abbrev errorNewSym : String :=
  "_RINvMNtNtCseaFDvLkwVtE_5alloc2io5errorNtNtNtCsxVxvXE3aUf_4core2io5error5Error3newReECs6NnNJOrmTEL_3std"

abbrev mutexLockContendedSym : String :=
  "_RNvMNtNtNtNtCs6NnNJOrmTEL_3std3sys4sync5mutex5futexNtB2_5Mutex14lock_contended"

/-! ## Instruction Words and Relocatable `CodeBlock` Definitions -/

def rustCode00_is_interrupted : List (BitVec 8) := wordsLE [
  0x7100101f#32, 0x1a9f17e0#32, 0xd65f03c0#32]

def rustCode01_file_open_c : List (BitVec 8) := wordsLE [
  0xa9bb7bfd#32, 0xf9000bf9#32, 0xa9025ff8#32, 0xa90357f6#32, 0xa9044ff4#32, 0x910003fd#32, 0x3940204a#32, 0x39402449#32,
  0xaa0103f4#32, 0x39402848#32, 0xaa0003f3#32, 0x360000aa#32, 0x36000149#32, 0x37000148#32, 0x52800048#32, 0x14000004#32,
  0x36000129#32, 0x37000128#32, 0x52800028#32, 0x39403449#32, 0x39402c4a#32, 0x14000012#32, 0x36000828#32, 0x52808048#32,
  0x14000003#32, 0x360008e8#32, 0x52808028#32, 0x39402c4a#32, 0x39403449#32, 0x7100055f#32, 0x54000121#32, 0x37000109#32,
  0x90000000#32, 0x91000000#32, 0x528007a1#32, 0x94000000#32, 0x52800028#32, 0xf9000660#32, 0x1400004a#32, 0x3940304b#32,
  0x360000eb#32, 0x7200015f#32, 0x5280080a#32, 0x5280480b#32, 0x1a8a116a#32, 0x370000c9#32, 0x14000006#32, 0x7200015f#32,
  0x5280400a#32, 0x1a9f114a#32, 0x36000049#32, 0x5280180a#32, 0x29405449#32, 0x529fff8b#32, 0x2a0a0108#32, 0x90000018#32,
  0x72bffaeb#32, 0x90000019#32, 0x91000339#32, 0x0a0b0129#32, 0x2a090117#32, 0x320d02e1#32, 0xaa1403e0#32, 0x2a1503e2#32,
  0x94000000#32, 0x3100041f#32, 0x540001c1#32, 0x94000000#32, 0xb9800016#32, 0xf9400308#32, 0xeb19011f#32, 0x540000e1#32,
  0xf9400308#32, 0x2a1603e0#32, 0xf9400908#32, 0xd63f0100#32, 0x3707fe20#32, 0x14000006#32, 0xf9000319#32, 0x17fffff9#32,
  0x2a1f03e8#32, 0xb9000660#32, 0x1400001e#32, 0x52800048#32, 0xaa168108#32, 0xf9000668#32, 0x14000019#32, 0x39402c48#32,
  0x3707f908#32, 0x39403048#32, 0x3707f8c8#32, 0x39403448#32, 0x3707f888#32, 0x2a1f03e8#32, 0x2a1f03ea#32, 0x17ffffd5#32,
  0x39403048#32, 0x37000128#32, 0x39403448#32, 0x370000e8#32, 0x39402c48#32, 0x370000a8#32, 0x90000000#32, 0x91000000#32,
  0x52800741#32, 0x14000004#32, 0x90000000#32, 0x91000000#32, 0x528007a1#32, 0x94000000#32, 0xf9000660#32, 0x52800028#32,
  0xb9000268#32, 0xa9444ff4#32, 0xf9400bf9#32, 0xa94357f6#32, 0xa9425ff8#32, 0xa8c57bfd#32, 0xd65f03c0#32]

def rustCode02_run_with_cstr : List (BitVec 8) := wordsLE [
  0xa9bc7bfd#32, 0xf9000bf7#32, 0xa90257f6#32, 0xa9034ff4#32, 0x910003fd#32, 0xb1000448#32, 0x540007c4#32, 0xaa0003f3#32,
  0xaa0803e0#32, 0xaa0303f6#32, 0xaa0203f5#32, 0xaa0103f7#32, 0x94000000#32, 0xb40006e0#32, 0xaa1703e1#32, 0xaa1503e2#32,
  0xaa0003f4#32, 0x94000000#32, 0x91001ee8#32, 0x927df109#32, 0xeb170128#32, 0x540000e0#32, 0xcb0902e9#32, 0xaa1703ea#32,
  0x3840154b#32, 0x3400040b#32, 0xb1000529#32, 0x54ffffa3#32, 0xb200c3e9#32, 0xd10042aa#32, 0xb201c3eb#32, 0xf2802009#32,
  0x8b0802ec#32, 0xa940318d#32, 0xcb0d012e#32, 0xcb0c012f#32, 0xaa0d01cd#32, 0xaa0c01ec#32, 0x8a0c01ac#32, 0xea2c017f#32,
  0x54000081#32, 0x91004108#32, 0xeb0a011f#32, 0x54fffea9#32, 0xeb0802a9#32, 0x540000c0#32, 0x8b0802e8#32, 0x3840150a#32,
  0x3400012a#32, 0xf1000529#32, 0x54ffffa1#32, 0xf94002c2#32, 0xaa1303e0#32, 0xaa1403e1#32, 0x38356a9f#32, 0x94000000#32,
  0x14000006#32, 0x90000008#32, 0x91000108#32, 0xf9000668#32, 0x52800028#32, 0xb9000268#32, 0xaa1403e0#32, 0xa9434ff4#32,
  0xf9400bf7#32, 0xa94257f6#32, 0xa8c47bfd#32, 0x14000000#32, 0xd4200020#32]

def rustCode03_small_probe_read : List (BitVec 8) := wordsLE [
  0xd10183ff#32, 0xa9027bfd#32, 0xf9001bf7#32, 0xa90457f6#32, 0xa9054ff4#32, 0x910083fd#32, 0x6f00e400#32, 0xaa0103f3#32,
  0x2a0003f4#32, 0x90000016#32, 0x90000017#32, 0x910002f7#32, 0xad0003e0#32, 0x910003e1#32, 0x2a1403e0#32, 0x52800402#32,
  0x94000000#32, 0xb100041f#32, 0x540001c1#32, 0x94000000#32, 0xb9800015#32, 0xf94002c8#32, 0xeb17011f#32, 0x540000e1#32,
  0xf94002c8#32, 0x2a1503e0#32, 0xf9400908#32, 0xd63f0100#32, 0x3707fe20#32, 0x14000016#32, 0xf90002d7#32, 0x17fffff9#32,
  0xf100841f#32, 0x54000462#32, 0xf9400a75#32, 0xf9400268#32, 0xaa0003f4#32, 0xcb150108#32, 0xeb08001f#32, 0x540002e8#32,
  0xb40000e0#32, 0xf9400668#32, 0x910003e1#32, 0xaa1403e2#32, 0x8b150100#32, 0x94000000#32, 0xaa1403e0#32, 0xaa1f03e8#32,
  0x8b0002a9#32, 0xf9000a69#32, 0x14000004#32, 0x52800048#32, 0xaa158114#32, 0x52800028#32, 0xaa0803e0#32, 0xaa1403e1#32,
  0xa9454ff4#32, 0xf9401bf7#32, 0xa94457f6#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32, 0xaa1303e0#32, 0xaa1503e1#32,
  0xaa1403e2#32, 0x94000000#32, 0xf9400a75#32, 0x17ffffe6#32, 0xd4200020#32]

def rustCode04_stderr_write_all : List (BitVec 8) := wordsLE [
  0xa9bb7bfd#32, 0xf9000bf9#32, 0xa9025ff8#32, 0xa90357f6#32, 0xa9044ff4#32, 0x910003fd#32, 0xd53bd048#32, 0xaa0203f4#32,
  0xaa0103f5#32, 0x91400108#32, 0xaa0003f3#32, 0x91004119#32, 0xf9400338#32, 0xb5000218#32, 0x90000008#32, 0x90000016#32,
  0x910002d6#32, 0xf9400117#32, 0xb10006ff#32, 0x54000ba0#32, 0x910006e1#32, 0xaa1703e0#32, 0xaa1603e2#32, 0x910006f8#32,
  0x94000000#32, 0xeb17001f#32, 0xaa0003f7#32, 0x54fffee1#32, 0xf9000338#32, 0xf9400268#32, 0xeb08031f#32, 0x540000e1#32,
  0xb9400e68#32, 0x3100051f#32, 0x540009c0#32, 0x11000508#32, 0xb9000e68#32, 0x1400000a#32, 0x91002262#32, 0x2a1f03e0#32,
  0x52800021#32, 0x52800036#32, 0x94000000#32, 0x7100001f#32, 0x540008a1#32, 0xf9000278#32, 0xb9000e76#32, 0xf9400a68#32,
  0xb5000808#32, 0x92800008#32, 0x90000017#32, 0x90000018#32, 0x91000318#32, 0xf9000a68#32, 0x14000003#32, 0x8b0002b5#32,
  0xb4000494#32, 0x52800040#32, 0xaa1503e1#32, 0xaa1403e2#32, 0x94000000#32, 0xb100041f#32, 0x540000a0#32, 0xb4000220#32,
  0xeb000294#32, 0x54fffec2#32, 0x1400002e#32, 0x94000000#32, 0xb9800016#32, 0xf94002e8#32, 0xeb18011f#32, 0x540000e1#32,
  0xf94002e8#32, 0x2a1603e0#32, 0xf9400908#32, 0xd63f0100#32, 0x3707fd80#32, 0x14000006#32, 0xf90002f8#32, 0x17fffff9#32,
  0x90000014#32, 0x91000294#32, 0x14000003#32, 0x52800048#32, 0xaa168114#32, 0x92400688#32, 0xf100091f#32, 0x540000a3#32,
  0x54000081#32, 0xd360fe88#32, 0xf100251f#32, 0x9a9403f4#32, 0xf9400a68#32, 0xb9400e69#32, 0x91000508#32, 0x71000529#32,
  0xf9000a68#32, 0xb9000e69#32, 0x540000e1#32, 0x91002261#32, 0x2a1f03e0#32, 0xf900027f#32, 0x94000000#32, 0x7100081f#32,
  0x54000180#32, 0xaa1403e0#32, 0xa9444ff4#32, 0xf9400bf9#32, 0xa94357f6#32, 0xa9425ff8#32, 0xa8c57bfd#32, 0xd65f03c0#32,
  0xd4200020#32, 0x91002260#32, 0x94000000#32, 0x17ffffba#32, 0x91002261#32, 0x52800c40#32, 0x52801022#32, 0x52800023#32,
  0x94000000#32, 0x17fffff0#32]

def rustBlk00_is_interrupted : CodeBlock where
  code := rustCode00_is_interrupted
  symbols := [(isInterruptedSym, 0)]
  relocs := []
  externs := []

def rustBlk01_file_open_c : CodeBlock where
  code := rustCode01_file_open_c
  symbols := [(fileOpenCSym, 0)]
  relocs := [
    { off := 128, kind := .adrpHi21, sym := "rustErrInvalidOpen1" },
    { off := 132, kind := .addLo12, sym := "rustErrInvalidOpen1" },
    { off := 140, kind := .call26, sym := errorNewSym },
    { off := 220, kind := .adrpHi21, sym := "rustOsFunctions" },
    { off := 228, kind := .adrpHi21, sym := "rustErrorFunctions" },
    { off := 232, kind := .addLo12, sym := "rustErrorFunctions" },
    { off := 256, kind := .call26, sym := "open" },
    { off := 268, kind := .call26, sym := "___errno_location" },
    { off := 276, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 288, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 312, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 408, kind := .adrpHi21, sym := "rustErrInvalidOpen0" },
    { off := 412, kind := .addLo12, sym := "rustErrInvalidOpen0" },
    { off := 424, kind := .adrpHi21, sym := "rustErrInvalidOpen1" },
    { off := 428, kind := .addLo12, sym := "rustErrInvalidOpen1" },
    { off := 436, kind := .call26, sym := errorNewSym }]
  externs := [
    errorNewSym, "open", "___errno_location",
    "rustErrInvalidOpen1", "rustOsFunctions", "rustErrorFunctions", "rustErrInvalidOpen0"]

def rustBlk02_run_with_cstr : CodeBlock where
  code := rustCode02_run_with_cstr
  symbols := [(runWithCstrSym, 0)]
  relocs := [
    { off := 48, kind := .call26, sym := "malloc" },
    { off := 68, kind := .call26, sym := "memcpy" },
    { off := 220, kind := .call26, sym := fileOpenCSym },
    { off := 228, kind := .adrpHi21, sym := "rustSimpleMsgInvalidInput" },
    { off := 232, kind := .addLo12, sym := "rustSimpleMsgInvalidInput" },
    { off := 268, kind := .jump26, sym := "free" }]
  externs := ["malloc", "memcpy", fileOpenCSym, "free", "rustSimpleMsgInvalidInput"]

def rustBlk03_small_probe_read : CodeBlock where
  code := rustCode03_small_probe_read
  symbols := [(smallProbeReadSym, 0)]
  relocs := [
    { off := 36, kind := .adrpHi21, sym := "rustOsFunctions" },
    { off := 40, kind := .adrpHi21, sym := "rustErrorFunctions" },
    { off := 44, kind := .addLo12, sym := "rustErrorFunctions" },
    { off := 64, kind := .call26, sym := "read" },
    { off := 76, kind := .call26, sym := "___errno_location" },
    { off := 84, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 96, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 120, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 180, kind := .call26, sym := "memcpy" },
    { off := 260, kind := .call26, sym := doReserveAndHandleSym }]
  externs := [
    "read", "___errno_location", "memcpy",
    doReserveAndHandleSym, "rustOsFunctions", "rustErrorFunctions"]

def rustBlk04_stderr_write_all : CodeBlock where
  code := rustCode04_stderr_write_all
  symbols := [(stderrWriteAllSym, 0)]
  relocs := [
    { off := 56, kind := .adrpHi21, sym := "rustThreadIdCounter" },
    { off := 60, kind := .adrpHi21, sym := "rustThreadIdCounter" },
    { off := 64, kind := .addLo12, sym := "rustThreadIdCounter" },
    { off := 68, kind := .ldst64Lo12, sym := "rustThreadIdCounter" },
    { off := 96, kind := .call26, sym := "__aarch64_cas8_relax" },
    { off := 168, kind := .call26, sym := "__aarch64_cas4_acq" },
    { off := 200, kind := .adrpHi21, sym := "rustOsFunctions" },
    { off := 204, kind := .adrpHi21, sym := "rustErrorFunctions" },
    { off := 208, kind := .addLo12, sym := "rustErrorFunctions" },
    { off := 240, kind := .call26, sym := "write" },
    { off := 268, kind := .call26, sym := "___errno_location" },
    { off := 276, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 288, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 312, kind := .ldst64Lo12, sym := "rustOsFunctions" },
    { off := 320, kind := .adrpHi21, sym := "rustWriteAllEof" },
    { off := 324, kind := .addLo12, sym := "rustWriteAllEof" },
    { off := 408, kind := .call26, sym := "__aarch64_swp4_rel" },
    { off := 456, kind := .call26, sym := mutexLockContendedSym },
    { off := 480, kind := .call26, sym := "syscall" }]
  externs := [
    "__aarch64_cas8_relax", "__aarch64_cas4_acq", "write", "___errno_location",
    "__aarch64_swp4_rel", mutexLockContendedSym, "syscall",
    "rustThreadIdCounter", "rustOsFunctions", "rustErrorFunctions", "rustWriteAllEof"]

def rustStdPlacedLib : MultiPlacedLib where
  name := "rust_std_io_fs"
  blocks := [
    rustBlk00_is_interrupted,
    rustBlk01_file_open_c,
    rustBlk02_run_with_cstr,
    rustBlk03_small_probe_read,
    rustBlk04_stderr_write_all]
  data := []
  exports := [
    isInterruptedSym,
    fileOpenCSym,
    runWithCstrSym,
    smallProbeReadSym,
    stderrWriteAllSym]

/-! ## Placement Typeclass and Per-Block Projections -/

class RustStdPlacement where
  mpl : MultiPlacement
  placeable : rustStdPlacedLib.Placeable mpl

abbrev rustStdMpl [RustStdPlacement] : MultiPlacement := RustStdPlacement.mpl

def rustStdLib00 : PlacedLib := rustStdPlacedLib.blockLib 0
def rustStdPl00 [RustStdPlacement] : Placement := rustStdPlacedLib.blockPlacement RustStdPlacement.mpl 0
theorem rustStdPlaceable00 [RustStdPlacement] : rustStdLib00.Placeable rustStdPl00 :=
  rustStdPlacedLib.placeable_blockLib (by decide) RustStdPlacement.placeable
def rustStdPC00 [RustStdPlacement] : Program := rustStdLib00.program rustStdPl00

def rustStdLib01 : PlacedLib := rustStdPlacedLib.blockLib 1
def rustStdPl01 [RustStdPlacement] : Placement := rustStdPlacedLib.blockPlacement RustStdPlacement.mpl 1
theorem rustStdPlaceable01 [RustStdPlacement] : rustStdLib01.Placeable rustStdPl01 :=
  rustStdPlacedLib.placeable_blockLib (by decide) RustStdPlacement.placeable
def rustStdPC01 [RustStdPlacement] : Program := rustStdLib01.program rustStdPl01

def rustStdLib02 : PlacedLib := rustStdPlacedLib.blockLib 2
def rustStdPl02 [RustStdPlacement] : Placement := rustStdPlacedLib.blockPlacement RustStdPlacement.mpl 2
theorem rustStdPlaceable02 [RustStdPlacement] : rustStdLib02.Placeable rustStdPl02 :=
  rustStdPlacedLib.placeable_blockLib (by decide) RustStdPlacement.placeable
def rustStdPC02 [RustStdPlacement] : Program := rustStdLib02.program rustStdPl02

def rustStdLib03 : PlacedLib := rustStdPlacedLib.blockLib 3
def rustStdPl03 [RustStdPlacement] : Placement := rustStdPlacedLib.blockPlacement RustStdPlacement.mpl 3
theorem rustStdPlaceable03 [RustStdPlacement] : rustStdLib03.Placeable rustStdPl03 :=
  rustStdPlacedLib.placeable_blockLib (by decide) RustStdPlacement.placeable
def rustStdPC03 [RustStdPlacement] : Program := rustStdLib03.program rustStdPl03

def rustStdLib04 : PlacedLib := rustStdPlacedLib.blockLib 4
def rustStdPl04 [RustStdPlacement] : Placement := rustStdPlacedLib.blockPlacement RustStdPlacement.mpl 4
theorem rustStdPlaceable04 [RustStdPlacement] : rustStdLib04.Placeable rustStdPl04 :=
  rustStdPlacedLib.placeable_blockLib (by decide) RustStdPlacement.placeable
def rustStdPC04 [RustStdPlacement] : Program := rustStdLib04.program rustStdPl04

/-! ## Placed Fetch and `fnOff` Generation -/

def rustStdProg00 : Program := { code := rustBlk00_is_interrupted.code, symbols := rustBlk00_is_interrupted.symbols }
def rustStdTree00 : WordTree := word_tree_of% rustStdProg00
theorem rustStd00_code_eq : rustStdLib00.text.code = rustStdTree00.toBytes := by rfl_kernel
theorem rustStd00_tree_size : rustStdTree00.checkSize? = some 3 := by rfl_kernel
def rustStdSymChars00 : List (List Char × Nat) := sym_chars_of% rustStdProg00
theorem rustStd00_symbols_eq : rustStdLib00.text.symbols = toStringSymbols rustStdSymChars00 := by rfl_kernel
theorem rustStd00_symbols_fresh : allFreshCharSymbols rustStdSymChars00 = true := by rfl_kernel

gen_placed_fetches rustStdPC00 rustStdLib00 rustStdTree00 rustStd00_code_eq rustStd00_tree_size
  via_placement rustStdPl00 rustStdPlaceable00 [0x0 → 0x8]
gen_placed_fnOffs rustStdPC00 rustStdLib00 rustStdSymChars00 rustStd00_symbols_eq rustStd00_symbols_fresh

def rustStdProg01 : Program := { code := rustBlk01_file_open_c.code, symbols := rustBlk01_file_open_c.symbols }
def rustStdTree01 : WordTree := word_tree_of% rustStdProg01
theorem rustStd01_code_eq : rustStdLib01.text.code = rustStdTree01.toBytes := by rfl_kernel
theorem rustStd01_tree_size : rustStdTree01.checkSize? = some 119 := by rfl_kernel
def rustStdSymChars01 : List (List Char × Nat) := sym_chars_of% rustStdProg01
theorem rustStd01_symbols_eq : rustStdLib01.text.symbols = toStringSymbols rustStdSymChars01 := by rfl_kernel
theorem rustStd01_symbols_fresh : allFreshCharSymbols rustStdSymChars01 = true := by rfl_kernel

gen_placed_fetches rustStdPC01 rustStdLib01 rustStdTree01 rustStd01_code_eq rustStd01_tree_size
  via_placement rustStdPl01 rustStdPlaceable01 [0x0 → 0x1d8]
gen_placed_fnOffs rustStdPC01 rustStdLib01 rustStdSymChars01 rustStd01_symbols_eq rustStd01_symbols_fresh

theorem rustStdPC01_pairStep_0xdc [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) (hb : b = rustStdPl01.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 220) (hrun : s.status = .Running)
    (hnext : SepWP (rustStdPC01.rebase b X) tgt
      ((s.writeReg64 (.gpr 24#5) (pageOf (rustStdPl01.ρ "rustOsFunctions"))).setPC
        (b + BitVec.ofNat 64 224)) P post oom) :
    SepWP (rustStdPC01.rebase b X) tgt s P post oom :=
  PlacedLib.sepWP_rebase_adrpPlain (lib := rustStdLib01) (pl := rustStdPl01) (off := 220) (off4 := 224)
    (r := ⟨220, .adrpHi21, "rustOsFunctions", 0, false⟩) (rd := 24#5) (w := 0x90000018#32)
    rustStdPlaceable01 hb rfl rfl (by unfold CodeBlock.relaxableAt; rw [show rustStdLib01.text.relocAt? 220 = some ⟨220, .adrpHi21, "rustOsFunctions", 0, false⟩ from rfl, show rustStdLib01.text.relocAt? 224 = none from rfl])
    (wordAt_of_getQuad? rustStd01_code_eq rustStd01_tree_size (j := 55) rfl)
    (by decide) rfl (by decide) rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd01_code_eq rustStd01_tree_size rustStdPlaceable01 (by omega))
    hpc hrun hnext

@[simp, arm64_norm] theorem rustStdPC01_rebase_fetch_0x114 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC01.rebase b X).fetch (b + BitVec.ofNat 64 276) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 24#5) (lo12Of (rustStdPl01.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib01) (pl := rustStdPl01) (off := 276)
    (r := ⟨276, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf9400308#32)
    rustStdPlaceable01 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd01_code_eq rustStd01_tree_size rustStdPlaceable01 (by omega))
    (wordAt_of_getQuad? rustStd01_code_eq rustStd01_tree_size (j := 69) rfl)
    rfl (by decide) (by decide) rfl rfl

@[simp, arm64_norm] theorem rustStdPC01_rebase_fetch_0x120 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC01.rebase b X).fetch (b + BitVec.ofNat 64 288) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 24#5) (lo12Of (rustStdPl01.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib01) (pl := rustStdPl01) (off := 288)
    (r := ⟨288, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf9400308#32)
    rustStdPlaceable01 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd01_code_eq rustStd01_tree_size rustStdPlaceable01 (by omega))
    (wordAt_of_getQuad? rustStd01_code_eq rustStd01_tree_size (j := 72) rfl)
    rfl (by decide) (by decide) rfl rfl

@[simp, arm64_norm] theorem rustStdPC01_rebase_fetch_0x138 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC01.rebase b X).fetch (b + BitVec.ofNat 64 312) =
      some (.str .X64 (.gpr 25#5) (.Offset (.gpr 24#5) (lo12Of (rustStdPl01.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib01) (pl := rustStdPl01) (off := 312)
    (r := ⟨312, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf9000319#32)
    rustStdPlaceable01 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd01_code_eq rustStd01_tree_size rustStdPlaceable01 (by omega))
    (wordAt_of_getQuad? rustStd01_code_eq rustStd01_tree_size (j := 78) rfl)
    rfl (by decide) (by decide) rfl rfl

def rustStdProg02 : Program := { code := rustBlk02_run_with_cstr.code, symbols := rustBlk02_run_with_cstr.symbols }
def rustStdTree02 : WordTree := word_tree_of% rustStdProg02
theorem rustStd02_code_eq : rustStdLib02.text.code = rustStdTree02.toBytes := by rfl_kernel
theorem rustStd02_tree_size : rustStdTree02.checkSize? = some 69 := by rfl_kernel
def rustStdSymChars02 : List (List Char × Nat) := sym_chars_of% rustStdProg02
theorem rustStd02_symbols_eq : rustStdLib02.text.symbols = toStringSymbols rustStdSymChars02 := by rfl_kernel
theorem rustStd02_symbols_fresh : allFreshCharSymbols rustStdSymChars02 = true := by rfl_kernel

gen_placed_fetches rustStdPC02 rustStdLib02 rustStdTree02 rustStd02_code_eq rustStd02_tree_size
  via_placement rustStdPl02 rustStdPlaceable02 [0x0 → 0x110]
gen_placed_fnOffs rustStdPC02 rustStdLib02 rustStdSymChars02 rustStd02_symbols_eq rustStd02_symbols_fresh

def rustStdProg03 : Program := { code := rustBlk03_small_probe_read.code, symbols := rustBlk03_small_probe_read.symbols }
def rustStdTree03 : WordTree := word_tree_of% rustStdProg03
theorem rustStd03_code_eq : rustStdLib03.text.code = rustStdTree03.toBytes := by rfl_kernel
theorem rustStd03_tree_size : rustStdTree03.checkSize? = some 69 := by rfl_kernel
def rustStdSymChars03 : List (List Char × Nat) := sym_chars_of% rustStdProg03
theorem rustStd03_symbols_eq : rustStdLib03.text.symbols = toStringSymbols rustStdSymChars03 := by rfl_kernel
theorem rustStd03_symbols_fresh : allFreshCharSymbols rustStdSymChars03 = true := by rfl_kernel

gen_placed_fetches rustStdPC03 rustStdLib03 rustStdTree03 rustStd03_code_eq rustStd03_tree_size
  via_placement rustStdPl03 rustStdPlaceable03 [0x0 → 0x110]
gen_placed_fnOffs rustStdPC03 rustStdLib03 rustStdSymChars03 rustStd03_symbols_eq rustStd03_symbols_fresh

theorem rustStdPC03_pairStep_0x24 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) (hb : b = rustStdPl03.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 36) (hrun : s.status = .Running)
    (hnext : SepWP (rustStdPC03.rebase b X) tgt
      ((s.writeReg64 (.gpr 22#5) (pageOf (rustStdPl03.ρ "rustOsFunctions"))).setPC
        (b + BitVec.ofNat 64 40)) P post oom) :
    SepWP (rustStdPC03.rebase b X) tgt s P post oom :=
  PlacedLib.sepWP_rebase_adrpPlain (lib := rustStdLib03) (pl := rustStdPl03) (off := 36) (off4 := 40)
    (r := ⟨36, .adrpHi21, "rustOsFunctions", 0, false⟩) (rd := 22#5) (w := 0x90000016#32)
    rustStdPlaceable03 hb rfl rfl (CodeBlock.relaxableAt_false_of_next_kind (r := ⟨40, .adrpHi21, "rustErrorFunctions", 0, false⟩) rfl (by decide))
    (wordAt_of_getQuad? rustStd03_code_eq rustStd03_tree_size (j := 9) rfl)
    (by decide) rfl (by decide) rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd03_code_eq rustStd03_tree_size rustStdPlaceable03 (by omega))
    hpc hrun hnext

@[simp, arm64_norm] theorem rustStdPC03_rebase_fetch_0x54 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC03.rebase b X).fetch (b + BitVec.ofNat 64 84) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 22#5) (lo12Of (rustStdPl03.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib03) (pl := rustStdPl03) (off := 84)
    (r := ⟨84, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf94002c8#32)
    rustStdPlaceable03 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd03_code_eq rustStd03_tree_size rustStdPlaceable03 (by omega))
    (wordAt_of_getQuad? rustStd03_code_eq rustStd03_tree_size (j := 21) rfl)
    rfl (by decide) (by decide) rfl rfl

@[simp, arm64_norm] theorem rustStdPC03_rebase_fetch_0x60 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC03.rebase b X).fetch (b + BitVec.ofNat 64 96) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 22#5) (lo12Of (rustStdPl03.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib03) (pl := rustStdPl03) (off := 96)
    (r := ⟨96, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf94002c8#32)
    rustStdPlaceable03 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd03_code_eq rustStd03_tree_size rustStdPlaceable03 (by omega))
    (wordAt_of_getQuad? rustStd03_code_eq rustStd03_tree_size (j := 24) rfl)
    rfl (by decide) (by decide) rfl rfl

@[simp, arm64_norm] theorem rustStdPC03_rebase_fetch_0x78 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC03.rebase b X).fetch (b + BitVec.ofNat 64 120) =
      some (.str .X64 (.gpr 23#5) (.Offset (.gpr 22#5) (lo12Of (rustStdPl03.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib03) (pl := rustStdPl03) (off := 120)
    (r := ⟨120, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf90002d7#32)
    rustStdPlaceable03 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd03_code_eq rustStd03_tree_size rustStdPlaceable03 (by omega))
    (wordAt_of_getQuad? rustStd03_code_eq rustStd03_tree_size (j := 30) rfl)
    rfl (by decide) (by decide) rfl rfl

def rustStdProg04 : Program := { code := rustBlk04_stderr_write_all.code, symbols := rustBlk04_stderr_write_all.symbols }
def rustStdTree04 : WordTree := word_tree_of% rustStdProg04
theorem rustStd04_code_eq : rustStdLib04.text.code = rustStdTree04.toBytes := by rfl_kernel
theorem rustStd04_tree_size : rustStdTree04.checkSize? = some 122 := by rfl_kernel
def rustStdSymChars04 : List (List Char × Nat) := sym_chars_of% rustStdProg04
theorem rustStd04_symbols_eq : rustStdLib04.text.symbols = toStringSymbols rustStdSymChars04 := by rfl_kernel
theorem rustStd04_symbols_fresh : allFreshCharSymbols rustStdSymChars04 = true := by rfl_kernel

gen_placed_fetches rustStdPC04 rustStdLib04 rustStdTree04 rustStd04_code_eq rustStd04_tree_size
  via_placement rustStdPl04 rustStdPlaceable04 [0x0 → 0x1e4]
gen_placed_fnOffs rustStdPC04 rustStdLib04 rustStdSymChars04 rustStd04_symbols_eq rustStd04_symbols_fresh

theorem rustStdPC04_pairStep_0x38 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) (hb : b = rustStdPl04.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 56) (hrun : s.status = .Running)
    (hnext : SepWP (rustStdPC04.rebase b X) tgt
      ((s.writeReg64 (.gpr 8#5) (pageOf (rustStdPl04.ρ "rustThreadIdCounter"))).setPC
        (b + BitVec.ofNat 64 60)) P post oom) :
    SepWP (rustStdPC04.rebase b X) tgt s P post oom :=
  PlacedLib.sepWP_rebase_adrpPlain (lib := rustStdLib04) (pl := rustStdPl04) (off := 56) (off4 := 60)
    (r := ⟨56, .adrpHi21, "rustThreadIdCounter", 0, false⟩) (rd := 8#5) (w := 0x90000008#32)
    rustStdPlaceable04 hb rfl rfl (CodeBlock.relaxableAt_false_of_next_kind (r := ⟨60, .adrpHi21, "rustThreadIdCounter", 0, false⟩) rfl (by decide))
    (wordAt_of_getQuad? rustStd04_code_eq rustStd04_tree_size (j := 14) rfl)
    (by decide) rfl (by decide) rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd04_code_eq rustStd04_tree_size rustStdPlaceable04 (by omega))
    hpc hrun hnext

@[simp, arm64_norm] theorem rustStdPC04_rebase_fetch_0x44 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC04.rebase b X).fetch (b + BitVec.ofNat 64 68) =
      some (.ldr .W64 .X64 false (.gpr 23#5) (.Offset (.gpr 8#5) (lo12Of (rustStdPl04.ρ "rustThreadIdCounter")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib04) (pl := rustStdPl04) (off := 68)
    (r := ⟨68, .ldst64Lo12, "rustThreadIdCounter", 0, false⟩) (scale := 3) (w := 0xf9400117#32)
    rustStdPlaceable04 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd04_code_eq rustStd04_tree_size rustStdPlaceable04 (by omega))
    (wordAt_of_getQuad? rustStd04_code_eq rustStd04_tree_size (j := 17) rfl)
    rfl (by decide) (by decide) rfl rfl

theorem rustStdPC04_pairStep_0xc8 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) (hb : b = rustStdPl04.base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 200) (hrun : s.status = .Running)
    (hnext : SepWP (rustStdPC04.rebase b X) tgt
      ((s.writeReg64 (.gpr 23#5) (pageOf (rustStdPl04.ρ "rustOsFunctions"))).setPC
        (b + BitVec.ofNat 64 204)) P post oom) :
    SepWP (rustStdPC04.rebase b X) tgt s P post oom :=
  PlacedLib.sepWP_rebase_adrpPlain (lib := rustStdLib04) (pl := rustStdPl04) (off := 200) (off4 := 204)
    (r := ⟨200, .adrpHi21, "rustOsFunctions", 0, false⟩) (rd := 23#5) (w := 0x90000017#32)
    rustStdPlaceable04 hb rfl rfl (CodeBlock.relaxableAt_false_of_next_kind (r := ⟨204, .adrpHi21, "rustErrorFunctions", 0, false⟩) rfl (by decide))
    (wordAt_of_getQuad? rustStd04_code_eq rustStd04_tree_size (j := 50) rfl)
    (by decide) rfl (by decide) rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd04_code_eq rustStd04_tree_size rustStdPlaceable04 (by omega))
    hpc hrun hnext

@[simp, arm64_norm] theorem rustStdPC04_rebase_fetch_0x114 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC04.rebase b X).fetch (b + BitVec.ofNat 64 276) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 23#5) (lo12Of (rustStdPl04.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib04) (pl := rustStdPl04) (off := 276)
    (r := ⟨276, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf94002e8#32)
    rustStdPlaceable04 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd04_code_eq rustStd04_tree_size rustStdPlaceable04 (by omega))
    (wordAt_of_getQuad? rustStd04_code_eq rustStd04_tree_size (j := 69) rfl)
    rfl (by decide) (by decide) rfl rfl

@[simp, arm64_norm] theorem rustStdPC04_rebase_fetch_0x120 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC04.rebase b X).fetch (b + BitVec.ofNat 64 288) =
      some (.ldr .W64 .X64 false (.gpr 8#5) (.Offset (.gpr 23#5) (lo12Of (rustStdPl04.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib04) (pl := rustStdPl04) (off := 288)
    (r := ⟨288, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf94002e8#32)
    rustStdPlaceable04 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd04_code_eq rustStd04_tree_size rustStdPlaceable04 (by omega))
    (wordAt_of_getQuad? rustStd04_code_eq rustStd04_tree_size (j := 72) rfl)
    rfl (by decide) (by decide) rfl rfl

@[simp, arm64_norm] theorem rustStdPC04_rebase_fetch_0x138 [RustStdPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (rustStdPC04.rebase b X).fetch (b + BitVec.ofNat 64 312) =
      some (.str .X64 (.gpr 24#5) (.Offset (.gpr 23#5) (lo12Of (rustStdPl04.ρ "rustOsFunctions")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := rustStdLib04) (pl := rustStdPl04) (off := 312)
    (r := ⟨312, .ldst64Lo12, "rustOsFunctions", 0, false⟩) (scale := 3) (w := 0xf90002f8#32)
    rustStdPlaceable04 rfl rfl
    (hookAtOff?_rebase_of_placeable rustStd04_code_eq rustStd04_tree_size rustStdPlaceable04 (by omega))
    (wordAt_of_getQuad? rustStd04_code_eq rustStd04_tree_size (j := 78) rfl)
    rfl (by decide) (by decide) rfl rfl

/-! ## `checkBlockNoSvc0` Certificates -/

theorem rustBlockNoSvc0_00 : checkBlockNoSvc0 (rustStdPlacedLib.blockLib 0).text = true := by decide
theorem rustBlockNoSvc0_01 : checkBlockNoSvc0 (rustStdPlacedLib.blockLib 1).text = true := by decide
theorem rustBlockNoSvc0_02 : checkBlockNoSvc0 (rustStdPlacedLib.blockLib 2).text = true := by decide
theorem rustBlockNoSvc0_03 : checkBlockNoSvc0 (rustStdPlacedLib.blockLib 3).text = true := by decide
theorem rustBlockNoSvc0_04 : checkBlockNoSvc0 (rustStdPlacedLib.blockLib 4).text = true := by decide

end VerifiedLibraries.RustStd
