/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
public import Arm64.Testing.Harness.ElfLoaderDiff
public meta import ProofLib.Process
meta import ProofLib.TestFiles

/-!
# Static ELF64 Loader Differential and Layout Conformance Tests

Kernel-checked conformance (`elf_loader_diff_corpus_conformance`) and elaboration-time rejection
tests for `ElfImage.parse` over unusual static AArch64 `ET_EXEC` layouts (multiple `rw-` segments
with unmapped gaps, mid-page `PT_LOAD` starts with `padzero` `.bss` zeroing, `PT_PHDR`, and
`.symtab` symbol extraction) and unsupported ELF inputs (PIE, dynamic, relocatable, W+X,
executable stack, and non-writable `.bss`).
-/

@[expose] public section

namespace Testing.ElfLoaderDiff

open Arm64 Arm64.Process

-- Every declaration below embeds a corpus binary; without them the block reports SKIPPED.
requires_test_files [
  "../../../Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_multi_rw.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_midpage_bss.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_tls_relro.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_pie.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_dynamic.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_relocatable.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_wx_segment.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_exec_stack.elf",
  "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_ro_bss.elf"]

/-! ## Embedded Layout Corpus -/

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

noncomputable def tinyAsmBytes : List (BitVec 8) :=
  file_bytes% "../../../Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf"
    sha256 "c68e47f717dbc0fb35ab4ccc958867336e8a4cb249609555339dc15b9585de21"

def tinyAsmImg : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf"

theorem tinyAsm_parse : ElfImage.parse tinyAsmBytes = .ok tinyAsmImg := by
  exact ElfImage.parse_of_fastParse rfl

noncomputable def layoutMultiRwBytes : List (BitVec 8) :=
  file_bytes% "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_multi_rw.elf"
    sha256 "e73041760c9fcc1237621e8e45fe55fce5f1c753ca2f050eab29e224f263a58e"

def layoutMultiRwImg : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_multi_rw.elf"

theorem layoutMultiRw_parse : ElfImage.parse layoutMultiRwBytes = .ok layoutMultiRwImg := by
  exact ElfImage.parse_of_fastParse rfl

noncomputable def layoutMidpageBssBytes : List (BitVec 8) :=
  file_bytes% "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_midpage_bss.elf"
    sha256 "fc9112cb7340002600a2c399b56e5849685ff45ee9f842f2008c2beca2708af5"

def layoutMidpageBssImg : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_midpage_bss.elf"

theorem layoutMidpageBss_parse : ElfImage.parse layoutMidpageBssBytes = .ok layoutMidpageBssImg := by
  exact ElfImage.parse_of_fastParse rfl

noncomputable def layoutTlsRelroBytes : List (BitVec 8) :=
  file_bytes% "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_tls_relro.elf"
    sha256 "7e2aede538651be61005c30dcb37696fe4327e2297493b60f7cb9b8e09d63a0d"

def layoutTlsRelroImg : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/layout_tls_relro.elf"

theorem layoutTlsRelro_parse : ElfImage.parse layoutTlsRelroBytes = .ok layoutTlsRelroImg := by
  exact ElfImage.parse_of_fastParse rfl

/-- Unstripped `layout_midpage_bss.elf` has `_start` (`STT_FUNC`, `STB_GLOBAL`) extracted from
    `.symtab`/`.strtab` at `0x400200#64` by `ElfImage.parse`. -/
theorem layoutMidpageBss_symbols :
    layoutMidpageBssImg.symbols = [("_start", 0x400200#64)] := by
  rfl

-- `file_bytes%` fails closed at elaboration time when the SHA-256 digest does not match.
/-- sha256 mismatch -/
#guard_msgs (substring := true) in
example : List (BitVec 8) :=
  file_bytes% "../../../Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf"
    sha256 "0000000000000000000000000000000000000000000000000000000000000000"

/-! ## Fail-Closed Rejection Tests -/

/-- ElfImage.parse: expected static ET_EXEC (2), got e_type=3 -/
#guard_msgs (substring := true) in
example : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_pie.elf"

/-- is not supported -/
#guard_msgs (substring := true) in
example : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_dynamic.elf"

/-- ElfImage.parse: expected static ET_EXEC (2), got e_type=1 -/
#guard_msgs (substring := true) in
example : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_relocatable.elf"

/-- ElfImage.parse: W+X PT_LOAD segment is not supported -/
#guard_msgs (substring := true) in
example : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_wx_segment.elf"

/-- ElfImage.parse: executable stack (PT_GNU_STACK with PF_X) is not supported -/
#guard_msgs (substring := true) in
example : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_exec_stack.elf"

/-- ElfImage.parse: non-writable PT_LOAD segment has p_filesz < p_memsz -/
#guard_msgs (substring := true) in
example : ElfImage :=
  elf_image% "../../../Arm64/Testing/ElfLoaderDiff/bin/reject_ro_bss.elf"

/-! ## Kernel-Checked Conformance -/

def checkElfLoaderDiffCorpusConformance : Bool :=
  let wfOk :=
    tinyAsmImg.WellFormed &&
    layoutMultiRwImg.WellFormed &&
    layoutMidpageBssImg.WellFormed &&
    layoutTlsRelroImg.WellFormed
  -- `layout_multi_rw.elf`: 5 PT_LOAD segments (r--, r-x, and 3 rw- segments with unmapped gap [0x432000, 0x445000))
  let multiRwOk :=
    match layoutMultiRwImg.segments with
    | [r0, r1, r2, r3, r4] =>
      r0.start == 0x400000#64 && r0.perm == Perm.ro &&
      r1.start == 0x410000#64 && r1.perm == Perm.rx &&
      r2.start == 0x420000#64 && r2.perm == Perm.rw && r2.bytes.length == 0x1000 &&
      r3.start == 0x430000#64 && r3.perm == Perm.rw && r3.bytes.length == 0x2000 &&
      r4.start == 0x445000#64 && r4.perm == Perm.rw && r4.bytes.length == 0x2000 &&
      r4.bytes.all (· == 0#8)
    | _ => false
  -- `layout_midpage_bss.elf`: `rxSeg` (`p_filesz == p_memsz`) retains trailing file bytes in the
  -- shared 4 KiB page (`0x0d, 0xf0`), whereas `rwSeg` (`p_filesz < p_memsz`) zeroes `[0x4a0, 0x3000)`.
  let midpageBssOk :=
    match layoutMidpageBssImg.segments with
    | [rxSeg, rwSeg] =>
      rxSeg.start == 0x400000#64 && rxSeg.perm == Perm.rx && rxSeg.bytes.length == 0x1000 &&
      rxSeg.bytes[0x380]? == some 0x0d#8 && rxSeg.bytes[0x381]? == some 0xf0#8 &&
      rwSeg.start == 0x402000#64 && rwSeg.perm == Perm.rw && rwSeg.bytes.length == 0x3000 &&
      rwSeg.bytes[0x380]? == some 0x0d#8 && rwSeg.bytes[0x381]? == some 0xf0#8 &&
      rwSeg.bytes[0x4a0]? == some 0x00#8 && rwSeg.bytes[0x4a1]? == some 0x00#8
    | _ => false
  let tlsRelroOk :=
    layoutTlsRelroImg.phdrVaddr == 0x400040#64 &&
    layoutTlsRelroImg.brkStart == 0x422000#64
  let symtabOk :=
    tinyAsmImg.symbols == [] &&
    layoutMidpageBssImg.symbols == [("_start", 0x400200#64)] &&
    layoutMultiRwImg.symbols == [] &&
    layoutTlsRelroImg.symbols == []
  wfOk && multiRwOk && midpageBssOk && tlsRelroOk && symtabOk

theorem elf_loader_diff_corpus_conformance :
    checkElfLoaderDiffCorpusConformance = true := by
  decide +kernel

end_requires_test_files

end Testing.ElfLoaderDiff
