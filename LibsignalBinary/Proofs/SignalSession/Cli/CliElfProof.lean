/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatchPlaced
public import ProofLib.Process
public import ProofLib.StdStartup.Layout
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection

@[expose] public section

set_option autoImplicit false

/-!
# Concrete `CliElfLib` Proofs for `libsignal-cli.elf` (`PIN-1`)

**Checked by Lean. Untrusted (`Role::Proof`).** Discharges the concrete ELF parse, well-formedness,
`brkStart`, segment geometry, and `CliElfMallocngLayout` obligations over the pinned from-source
stock `ld.lld` `libsignal-cli.elf` (`CliElf.cliElfBytes`, `617,448` B, SHA-256 `2f20c836…`) using
pure kernel reduction (`std3` axioms `{propext, Classical.choice, Quot.sound}` only; `0` `sorry`,
`0` `native_decide`, `0` `bv_decide`).
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process Arm64.Snapshot ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession.Cli (ElfStaticOk)
open CryptoVerification.SignalSession.InitStack (stackBase stackBase_eq)
open LibsignalBinary.Heap.Fine (
  CliElfMallocngLayout f3SegCount f3SegByteSum f3RxSegBase f3BrkStart
)

set_option maxRecDepth 200000

/-! ## 1. Reified `ElfImage` Witness & `ElfImage.parse` (`cliElf_parse`) -/

set_option maxRecDepth 4000000 in
/-- Concrete `ElfImage` reified at elaboration time from `.GeneratedLean/cli-elf/libsignal-cli.elf`
(untrusted witness; tied to the SHA-256-pinned `cliElfBytes` by `cliElf_parse`). -/
noncomputable def cliElfImage : ElfImage :=
  elf_image% "../../../../.GeneratedLean/cli-elf/libsignal-cli.elf"

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
/-- `ElfImage.parse` of the pinned `cliElfBytes` returns `cliElfImage`. -/
theorem cliElf_parse : ElfImage.parse cliElfBytes = .ok cliElfImage := by
  apply ElfImage.parse_of_fastParse
  rfl_kernel

/-! ## 2. Static Well-Formedness, `brkStart`, & Segment Geometry -/

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1200000 in
theorem cliElf_wellFormed : cliElfImage.WellFormed = true := by
  rw [← fastWellFormed_eq]
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_brkStart : cliElfImage.brkStart = f3BrkStart := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_brkStart_toNat : cliElfImage.brkStart.toNat = f3BrkStart.toNat := by
  rw [cliElf_brkStart]

theorem cliElf_brkStart_le_stackBase : cliElfImage.brkStart.toNat ≤ stackBase := by
  rw [cliElf_brkStart, stackBase_eq]
  decide

theorem cliElf_brkStart_le_defaultStack :
    cliElfImage.brkStart.toNat ≤ defaultStackTop.toNat - 8388608 := by
  rw [cliElf_brkStart]
  decide

theorem cliElf_staticOk : ElfStaticOk cliElfImage :=
  ⟨cliElf_wellFormed, cliElf_brkStart_le_stackBase⟩

set_option maxRecDepth 4000000 in
theorem cliElf_seg_count : cliElfImage.segments.length = f3SegCount := by
  rfl_kernel

private theorem seg_len_sum_eq_fast (segs : List Snapshot.Region) :
    (segs.map (fun r => r.bytes.length)).sum =
      (segs.map (fun r => fastLen512 1200 r.bytes)).sum := by
  simp only [fastLen512_eq_length]

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1200000 in
theorem cliElf_seg_len_sum :
    (cliElfImage.segments.map (fun r => r.bytes.length)).sum = f3SegByteSum := by
  rw [seg_len_sum_eq_fast]
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg0_lt : 0 < cliElfImage.segments.length := by
  rw [cliElf_seg_count]
  decide

set_option maxRecDepth 4000000 in
theorem cliElf_seg0_start : (cliElfImage.segments[0]'cliElf_seg0_lt).start = cliBase := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg0_perm : (cliElfImage.segments[0]'cliElf_seg0_lt).perm = Perm.ro := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg1_lt : 1 < cliElfImage.segments.length := by
  rw [cliElf_seg_count]
  decide

set_option maxRecDepth 4000000 in
theorem cliElf_seg1_start : (cliElfImage.segments[1]'cliElf_seg1_lt).start = 0x40a000#64 := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg1_perm : (cliElfImage.segments[1]'cliElf_seg1_lt).perm = Perm.rx := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg2_lt : 2 < cliElfImage.segments.length := by
  rw [cliElf_seg_count]
  decide

set_option maxRecDepth 4000000 in
theorem cliElf_seg2_start : (cliElfImage.segments[2]'cliElf_seg2_lt).start = f3RxSegBase := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg2_perm : (cliElfImage.segments[2]'cliElf_seg2_lt).perm = Perm.rx := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem cliElf_seg3_lt : 3 < cliElfImage.segments.length := by
  rw [cliElf_seg_count]
  decide

set_option maxRecDepth 4000000 in
theorem cliElf_seg3_perm : (cliElfImage.segments[3]'cliElf_seg3_lt).perm = Perm.rw := by
  rfl_kernel

end CryptoVerification.SignalSession
