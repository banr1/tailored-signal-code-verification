/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Process
public import ProofLib.StdStartup.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatchPlaced
public meta import ProofLib.ProgramReflection
public meta import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars

/-!
# Production `cliElfImage` Aliases and `CliElfMallocngLayout` Witnesses

**Checked by Lean.** Aliases `f3TrialElfBytes` and `f3TrialElf` to `cliElfBytes` and `cliElfImage`,
re-exports parse, symbol-table, and static well-formedness facts, and proves
`CliElfMallocngLayout` on `f3TrialElf` and across `patchElfTokensPlaced` (DEV-CLI10).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (BudgetLimits)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  cliElfBytes cliElfImage cliElf_parse cliElf_wellFormed cliElf_brkStart
  cliElf_brkStart_le_stackBase cliElf_staticOk cliElf_seg_count cliElf_seg_len_sum
  patchRegionByte patchElfByte patchElfTokensPlaced
)
open CryptoVerification.SignalSession.Cli (ElfStaticOk)
open CryptoVerification.SignalSession.InitStack (cliStackSize stackBase)
open LibsignalBinary.Heap.Fine (
  CliElfMallocngLayout f3SegCount f3SegByteSum f3BrkStart
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars (
  cliElfSymChars cliElf_symbols_eq
)

set_option maxRecDepth 200000

/-! ## ELF Aliases, Parse, and Reflected Symbol Table -/

/-- Alias for `CryptoVerification.SignalSession.cliElfBytes`. -/
noncomputable abbrev f3TrialElfBytes : List (BitVec 8) :=
  cliElfBytes

/-- Alias for `CryptoVerification.SignalSession.cliElfImage`. -/
noncomputable abbrev f3TrialElf : ElfImage :=
  cliElfImage

theorem f3TrialElf_parse : ElfImage.parse f3TrialElfBytes = .ok f3TrialElf :=
  cliElf_parse

noncomputable abbrev f3TrialElfSyms : List (String × BitVec 64) := f3TrialElf.symbols

noncomputable abbrev f3TrialElfSymChars : List (List Char × BitVec 64) :=
  cliElfSymChars

theorem f3TrialElfSyms_eq :
    f3TrialElf.symbols = toStringAssoc f3TrialElfSymChars :=
  cliElf_symbols_eq

/-! ## Static Well-Formedness and Segment Bounds -/

theorem f3TrialElf_wellFormed : f3TrialElf.WellFormed = true :=
  cliElf_wellFormed

theorem f3TrialElf_brkStart : f3TrialElf.brkStart = f3BrkStart :=
  cliElf_brkStart

theorem f3TrialElf_brkStart_le_stackBase : f3TrialElf.brkStart.toNat ≤ stackBase :=
  cliElf_brkStart_le_stackBase

theorem f3TrialElf_staticOk : ElfStaticOk f3TrialElf :=
  cliElf_staticOk

theorem f3TrialElf_seg_count : f3TrialElf.segments.length = f3SegCount :=
  cliElf_seg_count

theorem f3TrialElf_seg_len_sum :
    (f3TrialElf.segments.map (fun r => r.bytes.length)).sum = f3SegByteSum :=
  cliElf_seg_len_sum

/-! ## `CliElfMallocngLayout` and Token-Patch Transport -/

private def headSegGeMmapMin : List Snapshot.Region → Bool
  | [] => false
  | r :: _ => decide (MMAP_MIN_ADDR ≤ r.start.toNat)

private theorem exists_seg_ge_mmapMin {segs : List Snapshot.Region}
    (h : headSegGeMmapMin segs = true) :
    ∃ r ∈ segs, MMAP_MIN_ADDR ≤ r.start.toNat := by
  cases segs with
  | nil => cases h
  | cons r rs =>
    exact ⟨r, List.Mem.head rs, of_decide_eq_true h⟩

set_option maxRecDepth 4000000 in
private theorem f3TrialElf_headSegGeMmapMin :
    headSegGeMmapMin f3TrialElf.segments = true := by
  rfl_kernel

/-- `CliElfMallocngLayout` witness on `f3TrialElf` for any `BudgetLimits` accommodating
`f3SegCount + 1` (`5`) static mappings, `cliStackSize + f3SegByteSum` (`8,851,456` B) static bytes,
and physical cap `≤ 2 ^ 30`. -/
theorem f3TrialElf_cliElfMallocngLayout {lim : BudgetLimits}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30) :
    CliElfMallocngLayout f3TrialElf lim := by
  obtain ⟨r0, hr0, hr0Min⟩ := exists_seg_ge_mmapMin f3TrialElf_headSegGeMmapMin
  refine CliElfMallocngLayout.of_segment f3TrialElf_wellFormed hr0 hr0Min ?_ ?_ hphys
  · intro he
    rw [f3TrialElf_seg_count]
    exact hcnt he
  · intro he
    rw [f3TrialElf_seg_len_sum]
    exact hbytes he

private theorem bytes_length_patchRegionByte (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).bytes.length = r.bytes.length := by
  unfold patchRegionByte; dsimp only; split <;> simp

/-- `patchElfByte` preserves `brkStart`, segment count, and segment byte lengths, transporting
`CliElfMallocngLayout` across single-byte `.data` patches. -/
theorem cliElfMallocngLayout_patchElfByte {elf : ElfImage} {lim : BudgetLimits}
    (addr : BitVec 64) (val : BitVec 8) (h : CliElfMallocngLayout elf lim) :
    CliElfMallocngLayout (patchElfByte addr val elf) lim where
  brkStart_min := h.brkStart_min
  staticCount_le he := by
    simpa [patchElfByte] using h.staticCount_le he
  staticBytes_le he := by
    have hmap :
        ((patchElfByte addr val elf).segments.map (fun r => r.bytes.length)) =
          elf.segments.map (fun r => r.bytes.length) := by
      simp [patchElfByte, List.map_map, Function.comp_def, bytes_length_patchRegionByte]
    rw [hmap]
    exact h.staticBytes_le he
  physCap_le := h.physCap_le

/-- Transports `CliElfMallocngLayout` across `patchElfTokensPlaced` (DEV-CLI10). -/
theorem cliElfMallocngLayout_patchElfTokensPlaced [LibsignalPlacement]
    {elf : ElfImage} {lim : BudgetLimits} (h : CliElfMallocngLayout elf lim) :
    CliElfMallocngLayout (patchElfTokensPlaced elf) lim := by
  unfold patchElfTokensPlaced
  exact cliElfMallocngLayout_patchElfByte _ _
    (cliElfMallocngLayout_patchElfByte _ _
      (cliElfMallocngLayout_patchElfByte _ _
        (cliElfMallocngLayout_patchElfByte _ _
          (cliElfMallocngLayout_patchElfByte _ _ h))))

theorem f3TrialElf_patched_cliElfMallocngLayout [LibsignalPlacement] {lim : BudgetLimits}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30) :
    CliElfMallocngLayout (patchElfTokensPlaced f3TrialElf) lim :=
  cliElfMallocngLayout_patchElfTokensPlaced
    (f3TrialElf_cliElfMallocngLayout hcnt hbytes hphys)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture
