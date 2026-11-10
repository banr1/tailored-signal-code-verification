/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8RO
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import ProofLib.Placed.OpcodeExclusion
import LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8AsciiSteps
import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAddVm

/-!
# `core::str::converts::from_utf8` RO, `VmPreserved`, and `.rodata`-Free Hook Discharges (`LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8Vm`)

Proves that the real `rustc 1.98.1` `aarch64-unknown-linux-musl` `libcore` code for
`core::str::converts::from_utf8` (`VerifiedLibraries.RustStd.coreMultiLib` block `1`, `fuLib1` /
`fuTree1`, `156` words = `624` B, `0` B stack frame, `0` calls/syscalls) meets:

1. **RO bridges under `withRoDataSep` / `withRoData`** (`Section 1`): lifts
   `VerifiedLibraries.RustStd.coreFromUtf8RO_ok` and `coreFromUtf8RO_subroutineOk` to
   `CalleesRO.fromUtf8AsciiSpecRO hookStack` (`Cli/M24/CalleesRO.lean:91`).
2. **`withVmPreserved` lifts under `withRoData`** (`Section 2`): lifts both read-only
   (`fromUtf8AsciiSpecRO hookStack`) and read-write (`fromUtf8AsciiSpec hookStack`,
   `CliExt.fromUtf8Spec`) contracts to `withVmPreserved` (`keepsFs` and plain).
3. **`.rodata`-free ASCII-only real-code discharges** (`Section 3` RO, `Section 4` RW): on pure-ASCII
   slices (`∀ b ∈ bs, b.toNat < 128`), `coreMultiLib` block `1` never enters the multi-byte branch
   `+0x90` and never reads `corePlacedData1` from memory (`FromUtf8AsciiSteps`), satisfying the bare
   consumer contracts (`fromUtf8AsciiSpecRO hookStack`, `withVmPreserved (fromUtf8AsciiSpecRO hookStack)`,
   `fromUtf8AsciiSpec hookStack`, `CliExt.fromUtf8Spec`, and `withVmPreserved` variants) with **no
   `withRoData` premise**.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8Vm

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement PlacedLib svc0Pat msrTpidrEl0Pat)
open VerifiedLibraries.RustStd (coreMultiLib coreFromUtf8Sym coreUtf8CharWidthSym corePlacedData1
  coreFromUtf8ROSpec coreFromUtf8RO_ok coreFromUtf8RO_subroutineOk
  fromUtf8SretPost memRegion24_eq_fromUtf8Pre)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (fromUtf8Spec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData withRoDataSep
  subroutine_ok_withRoData_of_sep SpecSimulates keepsFs_withRoData)
open LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8 (fromUtf8AsciiSpec
  fromUtf8AsciiSpec_extHookStack runUtf8Validation_of_ascii)
open LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8AsciiSteps (
  sliceRO_lt_two_pow_64_of_sep_region24 coreFromUtf8RO_placed_asciiRO_noRoData_keepsFs_ok
  coreFromUtf8_placed_asciiRW_noRoData_keepsFs_ok)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAddVm (withRoData_withVmPreserved
  subroutine_ok_placedBlock_withVmPreserved_keepsFs pre_strip_withRoData)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO)

private theorem corePlacedData1_length_le : corePlacedData1.length ≤ 2 ^ 64 := by
  have h : corePlacedData1.length = 256 := rfl
  rw [h]; decide

private theorem coreMultiLib_blk1_externAt_none (mpl : MultiPlacement)
    (hpl : coreMultiLib.Placeable mpl) (externs : String → Option (State → State))
    (off : Nat) (hoff : off < 624) :
    (coreMultiLib.blockProgram mpl 1 externs).externAt?
      (mpl.base 1 + BitVec.ofNat 64 off) = none := by
  have hP1 : (coreMultiLib.blockLib 1).text.Placeable (coreMultiLib.blockPlacement mpl 1) :=
    hpl.blocks_ok 1 (by decide)
  have hlen : 0 + 624 ≤ (coreMultiLib.blockLib 1).text.code.length := by decide +kernel
  have hhf := PlacedLib.hookFree_program_noOverrides
    (lib := coreMultiLib.blockLib 1) (pl := coreMultiLib.blockPlacement mpl 1)
    (X := externs) (svc := Syscall.standard) hP1 hlen
  have hoff_eq :
      (mpl.base 1 + BitVec.ofNat 64 off -
        (coreMultiLib.blockProgram mpl 1 externs).base).toNat = off := by
    change (mpl.base 1 + BitVec.ofNat 64 off - mpl.base 1).toNat = off
    rw [Program.add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Program.externAt?
  rw [hoff_eq]
  exact Program.hookAtOff?_eq_none_of_hookFree hhf (Nat.zero_le _) hoff

private theorem specSimulates_add_withRoData {α : Type} (addr : BitVec 64)
    (bytes : List (BitVec 8)) (spec : Spec α) :
    SpecSimulates spec (withRoData addr bytes spec) := fun x R s0 hpre => by
  dsimp only [withRoData] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨x, R, hpre.2, fun _ hout => hout⟩

/-! ## 1. RO Spec-Level & Real-Code Bridges under `withRoDataSep` / `withRoData` -/

private theorem coreFromUtf8RO_simulates_roSep_keepsFs (tbl : BitVec 64)
    (hookStack : Nat := extHookStack) :
    SpecSimulates (coreFromUtf8ROSpec tbl)
      (withRoDataSep tbl corePlacedData1 (keepsFs (fromUtf8AsciiSpecRO hookStack))) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨r, p, bs⟩ R s0 hpre
  dsimp only [withRoDataSep, keepsFs, fromUtf8AsciiSpecRO] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (tbl ↦ᵣ corePlacedData1) ⌜_⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, hascii⟩, hpre⟩ := hpre
  have hlen : bs.length < 2 ^ 64 :=
    sliceRO_lt_two_pow_64_of_sep_region24
      (R := (tbl ↦ᵣ corePlacedData1) ∗ stackAt s0.sp hookStack ∗ R)
      (Satisfies.mono (by sep_entail) hpre)
  rw [memRegion24_eq_fromUtf8Pre r] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨b20, b18, hpre⟩ := hpre
  refine ⟨(p, r, bs, b18, b20), stackAt s0.sp hookStack ∗ R, ?_, ?_⟩
  · dsimp only [coreFromUtf8ROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlen⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [coreFromUtf8ROSpec] at hpost
    rw [runUtf8Validation_of_ascii hascii] at hpost
    dsimp only [fromUtf8SretPost] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    dsimp only [withRoDataSep, keepsFs, fromUtf8AsciiSpecRO]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (tbl ↦ᵣ corePlacedData1) ⌜sf.fs = s0.fs⌝,
      satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_left_comm (tbl ↦ᵣ corePlacedData1) ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝,
      satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs⟩, Satisfies.mono (by sep_entail) hpost⟩

/-- Separating `.rodata` bridge for read-only slice `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_roSep_ok {prog : Program} {entry tbl : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry (coreFromUtf8ROSpec tbl)) :
    subroutine_ok prog entry (withRoDataSep tbl corePlacedData1 (fromUtf8AsciiSpecRO hookStack)) :=
  ((coreFromUtf8RO_simulates_roSep_keepsFs tbl hookStack).trans
    SpecSimulates.drop_keepsFs_withRoDataSep).subroutine_ok h

/-- Pure `.rodata` image-fact bridge for `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_ok {prog : Program} {entry tbl : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry (coreFromUtf8ROSpec tbl)) :
    subroutine_ok prog entry (withRoData tbl corePlacedData1 (fromUtf8AsciiSpecRO hookStack)) :=
  subroutine_ok_withRoData_of_sep corePlacedData1_length_le
    (coreFromUtf8RO_fromUtf8AsciiSpecRO_roSep_ok hookStack h)

/-- `keepsFs` variant of `coreFromUtf8RO_fromUtf8AsciiSpecRO_ok`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_keepsFs_ok {prog : Program} {entry tbl : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry (coreFromUtf8ROSpec tbl)) :
    subroutine_ok prog entry
      (keepsFs (withRoData tbl corePlacedData1 (fromUtf8AsciiSpecRO hookStack))) := by
  rw [keepsFs_withRoData]
  exact ((coreFromUtf8RO_simulates_roSep_keepsFs tbl hookStack).trans
    (SpecSimulates.withRoData_of_sep corePlacedData1_length_le)).subroutine_ok h

/-- Placement-generic real-code discharge (`withRoDataSep`) for `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_roSep_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withRoDataSep (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (fromUtf8AsciiSpecRO hookStack))) :=
  (((coreFromUtf8RO_simulates_roSep_keepsFs (mpl.ρ coreUtf8CharWidthSym) hookStack).trans
    SpecSimulates.drop_keepsFs_withRoDataSep).withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8RO_ok hpl hext)

/-- Placement-generic real-code discharge (`withRoData`) for `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (fromUtf8AsciiSpecRO hookStack))) :=
  ((SpecSimulates.withRoData_of_sep corePlacedData1_length_le).withCodeLoaded
    coreMultiLib mpl).subroutine_ok
    (coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_roSep_ok hookStack hpl hext)

/-- Placement-generic real-code discharge (`keepsFs (withRoData ...)`) for `fromUtf8AsciiSpecRO`. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (keepsFs (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (fromUtf8AsciiSpecRO hookStack)))) := by
  rw [keepsFs_withRoData]
  exact (((coreFromUtf8RO_simulates_roSep_keepsFs (mpl.ρ coreUtf8CharWidthSym) hookStack).trans
    (SpecSimulates.withRoData_of_sep corePlacedData1_length_le)).withCodeLoaded
    coreMultiLib mpl).subroutine_ok (coreFromUtf8RO_ok hpl hext)

/-- `MultiPlacedLib.subroutineOk` (`withRoDataSep`) for `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_roSep_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoDataSep (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (fromUtf8AsciiSpecRO hookStack))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => (coreFromUtf8RO_simulates_roSep_keepsFs (mpl.ρ coreUtf8CharWidthSym) hookStack).trans
      SpecSimulates.drop_keepsFs_withRoDataSep)
    (coreFromUtf8RO_subroutineOk externs)

/-- `MultiPlacedLib.subroutineOk` (`withRoData`) for `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (fromUtf8AsciiSpecRO hookStack))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => SpecSimulates.withRoData_of_sep corePlacedData1_length_le)
    (coreFromUtf8RO_fromUtf8AsciiSpecRO_roSep_subroutineOk hookStack externs)

/-- `MultiPlacedLib.subroutineOk` (`keepsFs (withRoData ...)`) for `fromUtf8AsciiSpecRO hookStack`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_keepsFs_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => keepsFs (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (fromUtf8AsciiSpecRO hookStack)))
      externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_keepsFs_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-! ## 2. `withVmPreserved` Discharges under `withRoData` (RO & RW) -/

/-- Block `1` (`core::str::converts::from_utf8`, `624` B) avoids `SVC #0` under every placement. -/
theorem coreMultiLib_blk1_patchSafe_svc0 :
    coreMultiLib.blocks[1].patchSafe svc0Pat = true := by decide +kernel

/-- Block `1` (`core::str::converts::from_utf8`, `624` B) avoids `MSR TPIDR_EL0` under every placement. -/
theorem coreMultiLib_blk1_patchSafe_msrTpidrEl0 :
    coreMultiLib.blocks[1].patchSafe msrTpidrEl0Pat = true := by decide +kernel

/-- Placement-generic real-code discharge for `keepsFs (withRoData ... (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))`. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (keepsFs (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (withVmPreserved (fromUtf8AsciiSpecRO hookStack))))) := by
  have hlen1 : coreMultiLib.blocks[1].code.length = 624 := by decide +kernel
  rw [withRoData_withVmPreserved]
  exact subroutine_ok_placedBlock_withVmPreserved_keepsFs (lib := coreMultiLib) (mpl := mpl)
    (i := 1) (panAddr? := none)
    (spec := withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
      (fromUtf8AsciiSpecRO hookStack))
    hpl (by decide)
    (fun Q heQ _ =>
      coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_ok hookStack hpl
        (fun off hoff => heQ off (hlen1.symm ▸ hoff)))
    coreMultiLib_blk1_patchSafe_svc0
    coreMultiLib_blk1_patchSafe_msrTpidrEl0
    (fun off hoff => hext off (hlen1 ▸ hoff))
    (fun _ hpa => nomatch hpa)
    (h_pre_strip := pre_strip_withRoData)

/-- Placement-generic real-code discharge for `withRoData ... (withVmPreserved (fromUtf8AsciiSpecRO hookStack))`. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_keepsFs_ok hookStack hpl hext)

/-- `MultiPlacedLib.subroutineOk` for `keepsFs (withRoData ... (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_vmPreserved_keepsFs_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => keepsFs (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (withVmPreserved (fromUtf8AsciiSpecRO hookStack))))
      externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_keepsFs_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `MultiPlacedLib.subroutineOk` for `withRoData ... (withVmPreserved (fromUtf8AsciiSpecRO hookStack))`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_vmPreserved_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
      externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- Placement-generic real-code discharge for RW `keepsFs (withRoData ... (withVmPreserved (fromUtf8AsciiSpec hookStack)))`. -/
theorem coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (keepsFs (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (withVmPreserved (fromUtf8AsciiSpec hookStack))))) := by
  have hlen1 : coreMultiLib.blocks[1].code.length = 624 := by decide +kernel
  have hbase_rw : ∀ Q : Program,
      (∀ off : Nat, off < 624 → Q.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) →
      subroutine_ok Q (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
        (coreMultiLib.withCodeLoaded mpl
          (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
            (fromUtf8AsciiSpec hookStack))) := fun Q heQ =>
    ((SpecSimulates.drop_keepsFs.trans
      (specSimulates_add_withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (fromUtf8AsciiSpec hookStack))).withCodeLoaded coreMultiLib mpl).subroutine_ok
      (coreFromUtf8_placed_asciiRW_noRoData_keepsFs_ok hookStack hpl heQ)
  rw [withRoData_withVmPreserved]
  exact subroutine_ok_placedBlock_withVmPreserved_keepsFs (lib := coreMultiLib) (mpl := mpl)
    (i := 1) (panAddr? := none)
    (spec := withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1 (fromUtf8AsciiSpec hookStack))
    hpl (by decide)
    (fun Q heQ _ => hbase_rw Q (fun off hoff => heQ off (hlen1.symm ▸ hoff)))
    coreMultiLib_blk1_patchSafe_svc0
    coreMultiLib_blk1_patchSafe_msrTpidrEl0
    (fun off hoff => hext off (hlen1 ▸ hoff))
    (fun _ hpa => nomatch hpa)
    (h_pre_strip := pre_strip_withRoData)

/-- Placement-generic real-code discharge for RW `withRoData ... (withVmPreserved (fromUtf8AsciiSpec hookStack))`. -/
theorem coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (withVmPreserved (fromUtf8AsciiSpec hookStack)))) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_keepsFs_ok hookStack hpl hext)

/-- Placement-generic real-code discharge for `CliExt.fromUtf8Spec` (`withVmPreserved` under `withRoData`). -/
theorem coreFromUtf8_placed_fromUtf8Spec_vmPreserved_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
          (withVmPreserved fromUtf8Spec))) :=
  fromUtf8AsciiSpec_extHookStack ▸
    coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_ok extHookStack hpl hext

/-- `MultiPlacedLib.subroutineOk` for RW `withRoData ... (withVmPreserved (fromUtf8AsciiSpec hookStack))`. -/
theorem coreFromUtf8_fromUtf8AsciiSpec_vmPreserved_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (withVmPreserved (fromUtf8AsciiSpec hookStack)))
      externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `MultiPlacedLib.subroutineOk` for `withRoData ... (withVmPreserved CliExt.fromUtf8Spec)`. -/
theorem coreFromUtf8_fromUtf8Spec_vmPreserved_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1
        (withVmPreserved fromUtf8Spec))
      externs :=
  fromUtf8AsciiSpec_extHookStack ▸
    coreFromUtf8_fromUtf8AsciiSpec_vmPreserved_subroutineOk extHookStack externs

/-! ## 3. `.rodata`-Free ASCII-Only Real-Code Discharges (Read-Only Slice `p ↦ᵣ bs`) -/

/-- `.rodata`-free real-code discharge (`keepsFs (fromUtf8AsciiSpecRO hookStack)`): on ASCII
    input, `coreMultiLib` block `1` never reads `corePlacedData1`, so no `withRoData` premise is
    needed. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_noRoData_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (keepsFs (fromUtf8AsciiSpecRO hookStack))) :=
  coreFromUtf8RO_placed_asciiRO_noRoData_keepsFs_ok hookStack hpl hext

/-- `.rodata`-free real-code discharge (`fromUtf8AsciiSpecRO hookStack`). -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_noRoData_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (fromUtf8AsciiSpecRO hookStack)) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_noRoData_keepsFs_ok hookStack hpl hext)

/-- `.rodata`-free `MultiPlacedLib.subroutineOk` (`keepsFs (fromUtf8AsciiSpecRO hookStack)`). -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_noRoData_keepsFs_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun _ => keepsFs (fromUtf8AsciiSpecRO hookStack)) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_noRoData_keepsFs_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `.rodata`-free `MultiPlacedLib.subroutineOk` (`fromUtf8AsciiSpecRO hookStack`). -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_noRoData_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun _ => fromUtf8AsciiSpecRO hookStack) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_noRoData_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `.rodata`-free + `withVmPreserved` real-code discharge
    (`keepsFs (withVmPreserved (fromUtf8AsciiSpecRO hookStack))`). -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_noRoData_keepsFs_ok
    {mpl : MultiPlacement} (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (keepsFs (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))) := by
  have hlen1 : coreMultiLib.blocks[1].code.length = 624 := by decide +kernel
  exact subroutine_ok_placedBlock_withVmPreserved_keepsFs (lib := coreMultiLib) (mpl := mpl)
    (i := 1) (panAddr? := none) (spec := fromUtf8AsciiSpecRO hookStack)
    hpl (by decide)
    (fun Q heQ _ =>
      coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_noRoData_ok hookStack hpl
        (fun off hoff => heQ off (hlen1.symm ▸ hoff)))
    coreMultiLib_blk1_patchSafe_svc0
    coreMultiLib_blk1_patchSafe_msrTpidrEl0
    (fun off hoff => hext off (hlen1 ▸ hoff))
    (fun _ hpa => nomatch hpa)

/-- `.rodata`-free + `withVmPreserved` real-code discharge matching `MainCalleesROBlk617.fromUtf8`
    (`Cli/M24/CalleesRO.lean:139-140`) token-for-token with **no `withRoData` premise**. -/
theorem coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_noRoData_ok
    {mpl : MultiPlacement} (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_noRoData_keepsFs_ok hookStack hpl hext)

/-- `.rodata`-free + `withVmPreserved` `MultiPlacedLib.subroutineOk` (`keepsFs` variant). -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_vmPreserved_noRoData_keepsFs_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun _ => keepsFs (withVmPreserved (fromUtf8AsciiSpecRO hookStack))) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_noRoData_keepsFs_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `.rodata`-free + `withVmPreserved` `MultiPlacedLib.subroutineOk` matching
    `MainCalleesROBlk617.fromUtf8`. -/
theorem coreFromUtf8RO_fromUtf8AsciiSpecRO_vmPreserved_noRoData_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun _ => withVmPreserved (fromUtf8AsciiSpecRO hookStack)) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8RO_placed_fromUtf8AsciiSpecRO_vmPreserved_noRoData_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-! ## 4. `.rodata`-Free ASCII-Only Real-Code Discharges (Read-Write Slice `p ↦ₛ bs`) -/

/-- `.rodata`-free real-code discharge for RW `keepsFs (fromUtf8AsciiSpec hookStack)`. -/
theorem coreFromUtf8_placed_fromUtf8AsciiSpec_noRoData_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (keepsFs (fromUtf8AsciiSpec hookStack))) :=
  coreFromUtf8_placed_asciiRW_noRoData_keepsFs_ok hookStack hpl hext

/-- `.rodata`-free real-code discharge for RW `fromUtf8AsciiSpec hookStack`. -/
theorem coreFromUtf8_placed_fromUtf8AsciiSpec_noRoData_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (fromUtf8AsciiSpec hookStack)) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8_placed_fromUtf8AsciiSpec_noRoData_keepsFs_ok hookStack hpl hext)

/-- `.rodata`-free real-code discharge for `CliExt.fromUtf8Spec` (`CliExternsOk.fromUtf8`). -/
theorem coreFromUtf8_placed_fromUtf8Spec_noRoData_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl fromUtf8Spec) :=
  fromUtf8AsciiSpec_extHookStack ▸
    coreFromUtf8_placed_fromUtf8AsciiSpec_noRoData_ok extHookStack hpl hext

/-- `.rodata`-free `MultiPlacedLib.subroutineOk` for `CliExt.fromUtf8Spec`. -/
theorem coreFromUtf8_fromUtf8Spec_noRoData_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym (fun _ => fromUtf8Spec) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8_placed_fromUtf8Spec_noRoData_ok hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `.rodata`-free + `withVmPreserved` real-code discharge for RW
    `keepsFs (withVmPreserved (fromUtf8AsciiSpec hookStack))`. -/
theorem coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_noRoData_keepsFs_ok
    {mpl : MultiPlacement} (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (keepsFs (withVmPreserved (fromUtf8AsciiSpec hookStack)))) := by
  have hlen1 : coreMultiLib.blocks[1].code.length = 624 := by decide +kernel
  exact subroutine_ok_placedBlock_withVmPreserved_keepsFs (lib := coreMultiLib) (mpl := mpl)
    (i := 1) (panAddr? := none) (spec := fromUtf8AsciiSpec hookStack)
    hpl (by decide)
    (fun Q heQ _ =>
      coreFromUtf8_placed_fromUtf8AsciiSpec_noRoData_ok hookStack hpl
        (fun off hoff => heQ off (hlen1.symm ▸ hoff)))
    coreMultiLib_blk1_patchSafe_svc0
    coreMultiLib_blk1_patchSafe_msrTpidrEl0
    (fun off hoff => hext off (hlen1 ▸ hoff))
    (fun _ hpa => nomatch hpa)

/-- `.rodata`-free + `withVmPreserved` real-code discharge for RW
    `withVmPreserved (fromUtf8AsciiSpec hookStack)` (`MainCalleesBlk617.fromUtf8`). -/
theorem coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_noRoData_ok
    {mpl : MultiPlacement} (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (withVmPreserved (fromUtf8AsciiSpec hookStack))) :=
  (SpecSimulates.drop_keepsFs.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_noRoData_keepsFs_ok hookStack hpl hext)

/-- `.rodata`-free + `withVmPreserved` real-code discharge for `withVmPreserved CliExt.fromUtf8Spec`. -/
theorem coreFromUtf8_placed_fromUtf8Spec_vmPreserved_noRoData_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (withVmPreserved fromUtf8Spec)) :=
  fromUtf8AsciiSpec_extHookStack ▸
    coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_noRoData_ok extHookStack hpl hext

/-- `.rodata`-free + `withVmPreserved` `MultiPlacedLib.subroutineOk` for RW
    `withVmPreserved (fromUtf8AsciiSpec hookStack)`. -/
theorem coreFromUtf8_fromUtf8AsciiSpec_vmPreserved_noRoData_subroutineOk
    (hookStack : Nat := extHookStack)
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun _ => withVmPreserved (fromUtf8AsciiSpec hookStack)) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    coreFromUtf8_placed_fromUtf8AsciiSpec_vmPreserved_noRoData_ok hookStack hpl
      (coreMultiLib_blk1_externAt_none mpl hpl externs)⟩

/-- `.rodata`-free + `withVmPreserved` `MultiPlacedLib.subroutineOk` for
    `withVmPreserved CliExt.fromUtf8Spec`. -/
theorem coreFromUtf8_fromUtf8Spec_vmPreserved_noRoData_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun _ => withVmPreserved fromUtf8Spec) externs :=
  fromUtf8AsciiSpec_extHookStack ▸
    coreFromUtf8_fromUtf8AsciiSpec_vmPreserved_noRoData_subroutineOk extHookStack externs

end LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8Vm
