/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave1.CoreMemrchr
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common

/-!
# `core::slice::memchr::memrchr` CLI hook discharge

Bridges `VerifiedLibraries.RustStd.coreMemrchrSpec` (`coreMultiLib` block `2`, 296 bytes, 16-byte
stack frame) to `CliExt.memrchrSpec` with zero extra hypotheses (`16 ≤ hookStack ≤ 2 ^ 64`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open VerifiedLibraries.RustStd (coreMultiLib coreMemrchrSym coreMemrchrSpec coreMemrchr_ok
  lastIndexOf)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (MemrchrCall memrchrIdx memrchrSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)

/-- Stack-parameterized `CliExt.memrchrSpec` (`cliMemrchrSpec extHookStack = memrchrSpec`). -/
def cliMemrchrSpec (hookStack : Nat := extHookStack) : Spec MemrchrCall where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.c ∧ s.readReg64 .x1 = x.p ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64⌝ ∗
      (x.p ↦ₛ x.bs) ∗ stackAt s.sp hookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ match memrchrIdx x.c x.bs with
      | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗ (x.p ↦ₛ x.bs) ∗ stackAt s0.sp hookStack

theorem cliMemrchrSpec_extHookStack : cliMemrchrSpec extHookStack = memrchrSpec := rfl

theorem lastIndexOf_eq_memrchrIdx (c : BitVec 8) (bs : List (BitVec 8)) :
    lastIndexOf c bs = memrchrIdx c bs := rfl

private theorem coreMemrchr_simulates_keepsFs {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates coreMemrchrSpec (keepsFs (cliMemrchrSpec hookStack)) := by
  refine SpecSimulates.of_map fun x R s0 hpre => ?_
  dsimp only [keepsFs, cliMemrchrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hpre⟩ := hpre
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2,
    stackAt_eq_stackFrameAt s0.sp 16 (by decide)] at hpre
  have hx0_32 : (s0.readReg32 .x0).truncate 8 = x.c := by
    have hsw : (s0.readReg32 .x0).truncate 8 = (s0.readReg64 .x0).setWidth 8 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx0
  refine ⟨(x.c, x.p, x.bs, s0.sp),
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16) ∗ R, ?_, ?_⟩
  · dsimp only [coreMemrchrSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_32, hx1, hx2, rfl, hlen⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [coreMemrchrSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs, hret_opt⟩, hpost⟩ := hpost
    have hmatch : match memrchrIdx x.c x.bs with
        | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
        | none => sf.readReg64 .x0 = 0#64 := by
      rw [lastIndexOf_eq_memrchrIdx] at hret_opt
      cases hidx : memrchrIdx x.c x.bs with
      | none => simpa [hidx, RustAbi.optionU64] using hret_opt
      | some i => simpa [hidx, RustAbi.optionU64] using hret_opt
    dsimp only [keepsFs, cliMemrchrSpec]
    rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2,
      stackAt_eq_stackFrameAt s0.sp 16 (by decide)]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs, hmatch⟩, Satisfies.mono (by sep_entail) hpost⟩

/-! ## Spec-level bridges (`coreMemrchrSpec → CliExt.memrchrSpec`) -/

/-- Any subroutine satisfying `coreMemrchrSpec` satisfies `cliMemrchrSpec hookStack` whenever
    `16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`. -/
theorem coreMemrchr_cliMemrchrSpec_ok {prog : Program} {entry : BitVec 64}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry coreMemrchrSpec) :
    subroutine_ok prog entry (cliMemrchrSpec hookStack) :=
  ((coreMemrchr_simulates_keepsFs hstk).trans SpecSimulates.drop_keepsFs).subroutine_ok h

/-- Any subroutine satisfying `coreMemrchrSpec` satisfies `keepsFs (cliMemrchrSpec hookStack)`
    whenever `16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`. -/
theorem coreMemrchr_cliMemrchrSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry coreMemrchrSpec) :
    subroutine_ok prog entry (keepsFs (cliMemrchrSpec hookStack)) :=
  (coreMemrchr_simulates_keepsFs hstk).subroutine_ok h

/-- `coreMemrchrSpec` implies `CliExt.memrchrSpec`. -/
theorem coreMemrchr_memrchrSpec_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry coreMemrchrSpec) :
    subroutine_ok prog entry memrchrSpec :=
  coreMemrchr_cliMemrchrSpec_ok (by decide) h

theorem coreMemrchr_memrchrSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry coreMemrchrSpec) :
    subroutine_ok prog entry (keepsFs memrchrSpec) :=
  coreMemrchr_cliMemrchrSpec_keepsFs_ok (by decide) h

theorem coreMemrchr_memrchrSpec_inImage_ok {prog : Program} {entry : BitVec 64}
    (img : Obj.Image) (h : subroutine_ok prog entry coreMemrchrSpec) :
    subroutine_ok prog entry (memrchrSpec.inImage img) :=
  LibsignalBinary.Proofs.HookDischarge.Libc.Common.subroutine_ok_inImage img
    (coreMemrchr_memrchrSpec_ok h)

/-! ## Placed `coreMultiLib` bridges -/

/-- Placement-generic real-code discharge: `coreMultiLib`'s `core::slice::memchr::memrchr` satisfies
    `coreMultiLib.withCodeLoaded mpl (cliMemrchrSpec hookStack)` on any hook-free program `P`. -/
theorem coreMemrchr_placed_cliMemrchrSpec_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl (cliMemrchrSpec hookStack)) :=
  (((coreMemrchr_simulates_keepsFs hstk).trans SpecSimulates.drop_keepsFs).withCodeLoaded
    coreMultiLib mpl).subroutine_ok (coreMemrchr_ok hpl hext)

/-- Placement-generic real-code discharge for `CliExt.memrchrSpec` (`hookStack = extHookStack`). -/
theorem coreMemrchr_placed_memrchrSpec_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl memrchrSpec) :=
  coreMemrchr_placed_cliMemrchrSpec_ok hpl hext (by decide)

/-- `MultiPlacedLib.subroutineOk` for `coreMemrchrSym` against `CliExt.memrchrSpec` under the empty
    extern table (`fun _ => none`). -/
theorem coreMemrchr_memrchrSpec_subroutineOk :
    coreMultiLib.subroutineOk coreMemrchrSym (fun _ => memrchrSpec) :=
  ⟨by decide, 2, 0, by decide, fun mpl hpl =>
    coreMemrchr_placed_memrchrSpec_ok hpl (MultiPlacedLib.externAt?_blockProgram_none coreMultiLib mpl 2)⟩

end LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr
