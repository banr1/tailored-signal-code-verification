/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.StdCli.Shims
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common

/-!
# `__rustc::__rust_no_alloc_shim_is_unstable_v2` CLI hook discharge

Placement-generic bridges from `rustAllocShimInstrs = [ .ret .lr ]` and `hbAllocShimSpec` to
`CliExt.shimSpec` (with and without `keepsFs`, `inImage`, and `withStack`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.AllocShim

open Arm64 ProofLib
open ProofLib.StdStartup (StdStatePreserved hasInstrs)
open CaseStudies.Hashbrown.Proofs (hbAllocShimSpec)
open VerifiedLibraries.RustStd.StdCli (HbCliLayout HbShimsCode rustAllocShimInstrs rustAllocShim_ok)
open CryptoVerification.LibsignalTripleRatchet (sessionShimSpec)
open CryptoVerification.SignalSession.CliExt (shimSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack
  subroutine_ok_withStack_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)

theorem shimSpec_eq_sessionShimSpec : shimSpec = sessionShimSpec := rfl

/-- `hbAllocShimSpec` forward-simulates `keepsFs CliExt.shimSpec`. -/
theorem hbAllocShimSpec_simulates_keepsFs_shimSpec :
    SpecSimulates hbAllocShimSpec (keepsFs shimSpec) := by
  refine SpecSimulates.of_map fun _ R s0 hpre => ?_
  refine ⟨(), R, hpre, fun sf _hret _hcc hpost => ?_⟩
  dsimp only [hbAllocShimSpec] at hpost
  rw [satisfies_pure_sepConj] at hpost
  obtain ⟨⟨hstd, _hkf⟩, hR⟩ := hpost
  dsimp only [keepsFs, shimSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hstd.1, ?_⟩
  rw [satisfies_pure_sepConj]
  exact ⟨hstd.2.1, hR⟩

/-- `hbAllocShimSpec` forward-simulates `CliExt.shimSpec`. -/
theorem hbAllocShimSpec_simulates_shimSpec :
    SpecSimulates hbAllocShimSpec shimSpec :=
  hbAllocShimSpec_simulates_keepsFs_shimSpec.trans SpecSimulates.drop_keepsFs

/-! ## Spec-level bridges (`hbAllocShimSpec → CliExt.shimSpec`) -/

/-- Any subroutine satisfying `hbAllocShimSpec` satisfies `keepsFs CliExt.shimSpec`. -/
theorem hbAllocShim_shimSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr hbAllocShimSpec) :
    subroutine_ok P addr (keepsFs shimSpec) :=
  hbAllocShimSpec_simulates_keepsFs_shimSpec.subroutine_ok h

/-- Any subroutine satisfying `hbAllocShimSpec` satisfies `CliExt.shimSpec`. -/
theorem hbAllocShim_shimSpec_ok {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr hbAllocShimSpec) :
    subroutine_ok P addr shimSpec :=
  hbAllocShimSpec_simulates_shimSpec.subroutine_ok h

/-! ## `HbShimsCode` bridges -/

/-- Discharges `keepsFs shimSpec` at `C.rustAllocShimAddr` from `HbShimsCode P C`. -/
theorem rustAllocShim_of_hbShimsCode_shimSpec_keepsFs_ok {P : Program} {C : HbCliLayout}
    (hc : HbShimsCode P C) :
    subroutine_ok P C.rustAllocShimAddr (keepsFs shimSpec) :=
  hbAllocShim_shimSpec_keepsFs_ok (rustAllocShim_ok hc)

/-- Discharges `shimSpec` at `C.rustAllocShimAddr` from `HbShimsCode P C`. -/
theorem rustAllocShim_of_hbShimsCode_shimSpec_ok {P : Program} {C : HbCliLayout}
    (hc : HbShimsCode P C) :
    subroutine_ok P C.rustAllocShimAddr shimSpec :=
  hbAllocShim_shimSpec_ok (rustAllocShim_ok hc)

/-! ## Standalone placement-generic bridges (`hasInstrs P addr rustAllocShimInstrs`) -/

private theorem shim_fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch base = some inst := by
  have hlt : 0 < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off 0 0#64 hlt rfl
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  simpa using hf

/-- Standalone discharge of `hbAllocShimSpec` from `hasInstrs P addr rustAllocShimInstrs`. -/
theorem rustAllocShim_hbAllocShimSpec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr rustAllocShimInstrs) :
    subroutine_ok P addr hbAllocShimSpec := by
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  refine ⟨emp, hpre, ?_⟩
  have hf0 := shim_fetch_at0 hcode
  wp_step
  apply SepWP.done
  · rfl
  · exact hrun
  · refine ⟨fun hm => ?_, rfl, (CalleeSavedPreserved_setPC s0 s0 _).mpr (CalleeSavedPreserved.rfl s0)⟩
    dsimp only [hbAllocShimSpec]
    have hstd : StdStatePreserved s0 (s0.setPC (s0.readReg64 (.gpr 30#5))) := by
      cases s0; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    have hkf : s0.mem.KeepsFrozen (s0.setPC (s0.readReg64 (.gpr 30#5))).mem := by
      cases s0; exact Memory.KeepsFrozen.refl _
    exact Satisfies.mono (sepConj_mono_left (Entails.pure_right_only ⟨hstd, hkf⟩ (Entails.refl _))) hm

/-- `[ .ret .lr ]` at `addr` satisfies `keepsFs CliExt.shimSpec`. -/
theorem rustAllocShim_shimSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr rustAllocShimInstrs) :
    subroutine_ok P addr (keepsFs shimSpec) :=
  hbAllocShim_shimSpec_keepsFs_ok (rustAllocShim_hbAllocShimSpec_ok hcode)

/-- `[ .ret .lr ]` at `addr` satisfies `CliExt.shimSpec`. -/
theorem rustAllocShim_shimSpec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr rustAllocShimInstrs) :
    subroutine_ok P addr shimSpec :=
  hbAllocShim_shimSpec_ok (rustAllocShim_hbAllocShimSpec_ok hcode)

theorem rustAllocShim_shimSpec_inImage_ok {P : Program} {addr : BitVec 64} (img : Obj.Image)
    (hcode : hasInstrs P addr rustAllocShimInstrs) :
    subroutine_ok P addr (shimSpec.inImage img) :=
  subroutine_ok_inImage img (rustAllocShim_shimSpec_ok hcode)

theorem rustAllocShim_withStack_shimSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hookStack : Nat) (hcode : hasInstrs P addr rustAllocShimInstrs) :
    subroutine_ok P addr (keepsFs (withStack shimSpec hookStack)) :=
  subroutine_ok_withStack_keepsFs hookStack (rustAllocShim_shimSpec_keepsFs_ok hcode)

end LibsignalBinary.Proofs.HookDischarge.RustStd.AllocShim
