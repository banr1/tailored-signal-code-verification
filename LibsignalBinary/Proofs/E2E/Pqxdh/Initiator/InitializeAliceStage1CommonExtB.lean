/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtA
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs -- shake: keep

/-!
# Contract-Backed Panic and Key-Agreement Call Helpers (`tripleRatchetProgAtExt`)

Provides `initAlice_panic_at_raw_vec_handle_error_ext`, `allowPanic_hag_base_ext`, and
`SepWPp_call_hag_alice_ext` on `tripleRatchetProgAtExt` under
`pqxdhCalculateAgreementFrozenSpecExt` (`16608` B stack budget).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFill_ok_at_tripleRatchet
  rngFillAfter0Spec)
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
ls_attribute [local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "alloc::raw_vec::handle_error")

theorem initAlice_panic_at_raw_vec_handle_error_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::raw_vec::handle_error") :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext name k hk

theorem allowPanic_hag_base_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {s0 s : State} {F : SepProp}
    {x : BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64}
    (htr : s.trace = s0.trace) :
    ∀ sf, sf.status = .Panicked →
      PanicOomProp s0 sf
        ((pqxdhCalculateAgreementFrozenSpecExt P A img).onPanic x s sf ∗ F) := by
  intro sf _ R hm
  dsimp only [pqxdhCalculateAgreementFrozenSpecExt, rustPanicOnOom] at hm
  exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm

theorem SepWPp_call_hag_alice_ext {prog : Program} {ret : BitVec 64} {s : State}
    {P_pre : SepProp} {Q : State → SepProp → Prop} {s0 : State} {F : SepProp}
    {call_pc ret_pc fsp : BitVec 64} {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    (hWF : StructuralPrims P)
    (hag : subroutine_ok prog call_pc (pqxdhCalculateAgreementFrozenSpecExt P A img))
    (hF : img.FrozenLoaded s) (ourA : BitVec 64) (our : Bytes) (theirA : BitVec 64) (their : Bytes)
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hsp_eq : s.sp = fsp)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = ourA ∧ s.readReg64 Reg.x1 = theirA ∧
      s.readReg64 Reg.x8 = fsp + 3648#64 ∧ s.sp = fsp ∧ our.length = 32 ∧ their.length = 32)
    (hP : P_pre = (((ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
      memRegion (fsp + 3648#64) 24 ∗ A.pool ∗ stackAt fsp initAliceCalcStackExt) ∗ F))
    (herr : P.x25519 our their = List.replicate 32 0 →
      ∀ (sf : State) (hi : BitVec 56) (u2 : BitVec 64),
        sf.pc = ret_pc → sf.status = .Running → sf.sp = fsp →
        CalleeSavedPreserved s sf → sf.trace = s0.trace → img.FrozenLoaded sf →
        SepWPp prog ret sf (((fsp + 3648#64) ↦₆₄ 1#64) ∗ ((fsp + 3656#64) ↦₆₄ (hi ++ 3#8)) ∗
          ((fsp + 3664#64) ↦₆₄ u2) ∗ (ourA ↦ₛ bytesToBv8 our) ∗
          (theirA ↦ₛ bytesToBv8 their) ∗ A.pool ∗ stackAt fsp initAliceCalcStackExt ∗ F)
          Q (PanicOomProp s0))
    (hok : P.x25519 our their ≠ List.replicate 32 0 →
      ∀ (sf : State) (dh_ptr : BitVec 64),
        sf.pc = ret_pc → sf.status = .Running → sf.sp = fsp →
        CalleeSavedPreserved s sf → sf.trace = s0.trace → img.FrozenLoaded sf →
        SepWPp prog ret sf (((fsp + 3648#64) ↦₆₄ 0#64) ∗ ((fsp + 3656#64) ↦₆₄ dh_ptr) ∗
          ((fsp + 3664#64) ↦₆₄ 32#64) ∗ (dh_ptr ↦ₛ bytesToBv8 (P.x25519 our their)) ∗
          A.live dh_ptr 32 1 ∗ (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool ∗ stackAt fsp initAliceCalcStackExt ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P_pre Q (PanicOomProp s0) := by
  have hsp_align_s : s.spAligned = true := by unfold State.spAligned; rw [hsp_eq]; exact hfsp_align
  refine SepWPp.call_frame_frozen (x := (ourA, our, theirA, their, fsp + 3648#64, fsp))
    hF hag hpc hrun hsp_align_s hlr rfl ⟨hF, hx⟩ hP
    (fun _ _ _ _ hm => allowPanic_not_exited hm) (allowPanic_hag_base_ext htr)
    (fun sf hpc_f hrun_f hsp_f hcs_f hF_f => ?_)
  dsimp only [pqxdhCalculateAgreementFrozenSpecExt, pqxdhCalculateAgreementResultAt]
  rw [htr, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  by_cases hdh : P.x25519 our their = List.replicate 32 0
  · simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.fold (calcErr_entails_at_add3648 fsp) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun u2 => ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun hi => ?_
    simp only [sepConj_assoc]
    exact herr hdh sf hi u2 hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f
  · have hdh_bv_len : (bytesToBv8 (P.x25519 our their)).length = 32 := by
      simp [bytesToBv8, hWF.x25519_len our their]
    simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.fold (boxSliceU8_32_entails_at_add3648 A fsp hdh_bv_len) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun dh_ptr => ?_
    simp only [sepConj_assoc]
    exact hok hdh sf dh_ptr hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f

end CryptoVerification.E2E.Pqxdh.Initiator
