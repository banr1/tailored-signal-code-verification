/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `PqRatchetState::encode_to_vec`: `AllocContractsX` Callee and `memcpy` Wrappers

Stack-bounded (`extHookStack` / `AllocContractsX img A ext`) counterparts of `step_etv_memcpy_call`,
`etv_shim_ok`, `etv_rustAlloc_ok`, and `etv_memcpy_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

theorem subroutine_ok_withStepInv_x {α : Type} {prog : Program} {call_pc : BitVec 64}
    (img : Obj.Image) (s0 : State)
    (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) {S : Spec α}
    (hS : subroutine_ok prog call_pc (S.inImage img)) :
    subroutine_ok prog call_pc (withStepInv s0 S) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hal
  dsimp only [withStepInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv_s, hpre'⟩
  have hpre_img : s.mem ⊨ (S.inImage img).pre x s ∗ R := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hinv_s.1 img hinv0.1, hinv_s.2.1.trans hinv0.2⟩, hpre'⟩
  exact (hS.to_outcome x R s hpc hrun hpre_img hal).mono_outcome fun _ hout => hout

/-- Execute `bl memcpy` at `s.sp = sp - 144#64` with explicit callee stack
`stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)`. -/
theorem step_etv_memcpy_call {resStack : Nat}
    (b : BitVec 64) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem etv_shim_ok {resStack : Nat}
    (hlow : extHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    {entry : BitVec 64} (hfn : (spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (spqrProgAtExt img.base ext)
      (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (shimStackSpecOf resStack)) := by
  subst hfn
  have hshim0 := hAx.shim_ok_at spqrEncodeToVecName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (encodeToVecCalleeStackOf resStack) hlow (Nat.le_of_lt hhigh)
    (by rw [spqrEncodeToVec_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have hshim := subroutine_ok_withStepInv_x img s0 hinv0 hshim0
  apply subroutine_ok_outcome_intro
  intro u R s hpc hrun hpre hal
  have hpre' : s.mem ⊨ (withStepInv s0 (withStack sessionShimSpec (encodeToVecCalleeStackOf resStack))).pre u s ∗ R := by
    dsimp only [withStepInv, withStack, sessionShimSpec, shimStackSpecOf] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine (hshim.to_outcome u R s hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, withStack, sessionShimSpec, shimStackSpecOf] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem stackAt_callee_eq_extHook {resStack : Nat}
    (hlow : extHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
        (encodeToVecCalleeStackOf resStack - extHookStack) ∗
        stackAt sp1 extHookStack := by
  have h := ProofLib.stackAt_split_bottom sp1 extHookStack
    (encodeToVecCalleeStackOf resStack - extHookStack) (by omega)
  have heq : extHookStack + (encodeToVecCalleeStackOf resStack - extHookStack) =
      encodeToVecCalleeStackOf resStack := by omega
  simpa only [heq] using h

theorem etv_rustAlloc_ok {resStack : Nat}
    (hlow : extHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    {entry : BitVec 64} (hfn : (spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (spqrProgAtExt img.base ext)
      (entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (rustAllocStackSpecOf resStack A)) := by
  subst hfn
  have halloc0 := alloc_ok_at_norm_ext_x hAx (name := spqrEncodeToVecName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (by rw [spqrEncodeToVec_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  have halloc := subroutine_ok_withStepInv_x img s0 hinv0 halloc0
  apply subroutine_ok_outcome_intro
  intro sz R s hpc hrun hpre hal
  dsimp only [withStepInv, rustAllocStackSpecOf] at hpre
  rw [stackAt_callee_eq_extHook hlow hhigh s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
    (encodeToVecCalleeStackOf resStack - extHookStack)
  have hpre' : s.mem ⊨ (withStepInv s0 (rustAllocSpecWithStack A extHookStack)).pre (sz, 1) s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, rustAllocSpecWithStack, rustAllocSpec]
    simp only [satisfies_pure_sepConj, sepConj_assoc] at hpre ⊢
    rcases hpre with ⟨hinv_s, ⟨hx0, hx1, hpos, hlt⟩, hm⟩
    have hx1' : (s.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
    refine ⟨hinv_s, ⟨hx0, hx1', hpos, ⟨0, rfl⟩, by omega⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  refine (halloc.to_outcome (sz, 1) (F_rem ∗ R) s hpc hrun hpre' hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, rustAllocSpecWithStack, rustAllocSpec, rustAllocStackSpecOf] at hpost ⊢
    simp only [Nat.mod_one, true_and] at hpost
    rw [stackAt_callee_eq_extHook hlow hhigh s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_memcpy_ok {resStack : Nat}
    (hlow : extHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    {entry : BitVec 64} (hfn : (spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName = entry)
    (s0 : State) (hinv0 : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab) :
    subroutine_ok (spqrProgAtExt img.base ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))) := by
  subst hfn
  exact subroutine_ok_withStepInv_x img s0 hinv0
    (hAx.session_memcpy_region_ok_at spqrEncodeToVecName
      (num% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (encodeToVecCalleeStackOf resStack) hlow (Nat.le_of_lt hhigh)
      (by rw [spqrEncodeToVec_fnOff, (ls_stub% "memcpy")]))

end CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext
