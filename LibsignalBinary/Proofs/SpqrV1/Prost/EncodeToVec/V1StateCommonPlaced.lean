/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon

/-!
# Relocatable `[LibsignalPlacement]` Phase 2d Common Infrastructure: `V1State` Encoding Helpers

Generic/placed `SepWPp.call_cs` wrappers for `V1State` phase callees in
`<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec` (`Block 426`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem step_etv_v1State_encLen_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {roV1 : BitVec 64}
    {call_pc : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok prog call_pc
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (v1A sp ret_pc : BitVec 64) (g : V1StatePBGhost) (v1 : V1State)
    (hfit : v1StatePBEncodedLen v1 < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v1A)
    (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g v1A v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen v1) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((v1StatePBPinnedAt A g v1A v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack)
  refine SepWPp.call_cs (x := ⟨v1A, g, v1⟩) (F := F_rem ∗ F)
    hv1Len hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))
    rw [stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; ac_rfl)

theorem step_etv_leaf_encLen16_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} {prog : Program}
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok prog call_pc
      (withStepInv s0 (leafEncLen16Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M)
    (hfit : encLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((reprAt g msgA m ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  refine SepWPp.call_cs (x := ⟨msgA, g, m⟩) (F := F_rem ∗ F)
    hcallee hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_unchunkedEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, leafEncLen16Spec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, leafEncLen16Spec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, leafEncLen16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))
    rw [stackAt_callee_eq_unchunkedEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; ac_rfl)

theorem step_etv_chunked_encLen48_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} {prog : Program}
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok prog call_pc
      (withStepInv s0 (leafEncLen48Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M)
    (hfit : encLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((reprAt g msgA m ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (128 + resStack)
  refine SepWPp.call_cs (x := ⟨msgA, g, m⟩) (F := F_rem ∗ F)
    hcallee hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_chunkedEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, leafEncLen48Spec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, leafEncLen48Spec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, leafEncLen48Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))
    rw [stackAt_callee_eq_chunkedEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; ac_rfl)

theorem step_etv_encode_polyEncoder_call_placed {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (encA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((ProtoRepr.polynomialEncoderPBPinnedAt A g encA enc ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { encA := encA, g := g, enc := enc, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hpe hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyEncoderExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvPolyEncoderExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyEncoderExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_polyDecoder_call_placed {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (tag : BitVec 32) (decA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA)
    (hx2 : s.readReg64 .x2 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((ProtoRepr.polynomialDecoderPBPinnedAt A g decA dec ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { tag := tag, decA := decA, g := g, dec := dec, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hpd hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyDecoderExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvPolyDecoderExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyDecoderExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_ekSentCt1Received_call_placed {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked4PBGhost) (m : V1State.Unchunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hfit : bs.length +
      (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          vecU8At A v cap ptr
            (bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hek hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.weaken_pre
      (P' := ⌜cap.toNat ≤ cap'.toNat ∧
        (bs.length + (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)⌝ ∗
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          vecU8At A v cap' ptr'
            (bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hpres⟩ => ?_
    obtain ⟨rfl, rfl⟩ := hpres hfit
    exact hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call)

theorem step_etv_encode_ct1Sent_call_placed {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked5PBGhost) (m : V1State.Unchunked.Ct1Sent) (bs : List (BitVec 8))
    (hfit : bs.length +
      (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗
      vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A g msgA m ∗
          vecU8At A v cap ptr
            (bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs
    (x := { msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := F) hct1 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvCt1SentEncodeSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.weaken_pre
      (P' := ⌜cap.toNat ≤ cap'.toNat ∧
        (bs.length + (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)⌝ ∗
        ((ct1SentPBPinnedAt A g msgA m ∗
          vecU8At A v cap' ptr'
            (bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hpres⟩ => ?_
    obtain ⟨rfl, rfl⟩ := hpres hfit
    exact hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call)

end CryptoVerification.SpqrV1.Prost.EncodeToVec
