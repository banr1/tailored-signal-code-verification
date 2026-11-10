/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded / `VmPreserved` Phase 2d Common Infrastructure: `V1State` Encoding Helpers

Defines `VmPreserved`-strengthened `0`-allocation `encoded_len` and exact-capacity `encode`
specifications (`leafEncLen16Spec`, `leafEncLen48Spec`, `etvPoly{Encoder,Decoder}ExactSpecOf`,
`etv{EkSentCt1Received,Ct1Sent}EncodeExactSpecOf`), general budget-threaded `VecU8EncodeEnv`
specifications, and generic `Program` call wrappers at `s.sp = sp - 144#64`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (StepInvVm sepWPp_call_cs_noPanic)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv fitsEnv_vecU8EncodeEnv_of_spare)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage)
open CryptoVerification.SpqrV1.ProtoRepr
  (PinnedEncLenGhost PolynomialDecoderPBGhost PolynomialEncoderPBGhost Unchunked4PBGhost
   Unchunked5PBGhost V1StatePBGhost chunkedEncodedLenStack ct1SentPBPinnedAt
   ekSentCt1ReceivedPBPinnedAt polynomialDecoderPBPinnedAt polynomialEncoderPBPinnedAt
   unchunkedEncodedLenStack v1StateJumpTableBytes
   v1StatePBEncodedLen v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (EtvPolyDecoderGhost EtvPolyEncoderGhost EtvUnchunkedMsgEncodeGhost StepInv
   encodeToVecCalleeStackOf sp_sub_144_aligned stackAt_callee_eq_chunkedEncodedLen
   stackAt_callee_eq_unchunkedEncodedLen stackAt_callee_eq_v1StateEncodedLen withStepInv)

/-! ## 1. `VmPreserved` 0-Allocation `encoded_len` Specs & Generic `{prog}` Call Wrappers -/

/-- `VmPreserved`-strengthened 16-byte stack `encoded_len` specification (`0` allocations). -/
def leafEncLen16Spec {G M : Type} (reprAt : G → BitVec 64 → M → SepProp)
    (encLen : M → Nat) : Spec (PinnedEncLenGhost G M) :=
  withVmPreserved (CryptoVerification.SpqrV1.Prost.EncodeToVec.leafEncLen16Spec reprAt encLen)

/-- `VmPreserved`-strengthened 48-byte stack `encoded_len` specification (`0` allocations). -/
def leafEncLen48Spec {G M : Type} (reprAt : G → BitVec 64 → M → SepProp)
    (encLen : M → Nat) : Spec (PinnedEncLenGhost G M) :=
  withVmPreserved (CryptoVerification.SpqrV1.Prost.EncodeToVec.leafEncLen48Spec reprAt encLen)

theorem step_etv_v1State_encLen_call_prog {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {roV1 call_pc : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok prog call_pc
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (v1A sp ret_pc : BitVec 64) (g : V1StatePBGhost) (v1 : V1State)
    (hfit : v1StatePBEncodedLen v1 < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
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
      VmPreserved s sm →
      SepWPp prog ret sm
        ((v1StatePBPinnedAt A g v1A v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack)
  refine sepWPp_call_cs_noPanic (x := PinnedEncLenGhost.mk v1A g v1) (F := F_rem ∗ F)
    hv1Len hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call) hvm)
    rw [stackAt_callee_eq_v1StateEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; sep_ac_rfl)

theorem step_etv_leaf_encLen16_call_prog {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} {prog : Program}
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok prog call_pc (withStepInv s0 (leafEncLen16Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M)
    (hfit : encLen m < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
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
      VmPreserved s sm →
      SepWPp prog ret sm
        ((reprAt g msgA m ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  refine sepWPp_call_cs_noPanic (x := PinnedEncLenGhost.mk msgA g m) (F := F_rem ∗ F)
    hcallee hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_unchunkedEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, leafEncLen16Spec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.EncodeToVec.leafEncLen16Spec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, leafEncLen16Spec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.EncodeToVec.leafEncLen16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call) hvm)
    rw [stackAt_callee_eq_unchunkedEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; sep_ac_rfl)

theorem step_etv_chunked_encLen48_call_prog {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M : Type} {prog : Program}
    (reprAt : G → BitVec 64 → M → SepProp) (encLen : M → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok prog call_pc (withStepInv s0 (leafEncLen48Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M)
    (hfit : encLen m < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
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
      VmPreserved s sm →
      SepWPp prog ret sm
        ((reprAt g msgA m ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  let F_rem := memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (128 + resStack)
  refine sepWPp_call_cs_noPanic (x := PinnedEncLenGhost.mk msgA g m) (F := F_rem ∗ F)
    hcallee hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_callee_eq_chunkedEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, leafEncLen48Spec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.EncodeToVec.leafEncLen48Spec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, leafEncLen48Spec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.EncodeToVec.leafEncLen48Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call) hvm)
    rw [stackAt_callee_eq_chunkedEncodedLen (by omega) (sp - 144#64)]
    exact Entails.of_eq (by dsimp [F_rem]; sep_ac_rfl)

/-! ## 2. Exact-Capacity (`VmPreserved`, 0-Alloc) & Budget-Threaded `V1State` Encode Callee Specs -/

/-- Exact-capacity 0-allocation (`VmPreserved`) contract for `encode<PolynomialEncoder>` at
`s.sp = sp - 144#64` (no `A.pool` needed; callers pass `A.repAlloc` and frame `A.pool lim st`). -/
def etvPolyEncoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvPolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc).length ≤ x.cap.toNat⌝ ∗
      polynomialEncoderPBPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      polynomialEncoderPBPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc) ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Exact-capacity 0-allocation (`VmPreserved`) contract for `encode<PolynomialDecoder>` at
`s.sp = sp - 144#64` (no `A.pool` needed). -/
def etvPolyDecoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvPolyDecoderGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      polynomialDecoderPBPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      polynomialDecoderPBPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec) ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Exact-capacity 0-allocation (`VmPreserved`) contract for `encode<EkSentCt1Received>` at
`s.sp = sp - 144#64` (no `A.pool` needed). -/
def etvEkSentCt1ReceivedEncodeExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length +
        (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m) ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Exact-capacity 0-allocation (`VmPreserved`) contract for `encode<Ct1Sent>` at
`s.sp = sp - 144#64` (no `A.pool` needed). -/
def etvCt1SentEncodeExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked5PBGhost V1State.Unchunked.Ct1Sent) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length +
        (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length ≤ x.cap.toNat⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m) ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- General budget-threaded contract for `encode<EkSentCt1Received>` (`VecU8EncodeEnv`). -/
def etvEkSentCt1ReceivedEncodeSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received × M.σ) where
  pre := fun (x, st) s =>
    let msgLen := (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + msgLen ≤ x.cap.toNat ∨ x.bs.length + msgLen + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (VecU8EncodeEnv x.cap.toNat (x.bs.length + msgLen))⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    let msg := encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + msg.length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ msg)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜VecU8EncodeEnv x.cap.toNat (x.bs.length + msg.length) evs ∧
          (x.bs.length + msg.length ≤ x.cap.toNat → evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- General budget-threaded contract for `encode<Ct1Sent>` (`VecU8EncodeEnv`). -/
def etvCt1SentEncodeSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked5PBGhost V1State.Unchunked.Ct1Sent × M.σ) where
  pre := fun (x, st) s =>
    let msgLen := (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + msgLen ≤ x.cap.toNat ∨ x.bs.length + msgLen + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (VecU8EncodeEnv x.cap.toNat (x.bs.length + msgLen))⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    let msg := encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + msg.length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ msg)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜VecU8EncodeEnv x.cap.toNat (x.bs.length + msg.length) evs ∧
          (x.bs.length + msg.length ≤ x.cap.toNat → evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-! ## 3. Generic `{prog : Program}` Exact-Capacity Encode Call Wrappers -/

theorem step_etv_encode_polyEncoder_call_prog {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)))
    (encA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm
        ((polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool lim st sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic
    (x := { encA := encA, g := g, enc := enc, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := A.pool lim st s ∗ F) hpe hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyEncoderExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyEncoderExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hvm, htrm⟩ => ?_
    have hpool : A.pool lim st sm = A.pool lim st s := A.pool_transport lim st s sm hvm
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call) hvm)
    rw [hpool]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_etv_encode_polyDecoder_call_prog {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (tag : BitVec 32) (decA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
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
    (hP : P = (polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm
        ((polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool lim st sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  refine sepWPp_call_cs_noPanic
    (x := { tag := tag, decA := decA, g := g, dec := dec, v := v, cap := cap, ptr := ptr, bs := bs })
    (F := A.pool lim st s ∗ F) hpd hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyDecoderExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyDecoderExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hvm, htrm⟩ => ?_
    have hpool : A.pool lim st sm = A.pool lim st s := A.pool_transport lim st s sm hvm
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call) hvm)
    rw [hpool]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_etv_encode_ekSentCt1Received_call_prog {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A lim)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked4PBGhost) (m : V1State.Unchunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hfit : bs.length +
      (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool lim st sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  have hEnv : FitsEnv M lim st
      (VecU8EncodeEnv cap.toNat
        (bs.length + (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length)) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hfit
  refine sepWPp_call_cs_noPanic
    (x := ({ msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs }, st))
    (F := F) hek hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.weaken_pre
      (P' :=
        ⌜cap.toNat ≤ cap'.toNat ∧
          (bs.length +
            (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat →
              cap' = cap ∧ ptr' = ptr)⌝ ∗
        (⌜VecU8EncodeEnv cap.toNat
            (bs.length +
              (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length) evs ∧
          (bs.length +
            (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat →
              evs = [] ∧ VmPreserved s sm)⌝ ∗
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap' ptr'
            (bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hcp⟩ => ?_
    refine SepWPp.pure_elim fun ⟨_, hev⟩ => ?_
    rcases hcp hfit with ⟨rfl, rfl⟩
    rcases hev hfit with ⟨rfl, hvm⟩
    simp only [AllocCostModel.stepEvents]
    exact hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call) hvm

theorem step_etv_encode_ct1Sent_call_prog {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A lim)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked5PBGhost) (m : V1State.Unchunked.Ct1Sent) (bs : List (BitVec 8))
    (hfit : bs.length +
      (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool lim st sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_144_aligned halign
  have hEnv : FitsEnv M lim st
      (VecU8EncodeEnv cap.toNat
        (bs.length + (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length)) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hfit
  refine sepWPp_call_cs_noPanic
    (x := ({ msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs }, st))
    (F := F) hct1 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvCt1SentEncodeSpecOf, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.weaken_pre
      (P' :=
        ⌜cap.toNat ≤ cap'.toNat ∧
          (bs.length +
            (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat →
              cap' = cap ∧ ptr' = ptr)⌝ ∗
        (⌜VecU8EncodeEnv cap.toNat
            (bs.length +
              (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length) evs ∧
          (bs.length +
            (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat →
              evs = [] ∧ VmPreserved s sm)⌝ ∗
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap' ptr'
            (bs ++ encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hcp⟩ => ?_
    refine SepWPp.pure_elim fun ⟨_, hev⟩ => ?_
    rcases hcp hfit with ⟨rfl, rfl⟩
    rcases hev hfit with ⟨rfl, hvm⟩
    simp only [AllocCostModel.stepEvents]
    exact hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call) hvm

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
