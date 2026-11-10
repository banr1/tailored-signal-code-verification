/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2d Common Infrastructure: `V1State` Encoding Helpers

Provides `_placed` call-wrapper aliases propagating `VmPreserved` across `0`-allocation callees,
together with `A.pool lim st`-threaded exact-capacity specifications (`etv*BudgetExactSpecOf`)
and call wrappers at `s.sp = sp - 144#64`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWPp_call_cs_noPanic)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvCt1SentEncodeSpecOf etvEkSentCt1ReceivedEncodeSpecOf etvPolyDecoderExactSpecOf
   etvPolyEncoderExactSpecOf leafEncLen16Spec leafEncLen48Spec
   step_etv_chunked_encLen48_call_prog step_etv_encode_ct1Sent_call_prog
   step_etv_encode_ekSentCt1Received_call_prog step_etv_encode_polyDecoder_call_prog
   step_etv_encode_polyEncoder_call_prog step_etv_leaf_encLen16_call_prog
   step_etv_v1State_encLen_call_prog)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialDecoderPBGhost PolynomialEncoderPBGhost Unchunked4PBGhost
   Unchunked5PBGhost V1StatePBGhost ct1SentPBPinnedAt
   ekSentCt1ReceivedPBPinnedAt polynomialDecoderPBPinnedAt polynomialEncoderPBPinnedAt
   v1StateJumpTableBytes v1StatePBEncodedLen v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (EtvPolyDecoderGhost EtvPolyEncoderGhost EtvUnchunkedMsgEncodeGhost StepInv
   encodeToVecCalleeStackOf sp_sub_144_aligned withStepInv)

/-! ## 1. Placed Call-Wrapper Aliases (`VmPreserved`-Propagating) -/

theorem step_etv_v1State_encLen_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_v1State_encLen_call_prog hres A hv1Len v1A sp ret_pc g v1 hfit
    hpc hrun hsp halign htr hlr hx0 hinv0 hP hnext

theorem step_etv_leaf_encLen16_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_leaf_encLen16_call_prog hres reprAt encLen hcallee msgA sp ret_pc g m hfit
    hpc hrun hsp halign htr hlr hx0 hinv0 hP hnext

theorem step_etv_chunked_encLen48_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_chunked_encLen48_call_prog hres reprAt encLen hcallee msgA sp ret_pc g m hfit
    hpc hrun hsp halign htr hlr hx0 hinv0 hP hnext

theorem step_etv_encode_polyEncoder_call_placed {resStack : Nat}
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_encode_polyEncoder_call_prog A lim st hpe encA v cap ptr sp ret_pc g enc bs hfit
    hpc hrun hsp halign htr hlr hx0 hx1 hinv0 hP hnext

theorem step_etv_encode_polyDecoder_call_placed {resStack : Nat}
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_encode_polyDecoder_call_prog A lim st hpd tag decA v cap ptr sp ret_pc g dec bs hfit
    hpc hrun hsp halign htr hlr hw0 hx1 hx2 hinv0 hP hnext

theorem step_etv_encode_ekSentCt1Received_call_placed {resStack : Nat}
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_encode_ekSentCt1Received_call_prog A lim st hek msgA v cap ptr sp ret_pc g m bs hfit
    hpc hrun hsp halign htr hlr hx0 hx1 hinv0 hP hnext

theorem step_etv_encode_ct1Sent_call_placed {resStack : Nat}
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
    SepWPp prog ret s P Q Qp oom :=
  step_etv_encode_ct1Sent_call_prog A lim st hct1 msgA v cap ptr sp ret_pc g m bs hfit
    hpc hrun hsp halign htr hlr hx0 hx1 hinv0 hP hnext

/-! ## 2. Pool-Threaded (`A.pool lim st`) Exact-Capacity Encode Specs & Call Wrappers -/

/-- Exact-capacity `A.pool lim st`-threaded contract for `encode<PolynomialEncoder>` at
`s.sp = sp - 144#64` (`0` allocations, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def etvPolyEncoderBudgetExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvPolyEncoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc).length ≤ x.cap.toNat⌝ ∗
      polynomialEncoderPBPinnedAt A.repAlloc x.g x.encA x.enc ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      polynomialEncoderPBPinnedAt A.repAlloc x.g x.encA x.enc ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Exact-capacity `A.pool lim st`-threaded contract for `encode<PolynomialDecoder>` at
`s.sp = sp - 144#64` (`0` allocations, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def etvPolyDecoderBudgetExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvPolyDecoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      polynomialDecoderPBPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      polynomialDecoderPBPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Exact-capacity `A.pool lim st`-threaded contract for `encode<EkSentCt1Received>` at
`s.sp = sp - 144#64` (`0` allocations, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def etvEkSentCt1ReceivedBudgetExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length +
        (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Exact-capacity `A.pool lim st`-threaded contract for `encode<Ct1Sent>` at
`s.sp = sp - 144#64` (`0` allocations, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def etvCt1SentBudgetExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked5PBGhost V1State.Unchunked.Ct1Sent × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length +
        (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length ≤ x.cap.toNat⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr
        (x.bs ++ encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)

theorem step_etv_encode_polyEncoder_budget_call_placed {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
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
    (x := ({ encA := encA, g := g, enc := enc, v := v, cap := cap, ptr := ptr, bs := bs }, st))
    (F := F) hpe hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyEncoderBudgetExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyEncoderBudgetExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_polyDecoder_budget_call_placed {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
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
    (x := ({ tag := tag, decA := decA, g := g, dec := dec, v := v, cap := cap, ptr := ptr, bs := bs }, st))
    (F := F) hpd hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvPolyDecoderBudgetExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvPolyDecoderBudgetExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_ekSentCt1Received_budget_call_placed {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
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
  refine sepWPp_call_cs_noPanic
    (x := ({ msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs }, st))
    (F := F) hek hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvEkSentCt1ReceivedBudgetExactSpecOf, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvEkSentCt1ReceivedBudgetExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_ct1Sent_budget_call_placed {resStack : Nat}
    {M : AllocCostModel} {prog : Program}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
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
  refine sepWPp_call_cs_noPanic
    (x := ({ msgA := msgA, g := g, m := m, v := v, cap := cap, ptr := ptr, bs := bs }, st))
    (F := F) hct1 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, etvCt1SentBudgetExactSpecOf, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, etvCt1SentBudgetExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
