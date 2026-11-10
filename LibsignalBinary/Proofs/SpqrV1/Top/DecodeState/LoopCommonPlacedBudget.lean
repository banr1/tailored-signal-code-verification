/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Shared Loop Frame & Call Wrappers for `spqr::decode_state` (Block `325`)

Defines the budget-threaded active-loop frame `decodeStateLoopCommonPlaced`, proves the
error-frame folding lemmas, and provides panic-aware relocatable call wrappers (`decode_varint`,
`skip_field`, `bytes::merge`, and `ChainParams::merge`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost IsDropSuffix SkipFieldGhost
   decodeVarint_suffix pointsToBytes_prefix_join skip_suffix sliceCursorAfter sliceCursorAt)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack skipField3Stack)
open CryptoVerification.SpqrV1.ProtoRepr (chainParamsPBAt rustBytesVecAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3Stack proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto protoWireTypeToCodec_codecWireTypeToProto
   v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB PqRatchetState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (ChainParamsMergeGhost DecodeStateGhost TraceVRegs V1InnerHeapPred
   chainParamsMergeStack decodeStateSavedAt lower_352_fold
   protoPqRatchetStateAt protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt
   proto_mergeBytes_suffix proto_mergeMessage_suffix sliceCursorAfter_to_memRegion
   sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee upper_240_fold vecArgRestAt
   vecArg_join_bytes vecU8CapOkAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (SkipField3Env skipField3BudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (ChainParamsMergeEnv ChainParamsMergePostEnv chainParamsMergeSpec chainParamsMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)

/-- Reducible alias for `CryptoVerification.SpqrV1.Top.DecodeState.SepWPpIPlaced` so
`SepWPpIPlaced.call_*` budget wrappers live in `LoopCommonPlacedBudget.SepWPpIPlaced` without
colliding with the unbudgeted wrappers in `LoopCommonPlaced`. -/
abbrev SepWPpIPlaced [LibsignalPlacement] (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Q_err : State → SepProp → Prop) : Prop :=
  CryptoVerification.SpqrV1.Top.DecodeState.SepWPpIPlaced prog ret s P Q Q_err

theorem SepWPpIPlaced.of_sepWPp [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Q_err) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  CryptoVerification.SpqrV1.Top.DecodeState.SepWPpIPlaced.of_sepWPp h

theorem SepWPpIPlaced.of_sepWP [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpIPlaced prog ret sm Pm Q Q_err)) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  CryptoVerification.SpqrV1.Top.DecodeState.SepWPpIPlaced.of_sepWP h

theorem SepWPpIPlaced.exists_elim [LibsignalPlacement] {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Q_err : State → SepProp → Prop}
    (h : ∀ x, SepWPpIPlaced prog ret s (P x) Q Q_err) :
    SepWPpIPlaced prog ret s (∃∗ x, P x) Q Q_err :=
  CryptoVerification.SpqrV1.Top.DecodeState.SepWPpIPlaced.exists_elim h

theorem SepWPpIPlaced.mono_pre [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPpIPlaced prog ret s P' Q Q_err) :
    SepWPpIPlaced prog ret s P Q Q_err :=
  CryptoVerification.SpqrV1.Top.DecodeState.SepWPpIPlaced.mono_pre h hwp

/-! ## 1. Budget-Threaded Shared Loop Frame & Error-Frame Folding Lemmas -/

/-- Shared stack & heap frame across the active loops of `spqr::decode_state` under
`[LibsignalPlacement]` with `RustCliAllocBudget M`. -/
abbrev decodeStateLoopCommonPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (s0 s : State) : SepProp :=
  v1StateJumpTablesPlacedAt ∗
  vecArgRestAt A.repAlloc x.st ∗
  memRegion x.outPtr 352 ∗
  A.pool lim st s ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 336 ∗
  ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
  memRegion (s0.sp - 328#64) 224 ∗
  memRegion (s0.sp - 104#64) 8 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Fold `memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗ protoPqRatchetStateAt ... ∗
memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗ decodeStateLoopCommonPlaced`
into `decodeStateErrFramePlaced`. -/
theorem loopCommon_to_errFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 s : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      (x.st.ptr ↦ₛ x.st.bytes) ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateErrFramePlaced]
  have hst := vecArg_join_bytes A.repAlloc x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A.repAlloc x.st ∗ memRegion x.outPtr 352 ∗
          A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      v1StateJumpTablesPlacedAt ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A.repAlloc x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by sep_ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hst (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

/-- Fold `sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur` + `protoPqRatchetStateCapOkAt`
+ `decodeStateLoopCommonPlaced` directly into `decodeStateErrFramePlaced`. -/
theorem loopCommon_cursor_to_errFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remLen : Nat) (curSt : PqRatchetState)
    (s0 s : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s := by
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A.repAlloc
    (s0.sp - 1040#64) remLen curSt
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  rw [sepConj_assoc]
  exact loopCommon_to_errFrame_placed H_inner A lim st x curSt s0 s

/-- Fold callee error cursor output (`memRegion slot 16 ∗ ((ptr + ...) ↦ₛ cur) ∗ (ptr ↦ₛ take)`)
+ `protoPqRatchetStateCapOkAt` + `decodeStateLoopCommonPlaced` into `decodeStateErrFramePlaced`. -/
theorem loopCommon_calleeErr_to_errFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) {cur : List (BitVec 8)} (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur) (remLen : Nat) (curSt : PqRatchetState)
    (s0 s : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A.repAlloc
    (s0.sp - 1040#64) remLen curSt
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) ?_
  exact loopCommon_to_errFrame_placed H_inner A lim st x curSt s0 s

/-- Fold callee error cursor output + `protoPqRatchetStateAt` + `decodeStateLoopCommonPlaced`
into `decodeStateErrFramePlaced`. -/
theorem loopCommon_calleeErr_proto_to_errFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (curSt : PqRatchetState) (s0 s : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateErrFramePlaced H_inner A lim st x curSt s0 s := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  exact loopCommon_to_errFrame_placed H_inner A lim st x curSt s0 s

/-! ## 2. Budget-Threaded Panic-Aware Call Wrappers -/

theorem SepWPpIPlaced.call_decodeVarint2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeVarint2Spec A lim))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (DecodeVarint2Env bs))
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v : BitVec 64) (rest : List (BitVec 8)) (evs : List AllocEvent),
      decodeVarint bs = some (v, rest) →
      DecodeVarint2Env bs evs →
      rest.length < bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = v →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent),
      decodeVarint bs = none →
      DecodeVarint2Env bs evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_dv : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeVarint2Stack) ∗ F
  have hpre : s.mem ⊨ (decodeVarint2Spec A lim).pre (x_dv, st) s ∗ (F_ext ∗ R') := by
    dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeVarint2Stack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext, decodeVarint2Stack]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_dv, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv] at hpost
    rw [hsp] at hpost
    rcases hdv : decodeVarint bs with _ | ⟨v, rest⟩
    · simp only [hdv, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜DecodeVarint2Env bs evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 1#64⌝ ∗ (⌜sm.readReg64 .x1 ≠ 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - decodeVarint2Stack) ∗
                stackAt sp_cur decodeVarint2Stack) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x1) 0 ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext, decodeVarint2Stack]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_1, hx1_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur decodeVarint2Stack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm evs hdv hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_1 hx1_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hdv, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜DecodeVarint2Env bs evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64 ∧ sm.readReg64 .x1 = v⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - decodeVarint2Stack) ∗
                stackAt sp_cur decodeVarint2Stack) ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext, decodeVarint2Stack]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, ⟨hx0_0, hx1_v⟩, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur decodeVarint2Stack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm v rest evs hdv hevs (decodeVarint_length hdv) (decodeVarint_suffix hdv)
          hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 hx1_v
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [decodeVarint2Spec, decodeVarint2SpecGen] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [decodeVarint2Spec, decodeVarint2SpecGen] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [decodeVarint2Spec, decodeVarint2SpecGen] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_skipField3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (skipField3BudgetSpec M A lim))
    (wt : WireType) (tag depth : Nat) (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ) {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (htag : tag < 2 ^ 32)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hx3 : (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth)
    (hdepth : depth ≤ 100)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (SkipField3Env ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩))
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (rest : List (BitVec 8)) (evs : List AllocEvent),
      skipField (2 * bs.length + 2) depth tag wt bs = some rest →
      SkipField3Env ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent),
      skipField (2 * bs.length + 2) depth tag wt bs = none →
      SkipField3Env ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_sf : SkipFieldGhost := ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  have hM : skipField3Stack depth ≤ v1StateMergeStack := by
    have h100 : skipField3Stack 100 ≤ v1StateMergeStack := by decide
    have hmono : skipField3Stack depth ≤ skipField3Stack 100 := by unfold skipField3Stack; omega
    omega
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - skipField3Stack depth) ∗ F
  have hpre : s.mem ⊨ (skipField3BudgetSpec M A lim).pre (x_sf, st) s ∗ (F_ext ∗ R') := by
    dsimp only [skipField3BudgetSpec, x_sf]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, htag, hx2, hx3, by omega, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur (skipField3Stack depth) hM)))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_sf, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [skipField3BudgetSpec, x_sf] at hpost
    rw [hsp] at hpost
    rcases hsf : skipField (2 * bs.length + 2) depth tag wt bs with _ | rest
    · simp only [hsf, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜SkipField3Env x_sf evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - skipField3Stack depth) ∗
                stackAt sp_cur (skipField3Stack depth)) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm evs hsf hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hsf, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜SkipField3Env x_sf evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - skipField3Stack depth) ∗
                stackAt sp_cur (skipField3Stack depth)) ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      have hle := (skip_length (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      have hsuf := (skip_suffix (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm rest evs hsf hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [skipField3BudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [skipField3BudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [skipField3BudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-- Envelope-parameterized budget-threaded contract of `prost::encoding::bytes::merge` (`Block 290`),
generalizing `SignedDepsBudget.bytesMerge3RawBudgetSpec` over `PreEnv` / `PostEnv`. -/
def bytesMerge3RawBudgetSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (PreEnv PostEnv : BytesMergeGhost → List AllocEvent → Prop) :
    Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (PreEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem SepWPpIPlaced.call_bytesMerge3_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : BytesMergeGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpecOfEnv A lim PreEnv PostEnv)))
    (wt : WireType) (valPtr : BitVec 64) (valBs : List (BitVec 8))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = valPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : ∀ valCap valBuf : BitVec 64, BytesMergeCapOk valCap bs.length →
      FitsEnv M lim st (PreEnv ⟨wt, valPtr, valCap, valBuf, valBs, bufRef, slot, ptr, bs⟩))
    (hP : P = (vecU8CapOkAt A.repAlloc valPtr bs.length valBs ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v rest : List (BitVec 8)) (valCap valBuf : BitVec 64)
        (evs : List AllocEvent),
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = some (v, rest) →
      BytesMergeCapOk valCap bs.length →
      PostEnv ⟨wt, valPtr, valCap, valBuf, valBs, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (valCap valBuf : BitVec 64) (evs : List AllocEvent),
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = none →
      BytesMergeCapOk valCap bs.length →
      PostEnv ⟨wt, valPtr, valCap, valBuf, valBs, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          rustBytesVecAt A.repAlloc valPtr valBs ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  rw [hP] at hm
  unfold vecU8CapOkAt at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨valCap, valBuf, hm⟩
  have hm_pure : s.mem ⊨ ⌜BytesMergeCapOk valCap bs.length⌝ ∗
      (((vecU8At A.repAlloc valPtr valCap valBuf valBs ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
        stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F) ∗ R') := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hcap_ok, hm⟩
  let sp_cur := s0.sp - 1392#64
  let x_bm : BytesMergeGhost := ⟨wt, valPtr, valCap, valBuf, valBs, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - bytesMerge3Stack) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpecOfEnv A lim PreEnv PostEnv)).pre
        (x_bm, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [bytesMerge3RawBudgetSpecOfEnv, x_bm]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hcap_ok, hfits valCap valBuf hcap_ok⟩, ?_⟩
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur bytesMerge3Stack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_bm, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (bytesMerge3RawBudgetSpecOfEnv A lim PreEnv PostEnv).post (x_bm, st) s sm ∗
      (F_ext ∗ R') at hpost
    dsimp only [bytesMerge3RawBudgetSpecOfEnv, x_bm] at hpost
    have hmb_eq : mergeBytes wt bs = (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption := by
      have h := proto_mergeBytes_toOption (codecWireTypeToProto wt) bs
      rw [protoWireTypeToCodec_codecWireTypeToProto] at h
      exact h.symm
    rw [hmb_eq, hsp] at hpost
    rcases hmb : (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption with _ | ⟨v, rest⟩
    · simp only [hmb, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_bm evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
            (vecU8At A.repAlloc valPtr valCap valBuf valBs ∗
              (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
                (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                  (v1StateMergeStack - bytesMerge3Stack) ∗
                  stackAt sp_cur bytesMerge3Stack) ∗
                decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗
                memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hvec : vecU8At A.repAlloc valPtr valCap valBuf valBs ⊢
          rustBytesVecAt A.repAlloc valPtr valBs := by
        unfold rustBytesVecAt
        exact Entails.sepExists_right valCap (Entails.sepExists_right valBuf (Entails.refl _))
      have hpost1' := Satisfies.mono (sepConj_mono hvec (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide)))))))) hpost1
      have hpost2 : sm.mem ⊨
          (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt sp_cur v1StateMergeStack ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗
            rustBytesVecAt A.repAlloc valPtr valBs ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R' :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1'
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm valCap valBuf evs hmb hcap_ok hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hmb, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨cap', ptr', evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_bm evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (⌜BytesMergeCapOk cap' rest.length⌝ ∗
              (vecU8At A.repAlloc valPtr cap' ptr' v ∗
                (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
                  (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                    (v1StateMergeStack - bytesMerge3Stack) ∗
                    stackAt sp_cur bytesMerge3Stack) ∗
                  sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_0, hcap', hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hvec' : vecU8At A.repAlloc valPtr cap' ptr' v ⊢
          vecU8CapOkAt A.repAlloc valPtr rest.length v := by
        unfold vecU8CapOkAt
        exact Entails.sepExists_right cap'
          (Entails.sepExists_right ptr' (Entails.pure_right hcap' (Entails.refl _)))
      have hpost1' := Satisfies.mono (sepConj_mono hvec' (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide)))))))) hpost1
      have hpost2 : sm.mem ⊨
          (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt sp_cur v1StateMergeStack ∗
            vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R' :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1'
      have ⟨hle, hsuf⟩ := proto_mergeBytes_suffix hmb
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm v rest valCap valBuf evs hmb hcap_ok hevs hle hsuf hpcm hrunm hspm
          (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2
          (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-- Deterministic-envelope (`MergeDefsBudget.BytesMergeEnv`) budget-threaded contract of
`prost::encoding::bytes::merge` (`Block 290`), matching `DecodeStateIterEnv.of_bytesMergeEnv`. -/
abbrev bytesMerge3DetBudgetSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  bytesMerge3RawBudgetSpecOfEnv A lim BytesMergeEnv BytesMergeEnv

theorem SepWPpIPlaced.call_bytesMerge3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (wt : WireType) (valPtr : BitVec 64) (valBs : List (BitVec 8))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = valPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : ∀ valCap : BitVec 64, BytesMergeCapOk valCap bs.length →
      FitsEnv M lim st (fun evs => evs = bytesMergeEventsCore wt valCap bs))
    (hP : P = (vecU8CapOkAt A.repAlloc valPtr bs.length valBs ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v rest : List (BitVec 8)) (valCap : BitVec 64)
        (evs : List AllocEvent),
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = some (v, rest) →
      BytesMergeCapOk valCap bs.length →
      evs = bytesMergeEventsCore wt valCap bs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (valCap : BitVec 64) (evs : List AllocEvent),
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = none →
      BytesMergeCapOk valCap bs.length →
      evs = bytesMergeEventsCore wt valCap bs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          rustBytesVecAt A.repAlloc valPtr valBs ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  SepWPpIPlaced.call_bytesMerge3_ofEnv (PreEnv := BytesMergeEnv) (PostEnv := BytesMergeEnv)
    hcall wt valPtr valBs bufRef slot ptr bs st hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen
    (fun valCap _ hcap => hfits valCap hcap) hP
    (fun sf v rest valCap _ evs hmb hcap hevs => hok sf v rest valCap evs hmb hcap hevs)
    (fun sf valCap _ evs hmb hcap hevs => herr sf valCap evs hmb hcap hevs)

theorem SepWPpIPlaced.call_chainParamsMerge_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : ChainParamsMergeGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (chainParamsMergeSpecOfEnv A lim PreEnv PostEnv))
    (wt : WireType) (msgPtr : BitVec 64) (msg : ChainParamsPB)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (PreEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (chainParamsPBAt msgPtr msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : ChainParamsPB) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        some (m', rest) →
      PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : ChainParamsPB) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        none →
      PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          chainParamsPBAt msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_cp : ChainParamsMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - chainParamsMergeStack) ∗ F
  have hpre : s.mem ⊨
      (chainParamsMergeSpecOfEnv A lim PreEnv PostEnv).pre (x_cp, st) s ∗ (F_ext ∗ R') := by
    dsimp only [chainParamsMergeSpecOfEnv, x_cp]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur chainParamsMergeStack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_cp, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [chainParamsMergeSpecOfEnv, x_cp] at hpost
    rw [hsp] at hpost
    rcases hcp :
        (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption
        with _ | ⟨m', rest⟩
    · simp only [hcp, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_cp evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - chainParamsMergeStack) ∗
                stackAt sp_cur chainParamsMergeStack) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) n ∗
              chainParamsPBAt msgPtr m' ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hn, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' evs hcp hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hcp, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_cp evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - chainParamsMergeStack) ∗
                stackAt sp_cur chainParamsMergeStack) ∗
              chainParamsPBAt msgPtr m' ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hcp
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest evs hcp hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [chainParamsMergeSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [chainParamsMergeSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [chainParamsMergeSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_chainParamsMerge [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (chainParamsMergeSpec A lim))
    (wt : WireType) (msgPtr : BitVec 64) (msg : ChainParamsPB)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (ChainParamsMergeEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (chainParamsPBAt msgPtr msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : ChainParamsPB) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        some (m', rest) →
      ChainParamsMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : ChainParamsPB) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        none →
      ChainParamsMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          chainParamsPBAt msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  SepWPpIPlaced.call_chainParamsMerge_ofEnv
    (PreEnv := ChainParamsMergeEnv) (PostEnv := ChainParamsMergePostEnv)
    hcall wt msgPtr msg bufRef slot ptr bs st hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen hfits
    hP hok herr

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
