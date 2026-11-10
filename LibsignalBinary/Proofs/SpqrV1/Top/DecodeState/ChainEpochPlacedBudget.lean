/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Merge Helpers

Budget-threaded relocatable `[LibsignalPlacement]` proofs of `ChainEpochPB` tag 2 (`recv`, `+1052`)
and `skip_field(depth=98)` (`+964`), re-exporting tag 1 (`send`) and framing helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix SkipFieldGhost sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB EpochDirectionPB PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred cap_add_one_beq_zero_false chainEpochPBCapOkAt
   chainEpochPBCapOkAt_entails_chainEpochPBAt chainEpochPBCapOkAt_mono decodeStatePlacedEntry
   decodeStatePlacedProg epochDirectionPBCapOkAt_default_init protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateLoopEnv EpochDirectionMergeEnv EpochDirectionMergePostEnv
   FitsEnv.decodeStateLoop_mono FitsEnv.decodeStateLoop_split)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   decodeStateEnv_of_loop_epochDrop_push2_free decodeStateEnv_of_loop_push_epochDrop_push2_free
   decodeState_err_drop_epoch_53c18_placed_ofEnv fitsEnv_epochDrop_push1_of_loop
   fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2
  (decodeState_epoch_recv_call_538dc_placed_ofEnv epochRecvMergeGhost)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
  (optEpochDirectionPB_none_split48 optEpochDirectionPBCapOkAt_some
   optEpochDirectionPBCapOkAt_none optEpochDirectionPBAt_some_eq epochDirectionPBCapOkRestAt)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
  (epochDirectionPBCapOkAt_expose_cap epochDirectionPBCapOkAt_fold_cap
   chainEpochPBCapOkAt_eq chainEpochPBAt_eq epochLoop_cursor_to_epochErrFrame_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
  (epochLoop_calleeErr_to_epochErrFrame_placed fitsEnv_epochDirectionMerge_of_loop
   decodeStateLoopEnv_of_epochDirectionMergePost_ok
   decodeStateLoopEnv_of_epochDirectionMergePost_err fitsEnv_epochMergeErr_push0_of_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
  (fitsEnv_epochMergeErr_push1_of_loop fitsEnv_epochMergeErr_push2_of_loop
   fitsEnv_skipField3_of_loop decodeStateLoopEnv_of_skipField3
   fitsEnv_growOneChainEpoch_of_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux
  (decodeStateLoopEnv_of_growOneChainEpoch)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2
  (epochSendMergeGhost epochRecvMergeGhost decodeState_epoch_send_call_53914_placed_ofEnv
   decodeState_epoch_send_call_53914_placed decodeState_epoch_send_538f0_placed_ofEnv)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux2
  (decodeState_epoch_send_538f0_placed decodeState_epoch_send_538f0_placed_loop
   decodeState_epoch_recv_call_538dc_placed_ofEnv decodeState_epoch_recv_call_538dc_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local irreducible] skipField
  CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
  CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

/-- `SkipFieldGhost` at depth `98` inside `ChainEpochPB::merge` of `spqr::decode_state`. -/
abbrev epochSkipGhost (x : DecodeStateGhost) (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (s0 : State) : SkipFieldGhost :=
  ⟨iwt, tag, 98, s0.sp - 336#64, s0.sp - 1056#64,
    x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩

/-! ## `ChainEpochPB` Tag Body Helpers (`recv`, `skip_field`) -/

/-- Envelope-parameterized Tag 2 (`recv: Option<EpochDirection>`) in `ChainEpochPB` at
`+1052..+1104`, `+1160..+1164`. -/
theorem decodeState_epoch_recv_538b8_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st
      (EpochDirectionMergeEnv (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1052#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = some (d', rest2) →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length
          { curEpoch with recv := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases curEpoch with ⟨optSend, _ | d⟩
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none]
    dsimp only [ChainEpochPB.recv, Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry,
      decodeStateLoopCommonPlaced]
      at hpc herr_of_none hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1088#64)
    refine SepWP.fold (optEpochDirectionPB_none_split48 (s0.sp - 632#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps_sync_pool ((blkPl_325).base + 1088#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold
      (epochDirectionPBCapOkAt_default_init A.repAlloc (s0.sp - 632#64) rest1.length)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_epoch_recv_call_538dc_placed_ofEnv (v20 := v20) hc x st0 st curSt optSend
      default rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
      s0 _ _ R post hpost hs0A hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx20])
      (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
      (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
      (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
      (by simp only [wp_norm, arm64_norm, hx27]) (by simp only [wp_norm, arm64_norm, hx28])
      (by simp only [wp_norm, arm64_norm, hx29])
      (by
        rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)
      hloop
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
    dsimp only [ChainEpochPB.recv, Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry,
      decodeStateLoopCommonPlaced]
      at hpc herr_of_none hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1088#64)
    refine SepWP.fold (epochDirectionPBCapOkAt_expose_cap A.repAlloc (s0.sp - 632#64)
      rest1.length d) (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1
    wp_focus_pure; rintro ⟨hcap, hcap_lt⟩
    have hcmn : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (epochDirectionPBCapOkAt_fold_cap A.repAlloc (s0.sp - 632#64) cap1
      rest1.length d hcap) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_epoch_recv_call_538dc_placed_ofEnv (v20 := v20) hc x st0 st curSt optSend d
      rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
      s0 _ _ R post hpost hs0A hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcmn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by
        rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)
      hloop

theorem decodeState_epoch_recv_538b8_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st
      (EpochDirectionMergeEnv (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1052#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = some (d', rest2) →
      EpochDirectionMergePostEnv
        (epochRecvMergeGhost x (curEpoch.recv.getD default) rest1 iwt s0) evs_ed →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length
          { curEpoch with recv := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_recv_538b8_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
    s0 s P R post hpost hs0A hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

theorem decodeState_epoch_recv_538b8_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 12 ≤ rem)
    (hf : f + 4 * rest1.length + 13 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1052#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = some (d', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_ed) →
      M.stepEvents (evs_acc ++ evs_ed) st0 = M.stepEvents evs_ed st →
      FitsEnv M lim (M.stepEvents evs_ed st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length
          { curEpoch with recv := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := by
  refine decodeState_epoch_recv_538b8_placed (v20 := v20) hc x st0 st curSt curEpoch rest1
    limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none s0 s P R post hpost hs0A
    (fitsEnv_epochDirectionMerge_of_loop hrest1_le (by dsimp only [epochRecvMergeGhost]; omega) hFit)
    (fun n evs_ed hn hed hevs_ed =>
      fitsEnv_epochMergeErr_push0_of_loop (by omega) (by decide : 1 ≤ 4)
        (FitsEnv.decodeStateLoop_split
          (decodeStateLoopEnv_of_epochDirectionMergePost_err hrest1_le hed hevs_ed)
          (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)))
    (fun n evs_ed evs_p0 evs_d hn hed hevs_ed hp0 hd =>
      fitsEnv_epochMergeErr_push1_of_loop (by omega) (by decide : 3 ≤ 4)
        (FitsEnv.decodeStateLoop_split
          (decodeStateLoopEnv_of_epochDirectionMergePost_err hrest1_le hed hevs_ed)
          (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
        evs_p0 evs_d hp0 hd)
    (fun n evs_ed evs_p0 evs_d evs_p1 hn hed hevs_ed hp0 hd hp1 =>
      fitsEnv_epochMergeErr_push2_of_loop (by omega) (by decide : 4 ≤ 4)
        (FitsEnv.decodeStateLoop_split
          (decodeStateLoopEnv_of_epochDirectionMergePost_err hrest1_le hed hevs_ed)
          (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
        evs_p0 evs_d evs_p1 hp0 hd hp1)
    (fun n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f hn hed hevs_ed hp0 hd hp1 hp2 hfree =>
      decodeStateEnv_of_loop_push_epochDrop_push2_free (by omega) (by omega)
        (hacc.append (decodeStateLoopEnv_of_epochDirectionMergePost_err hrest1_le hed hevs_ed))
        (by rw [M.stepEvents_append, hst]) evs_p0 evs_d evs_p1 evs_p2 evs_f hp0 hd hp1 hp2 hfree)
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
  intro d' rest2 evs_ed sf P' hed hevs_ed hle2 hsuf2
  have hed_ok := decodeStateLoopEnv_of_epochDirectionMergePost_ok
    (polyCapBound := 2 * x.st.bytes.length + 16) hrest1_le hed hevs_ed
  exact hloop d' rest2 evs_ed sf P' hed hle2 hsuf2 (hacc.append hed_ok)
    (by rw [M.stepEvents_append, hst])
    (FitsEnv.decodeStateLoop_split hed_ok
      (FitsEnv.decodeStateLoop_mono (by dsimp only [epochRecvMergeGhost]; omega) (Nat.le_refl _) (Nat.le_refl _) hFit))

/-- Envelope-parameterized unknown tag (`skip_field(depth=98)`) in `ChainEpochPB` at
`+964..+980`. -/
theorem decodeState_epoch_skip_53860_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_sf : FitsEnv M lim st (SkipField3Env (epochSkipGhost x rest1 tag iwt s0)))
    (hfits_err1 : ∀ evs_sf evs_d,
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_sf st)) (DecodeErrorPushEnv 0))
    (hfits_err2 : ∀ evs_sf evs_d evs_p1,
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_sf st)))
        (DecodeErrorPushEnv 1))
    (henv_err : ∀ evs_sf evs_d evs_p1 evs_p2 evs_f,
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_sf st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 964#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent) (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = some rest2 →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hsf_call := hc.skipField3
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hsf_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 263)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_skipField3 hsf_call iwt tag 98
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 976#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hx1 := by simp only [arm64_norm, hx1])
    (htag := htag.2) (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hx3 := by simp only [arm64_norm]) (hdepth := by decide) (hlen := by omega)
    (hfits := hfits_sf)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 rest2 evs_sf hsf hevs_sf hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 2
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length) (st := curSt) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 688#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (ep := curEpoch) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_0]) (by simp only [arm64_norm, hrun1])
    exact hloop rest2 evs_sf _ _ hsf hevs_sf hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)
  · intro s1 evs_sf hsf hevs_sf hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    have hcbz : (s1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have hcbnz : (s1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1916#64)
    wp_steps 2
    refine SepWP.fold
      (chainEpochPBCapOkAt_entails_chainEpochPBAt A.repAlloc (s0.sp - 688#64) rest1.length
        curEpoch)
      (by sep_focus) ?_
    have hfold := epochLoop_calleeErr_to_epochErrFrame_placed H_inner A lim
      (M.stepEvents evs_sf st) x hrest1_le hrest1_suf rest1.length curSt curEpoch s0 s1
    dsimp only [decodeStateLoopCommonPlaced] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcbz, hcbnz]) (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_drop_epoch_53c18_placed_ofEnv hc x st0
      (M.stepEvents evs_sf st) curSt curEpoch 0 (by decide)
      (s1.readReg64 (Reg.gpr 0#5)) s0 _ _ R post hpost (herr_of_none hsf)
      (fun evs_d hd => hfits_err1 evs_sf evs_d hsf hevs_sf hd)
      (fun evs_d evs_p1 hd hp1 => hfits_err2 evs_sf evs_d evs_p1 hsf hevs_sf hd hp1)
      (fun evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree =>
        henv_err evs_sf evs_d evs_p1 evs_p2 evs_f hsf hevs_sf hd hp1 hp2 hfree)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcbz, hcbnz])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm])
      (by
        dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
        pool_reg_norm
        sep_ac_rfl))

theorem decodeState_epoch_skip_53860_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_sf : FitsEnv M lim st (SkipField3Env (epochSkipGhost x rest1 tag iwt s0)))
    (hfits_err1 : ∀ evs_sf evs_d,
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_sf st)) (DecodeErrorPushEnv 0))
    (hfits_err2 : ∀ evs_sf evs_d evs_p1,
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_sf st)))
        (DecodeErrorPushEnv 1))
    (henv_err : ∀ evs_sf evs_d evs_p1 evs_p2 evs_f,
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      FreeOnlyEvs evs_d → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_sf st)))))
    (hpc : s.pc = decodeStatePlacedEntry + 964#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent) (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = some rest2 →
      SkipField3Env (epochSkipGhost x rest1 tag iwt s0) evs_sf →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_skip_53860_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch rest1 limitEpoch tag iwt htag hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hs0A hfits_sf hfits_err1 hfits_err2 henv_err
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

theorem decodeState_epoch_skip_53860_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 ≤ rem)
    (hf : f + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 964#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent) (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = some rest2 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 1) x.st.bytes.length (2 * x.st.bytes.length + 16)
        (evs_acc ++ evs_sf) →
      M.stepEvents (evs_acc ++ evs_sf) st0 = M.stepEvents evs_sf st →
      FitsEnv M lim (M.stepEvents evs_sf st)
        (DecodeStateLoopEnv (rem - 1) x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := by
  refine decodeState_epoch_skip_53860_placed (v20 := v20) hc x st0 st curSt curEpoch rest1
    limitEpoch tag iwt htag hrest1_le hrest1_suf hlen_bound herr_of_none s0 s P R post hpost hs0A
    (fitsEnv_skipField3_of_loop (by omega) hFit)
    (fun evs_sf evs_d _ hevs_sf hd =>
      fitsEnv_epochDrop_push1_of_loop (by decide : 0 ≤ 4) (by decide : 2 ≤ 3)
        (FitsEnv.decodeStateLoop_split (decodeStateLoopEnv_of_skipField3 hevs_sf)
          (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
        evs_d hd)
    (fun evs_sf evs_d evs_p1 _ hevs_sf hd hp1 =>
      fitsEnv_epochDrop_push2_of_loop (by decide : 0 + 1 ≤ 4) (by decide : 3 ≤ 3)
        (FitsEnv.decodeStateLoop_split (decodeStateLoopEnv_of_skipField3 hevs_sf)
          (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
        evs_d evs_p1 hd hp1)
    (fun evs_sf evs_d evs_p1 evs_p2 evs_f _ hevs_sf hd hp1 hp2 hfree =>
      decodeStateEnv_of_loop_epochDrop_push2_free (by decide : 0 + 1 ≤ 4) (by omega)
        (hacc.append (decodeStateLoopEnv_of_skipField3 hevs_sf))
        (by rw [M.stepEvents_append, hst]) evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree)
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
  intro rest2 evs_sf sf P' hsf hevs_sf hle2 hsuf2
  have hsf_loop := decodeStateLoopEnv_of_skipField3
    (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16) hevs_sf
  exact hloop rest2 evs_sf sf P' hsf hle2 hsuf2 (hacc.append hsf_loop)
    (by rw [M.stepEvents_append, hst])
    (FitsEnv.decodeStateLoop_split hsf_loop
      (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))

abbrev SepWPpIPlaced.call_epochDirectionMerge_ofEnv :=
  @LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux.SepWPpIPlaced.call_epochDirectionMerge_ofEnv
abbrev SepWPpIPlaced.call_epochDirectionMerge :=
  @LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux.SepWPpIPlaced.call_epochDirectionMerge
abbrev SepWPpIPlaced.call_growOneChainEpoch :=
  @LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux.SepWPpIPlaced.call_growOneChainEpoch

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
