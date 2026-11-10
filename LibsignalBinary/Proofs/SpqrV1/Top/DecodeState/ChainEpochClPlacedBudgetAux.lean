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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Code-Loaded `ChainEpochPB` `send` & Call Helpers

Budget-threaded code-loaded `[LibsignalPlacement]` call wrappers, framing lemmas, tag 1 (`send`, `+1108`),
and tag 2 call helper (`+1088`) for `ChainEpochPB::merge`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.SpqrV1.Alloc (GrowGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB EpochDirectionPB PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred
   cap_add_one_beq_zero_false chainEpochPBCapOkAt decodeStatePlacedEntry decodeStatePlacedProg
   epochDirectionPBCapOkAt_default_init optEpochDirectionPBCapOkAt
   optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt optEpochDirectionPBCapOkAt_mono
   protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned
   stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (GrowOneStrideEnv growOneStrideEvents growOneStrideFullSpec growOneStrideFullSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateLoopEnv EpochDirectionMergeEnv EpochDirectionMergePostEnv
   FitsEnv.decodeStateLoop_mono FitsEnv.decodeStateLoop_split)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   decodeStateEnv_of_loop_push_epochDrop_push2_free
   decodeState_err_epoch_recv_merge_53fec_cl_placed_ofEnv
   decodeState_err_epoch_send_merge_53fd4_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
  (SepWPpIPlaced.call_epochDirectionMerge chainEpochPBAt_eq chainEpochPBCapOkAt_eq
   decodeStateLoopEnv_of_epochDirectionMergePost_err
   decodeStateLoopEnv_of_epochDirectionMergePost_ok epochDirectionPBCapOkAt_expose_cap
   epochDirectionPBCapOkAt_fold_cap epochLoop_calleeErr_to_epochErrFrame_placed
   epochRecvMergeGhost epochSendMergeGhost fitsEnv_epochDirectionMerge_of_loop
   fitsEnv_epochMergeErr_push0_of_loop fitsEnv_epochMergeErr_push1_of_loop
   fitsEnv_epochMergeErr_push2_of_loop optEpochDirectionPBAt_some_eq
   optEpochDirectionPBCapOkAt_none optEpochDirectionPBCapOkAt_some
   optEpochDirectionPB_none_split48)

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

/-! ## Code-Loaded Budget-Threaded `RawVec<ChainEpoch>::grow_one` Call Wrapper -/

theorem SepWPpIPlaced.call_growOneChainEpoch_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)))
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = v)
    (hlen : bs.length = cap.toNat * 112)
    (hptr : ptr ≠ 0#64)
    (hbound : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63)
    (hfits : FitsEnv M lim st (GrowOneStrideEnv cap 112 8))
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.repAlloc.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (p' : BitVec 64) (evs : List AllocEvent),
      p' ≠ 0#64 → p'.toNat % 8 = 0 →
      GrowOneStrideEnv cap 112 8 evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_go : GrowGhost := (v, cap, ptr, bs)
  let callee_stk := (allocHookStack + 48) + 64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - callee_stk) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8)).pre (x_go, st) s ∗
        (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack, x_go]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hptr, hbound, hfits⟩, ?_⟩
    rw [hP] at hm
    simp only [RustCliAllocBudget.repAlloc_live] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur callee_stk (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, callee_stk, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_go, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (growOneStrideFullSpec M A lim 112 8).post (x_go, st) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack, x_go] at hpost
    rw [hsp] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sm ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - callee_stk) ∗
            stackAt sp_cur callee_stk)) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      simp only [RustCliAllocBudget.repAlloc_live]
      dsimp only [sp_cur, callee_stk, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
    rcases hpost_pure with ⟨htrm, ⟨hp'_ne, hp'_al⟩, hpost1⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur callee_stk (by decide)))))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm p' (growOneStrideEvents cap 112 8) hp'_ne hp'_al rfl hpcm hrunm hspm
        (htr.step htrm hcsm) hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneStrideFullSpecWithStack] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneStrideFullSpecWithStack] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneStrideFullSpecWithStack] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## `ChainEpochPB` Tag 1 (`send`) & Tag 2 (`recv`) Call Helpers -/

theorem decodeState_epoch_send_call_53914_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (d : EpochDirectionPB)
    (optRecv : Option EpochDirectionPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st (EpochDirectionMergeEnv (epochSendMergeGhost x d rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1144#64)
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
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length ⟨some d, optRecv⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        some (d', rest2) →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
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
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ⟨some d', optRecv⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hed_call := hc.epochDirectionMerge
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf, chainEpochPBCapOkAt_eq,
    optEpochDirectionPBCapOkAt_some]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hed_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 299)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hsp2c0 : s0.sp - 1392#64 + 704#64 = s0.sp - 688#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_epochDirectionMerge hed_call iwt (s0.sp - 688#64) d
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 1156#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hsp, hsp2c0])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := hfits_ed)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 d' rest2 evs_ed hed hevs_ed hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length) (st := curSt) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optEpochDirectionPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 632#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optRecv) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop d' rest2 evs_ed _ _ hed hevs_ed hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)
  · intro s1 n d' evs_ed hed hevs_ed hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2872#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt A.repAlloc (s0.sp - 632#64)
          rest1.length optRecv)
        (by sep_focus) ?_
      have hfold := epochLoop_calleeErr_to_epochErrFrame_placed H_inner A lim
        (M.stepEvents evs_ed st) x hrest1_le hrest1_suf rest1.length curSt ⟨some d', optRecv⟩ s0 s1
      rw [chainEpochPBAt_eq, optEpochDirectionPBAt_some_eq] at hfold
      dsimp only [decodeStateLoopCommonPlaced] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact decodeState_err_epoch_send_merge_53fd4_cl_placed_ofEnv
        hc.toDecodeStateCalleeContractsClPlaced x st0 (M.stepEvents evs_ed st) curSt
        ⟨some d', optRecv⟩ n (by omega) (s1.readReg64 .x0) s0 _ _ R post hpost (herr_of_none hed)
        (hfits_err1 n evs_ed hn_le hed hevs_ed)
        (fun evs_p0 evs_d hp0 hd => hfits_err2 n evs_ed evs_p0 evs_d hn_le hed hevs_ed hp0 hd)
        (fun evs_p0 evs_d evs_p1 hp0 hd hp1 =>
          hfits_err3 n evs_ed evs_p0 evs_d evs_p1 hn_le hed hevs_ed hp0 hd hp1)
        (fun evs_p0 evs_d evs_p1 evs_p2 evs_f hp0 hd hp1 hp2 hfree =>
          henv_err n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f hn_le hed hevs_ed hp0 hd hp1 hp2
            hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by
          dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
          pool_reg_norm
          sep_ac_rfl)
    · exact absurd hcbnz hx0_ne

theorem decodeState_epoch_send_call_53914_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (d : EpochDirectionPB)
    (optRecv : Option EpochDirectionPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st (EpochDirectionMergeEnv (epochSendMergeGhost x d rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1144#64)
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
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length ⟨some d, optRecv⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        some (d', rest2) →
      EpochDirectionMergePostEnv (epochSendMergeGhost x d rest1 iwt s0) evs_ed →
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
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ⟨some d', optRecv⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_send_call_53914_cl_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt d optRecv rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
    s0 s P R post hpost hs0A hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

/-- Envelope-parameterized code-loaded Tag 1 (`send: Option<EpochDirection>`) in `ChainEpochPB` at
`+1108..+1164`. -/
theorem decodeState_epoch_send_538f0_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st
      (EpochDirectionMergeEnv (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1108#64)
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
        (curEpoch.send.getD default) rest1 98).toOption = some (d', rest2) →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
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
          { curEpoch with send := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases curEpoch with ⟨_ | d, optRecv⟩
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none]
    dsimp only [ChainEpochPB.send, Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry,
      decodeStateLoopCommonPlaced]
      at hpc herr_of_none hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1144#64)
    refine SepWP.fold (optEpochDirectionPB_none_split48 (s0.sp - 688#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps_sync_pool ((blkPl_325).base + 1144#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold
      (epochDirectionPBCapOkAt_default_init A.repAlloc (s0.sp - 688#64) rest1.length)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_epoch_send_call_53914_cl_placed_ofEnv (v20 := v20) hc x st0 st curSt default
      optRecv rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
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
    dsimp only [ChainEpochPB.send, Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry,
      decodeStateLoopCommonPlaced]
      at hpc herr_of_none hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1144#64)
    refine SepWP.fold (epochDirectionPBCapOkAt_expose_cap A.repAlloc (s0.sp - 688#64)
      rest1.length d) (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1
    wp_focus_pure; rintro ⟨hcap, hcap_lt⟩
    have hcmn : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (epochDirectionPBCapOkAt_fold_cap A.repAlloc (s0.sp - 688#64) cap1
      rest1.length d hcap) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_epoch_send_call_53914_cl_placed_ofEnv (v20 := v20) hc x st0 st curSt d
      optRecv rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
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

theorem decodeState_epoch_send_538f0_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st
      (EpochDirectionMergeEnv (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1108#64)
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
        (curEpoch.send.getD default) rest1 98).toOption = some (d', rest2) →
      EpochDirectionMergePostEnv
        (epochSendMergeGhost x (curEpoch.send.getD default) rest1 iwt s0) evs_ed →
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
          { curEpoch with send := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_send_538f0_cl_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt curEpoch rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
    s0 s P R post hpost hs0A hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

theorem decodeState_epoch_send_538f0_cl_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
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
    (hpc : s.pc = decodeStatePlacedEntry + 1108#64)
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
        (curEpoch.send.getD default) rest1 98).toOption = some (d', rest2) →
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
          { curEpoch with send := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) := by
  refine decodeState_epoch_send_538f0_cl_placed (v20 := v20) hc x st0 st curSt curEpoch rest1
    limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none s0 s P R post hpost hs0A
    (fitsEnv_epochDirectionMerge_of_loop hrest1_le (by dsimp only [epochSendMergeGhost]; omega) hFit)
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
      (FitsEnv.decodeStateLoop_mono (by dsimp only [epochSendMergeGhost]; omega) (Nat.le_refl _) (Nat.le_refl _) hFit))

theorem decodeState_epoch_recv_call_538dc_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (optSend : Option EpochDirectionPB) (d : EpochDirectionPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st (EpochDirectionMergeEnv (epochRecvMergeGhost x d rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1088#64)
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
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length ⟨optSend, some d⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        some (d', rest2) →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
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
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ⟨optSend, some d'⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hed_call := hc.epochDirectionMerge
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf, chainEpochPBCapOkAt_eq,
    optEpochDirectionPBCapOkAt_some]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hed_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 299)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx25_38 : s0.sp - 688#64 + 56#64 = s0.sp - 632#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_epochDirectionMerge hed_call iwt (s0.sp - 632#64) d
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 1100#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hx25, hx25_38])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := hfits_ed)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 d' rest2 evs_ed hed hevs_ed hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length) (st := curSt) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optEpochDirectionPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 688#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optSend) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop d' rest2 evs_ed _ _ hed hevs_ed hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
        dsimp only [decodeStateLoopCommonPlaced]
        pool_reg_norm
        sep_ac_rfl)
  · intro s1 n d' evs_ed hed hevs_ed hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2896#64)
    wp_steps 1
    wp_if hcbz
    · exact absurd hcbz hx0_ne
    · wp_steps 1
      refine SepWP.fold
        (optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt A.repAlloc (s0.sp - 688#64)
          rest1.length optSend)
        (by sep_focus) ?_
      have hfold := epochLoop_calleeErr_to_epochErrFrame_placed H_inner A lim
        (M.stepEvents evs_ed st) x hrest1_le hrest1_suf rest1.length curSt ⟨optSend, some d'⟩ s0 s1
      rw [chainEpochPBAt_eq, optEpochDirectionPBAt_some_eq] at hfold
      dsimp only [decodeStateLoopCommonPlaced] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact decodeState_err_epoch_recv_merge_53fec_cl_placed_ofEnv
        hc.toDecodeStateCalleeContractsClPlaced x st0 (M.stepEvents evs_ed st) curSt
        ⟨optSend, some d'⟩ n (by omega) (s1.readReg64 .x0) s0 _ _ R post hpost (herr_of_none hed)
        (hfits_err1 n evs_ed hn_le hed hevs_ed)
        (fun evs_p0 evs_d hp0 hd => hfits_err2 n evs_ed evs_p0 evs_d hn_le hed hevs_ed hp0 hd)
        (fun evs_p0 evs_d evs_p1 hp0 hd hp1 =>
          hfits_err3 n evs_ed evs_p0 evs_d evs_p1 hn_le hed hevs_ed hp0 hd hp1)
        (fun evs_p0 evs_d evs_p1 evs_p2 evs_f hp0 hd hp1 hp2 hfree =>
          henv_err n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f hn_le hed hevs_ed hp0 hd hp1 hp2
            hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by
          dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
          pool_reg_norm
          sep_ac_rfl)

theorem decodeState_epoch_recv_call_538dc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (curSt : PqRatchetState)
    (optSend : Option EpochDirectionPB) (d : EpochDirectionPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hfits_ed : FitsEnv M lim st (EpochDirectionMergeEnv (epochRecvMergeGhost x d rest1 iwt s0)))
    (hfits_err1 : ∀ n evs_ed, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      FitsEnv M lim (M.stepEvents evs_ed st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_ed evs_p0 evs_d, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st)))
        (DecodeErrorPushEnv (n + 1)))
    (hfits_err3 : ∀ n evs_ed evs_p0 evs_d evs_p1, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))
        (DecodeErrorPushEnv (n + 2)))
    (henv_err : ∀ n evs_ed evs_p0 evs_d evs_p1 evs_p2 evs_f, n ≤ 1 →
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        none →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      DecodeErrorPushEnv (n + 1) evs_p1 → DecodeErrorPushEnv (n + 2) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f
            (M.stepEvents evs_p2
              (M.stepEvents evs_p1
                (M.stepEvents evs_d (M.stepEvents evs_p0 (M.stepEvents evs_ed st))))))
    (hpc : s.pc = decodeStatePlacedEntry + 1088#64)
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
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length ⟨optSend, some d⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (evs_ed : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        some (d', rest2) →
      EpochDirectionMergePostEnv (epochRecvMergeGhost x d rest1 iwt s0) evs_ed →
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
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ⟨optSend, some d'⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ed st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_recv_call_538dc_cl_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st curSt optSend d rest1 limitEpoch iwt hrest1_le hrest1_suf hlen_bound herr_of_none
    s0 s P R post hpost hs0A hfits_ed hfits_err1 hfits_err2 hfits_err3 henv_err
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudgetAux
