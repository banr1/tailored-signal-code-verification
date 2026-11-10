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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Code-Loaded `ChainEpochPB` Dispatch & Loop Body

Budget-threaded code-loaded `[LibsignalPlacement]` proofs of `ChainEpochPB` tag dispatch (`+1036`)
and single loop iteration (`+996`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (mergeLoopBin protoPrefixStep_chainEpochPB_mergeField)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB PqRatchetState spqrDecodeState)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred chainEpochPBCapOkAt
   chainEpochPBCapOkAt_entails_chainEpochPBAt chainEpochPBCapOkAt_mono
   chainEpochPB_mergeField_other chainEpochPB_mergeField_tag1 chainEpochPB_mergeField_tag2
   codecWireTypeToProto decodeStatePlacedEntry decodeStatePlacedProg key_and7_of_wt_none
   key_and7_of_wt_some key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge key_lsr3_32_eq
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned tag_cbz32_false tag_cbz64_false
   tag_cmp32_of_gt tag_lt_pow29_of_key_lt tag_setWidth32_ofNat tag_zeroExtend64_ofNat32
   truncate32_zeroExtend64_lsr3 wt_setWidth8 wt_ult6)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_mono
   FitsEnv.decodeStateLoop_split FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (fitsEnv_decodeErrorFrom_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   decodeStateEnv_of_loop_epochDrop_push2_free decodeStateEnv_of_loop_from_epochDrop_push2_free
   decodeStateEnv_of_loop_push_epochDrop_push2_free decodeState_err_drop_epoch_53c18_cl_placed_ofEnv
   decodeState_err_epoch_invalid_wt_53bf8_cl_placed_ofEnv
   decodeState_err_epoch_key_overflow_53bec_cl_placed_ofEnv
   decodeState_err_epoch_zero_tag_53c04_cl_placed_ofEnv fitsEnv_epochDrop_push1_of_loop
   fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
  (SepWPpIPlaced.call_decodeVarint2_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudget
  (decodeStateLoopEnv_of_epochDirectionMergePost_err
   decodeStateLoopEnv_of_epochDirectionMergePost_ok decodeStateLoopEnv_of_skipField3
   decodeState_epoch_recv_538b8_cl_placed_ofEnv decodeState_epoch_send_538f0_cl_placed_ofEnv
   decodeState_epoch_skip_53860_cl_placed_ofEnv epochRecvMergeGhost epochSendMergeGhost
   fitsEnv_epochDirectionMerge_of_loop fitsEnv_epochMergeErr_push0_of_loop
   fitsEnv_epochMergeErr_push1_of_loop fitsEnv_epochMergeErr_push2_of_loop
   fitsEnv_skipField3_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
  (after_decodeVarint2_err_to_epochErrFrame_placed after_decodeVarint2_to_epochErrFrame_placed
   decodeVarint2Env_eq_nil_of_some fitsEnv_decodeVarint2_of_loop
   fitsEnv_from_epochDrop_push1_of_loop fitsEnv_from_epochDrop_push2_of_loop lift_postEnv
   stepEvents_nil_of_acc)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] truncate32_zeroExtend64_lsr3

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

/-! ## Tag Dispatch and Single Loop Iteration of `ChainEpochPB::merge` (Code-Loaded) -/

private theorem prost_codecWireTypeToProto_eq (iwt : WireType) :
    CryptoVerification.SpqrV1.Prost.MessageMerge.codecWireTypeToProto iwt =
      codecWireTypeToProto iwt := by
  cases iwt <;> rfl

/-- Envelope-parameterized code-loaded tag dispatch for `ChainEpochPB` at `+1036` given
`1 ≤ tag < 2 ^ 29`. -/
theorem decodeState_epoch_dispatch_538a8_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (match (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption with
       | none => none
       | some (ep', rest2) => mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 12 ≤ rem)
    (hf : f + 4 * rest1.length + 13 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1036#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_step : List AllocEvent)
        (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption =
        some (ep', rest2) →
      DecodeStateLoopEnv (f + (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  have hwt8 := wt_setWidth8 iwt
  by_cases htag1 : tag = 1
  · subst htag1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1108#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    refine decodeState_epoch_send_538f0_cl_placed_ofEnv (v20 := v20)
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st curSt curEpoch rest1 limitEpoch iwt
      hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [prost_codecWireTypeToProto_eq] at hnone
        rw [show BitVec.ofNat 32 1 = 1#32 from rfl, chainEpochPB_mergeField_tag1, hnone]; rfl))
      s0 _ _ R post hpost hs0A
      (fitsEnv_epochDirectionMerge_of_loop hrest1_le
        (by dsimp only [epochSendMergeGhost]; omega) hFit)
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
        lift_postEnv hpost_env
          (decodeStateEnv_of_loop_push_epochDrop_push2_free (by omega) (by omega)
            (hacc.append (decodeStateLoopEnv_of_epochDirectionMergePost_err hrest1_le hed hevs_ed))
            (by rw [M.stepEvents_append, hst]) evs_p0 evs_d evs_p1 evs_p2 evs_f hp0 hd hp1 hp2 hfree))
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0, hwt8])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl) ?_
    intro d' rest2 evs_ed sf P' hed hevs_ed hle2 hsuf2 hpc'
    have hed_ok := decodeStateLoopEnv_of_epochDirectionMergePost_ok
      (polyCapBound := 2 * x.st.bytes.length + 16) hrest1_le hed hevs_ed
    exact hnext { curEpoch with send := some d' } rest2 evs_ed sf P' hle2 hsuf2
      (by rw [prost_codecWireTypeToProto_eq] at hed
          rw [show BitVec.ofNat 32 1 = 1#32 from rfl, chainEpochPB_mergeField_tag1, hed]; rfl)
      ((hacc.append hed_ok).mono_fuel (by dsimp only [epochSendMergeGhost]; omega))
      (by rw [M.stepEvents_append, hst])
      (FitsEnv.decodeStateLoop_split hed_ok
        (FitsEnv.decodeStateLoop_mono (by dsimp only [epochSendMergeGhost]; omega)
          (Nat.le_refl _) (Nat.le_refl _) hFit))
      hpc'
  · by_cases htag2 : tag = 2
    · subst htag2
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1052#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      refine decodeState_epoch_recv_538b8_cl_placed_ofEnv (v20 := v20)
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc x st0 st curSt curEpoch rest1 limitEpoch iwt
        hrest1_le hrest1_suf hlen_bound
        (fun hnone => herr_of_none (by
          rw [prost_codecWireTypeToProto_eq] at hnone
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, chainEpochPB_mergeField_tag2, hnone]; rfl))
        s0 _ _ R post hpost hs0A
        (fitsEnv_epochDirectionMerge_of_loop hrest1_le
          (by dsimp only [epochRecvMergeGhost]; omega) hFit)
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
          lift_postEnv hpost_env
            (decodeStateEnv_of_loop_push_epochDrop_push2_free (by omega) (by omega)
              (hacc.append (decodeStateLoopEnv_of_epochDirectionMergePost_err hrest1_le hed hevs_ed))
              (by rw [M.stepEvents_append, hst]) evs_p0 evs_d evs_p1 evs_p2 evs_f hp0 hd hp1 hp2 hfree))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0, hwt8])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
        (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29])
        (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl) ?_
      intro d' rest2 evs_ed sf P' hed hevs_ed hle2 hsuf2 hpc'
      have hed_ok := decodeStateLoopEnv_of_epochDirectionMergePost_ok
        (polyCapBound := 2 * x.st.bytes.length + 16) hrest1_le hed hevs_ed
      exact hnext { curEpoch with recv := some d' } rest2 evs_ed sf P' hle2 hsuf2
        (by rw [prost_codecWireTypeToProto_eq] at hed
            rw [show BitVec.ofNat 32 2 = 2#32 from rfl, chainEpochPB_mergeField_tag2, hed]; rfl)
        ((hacc.append hed_ok).mono_fuel (by dsimp only [epochRecvMergeGhost]; omega))
        (by rw [M.stepEvents_append, hst])
        (FitsEnv.decodeStateLoop_split hed_ok
          (FitsEnv.decodeStateLoop_mono (by dsimp only [epochRecvMergeGhost]; omega)
            (Nat.le_refl _) (Nat.le_refl _) hFit))
        hpc'
    · have ⟨_, _, _, _, hbeq1, hbne1⟩ := tag_cmp32_of_gt (c := 1) (by omega) htag29
      have ⟨_, _, _, _, hbeq2, hbne2⟩ := tag_cmp32_of_gt (c := 2) (by omega) htag29
      have htw32 := tag_setWidth32_ofNat tag
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 964#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm, hx1, htw32, hbeq1, hbne1, hbeq2, hbne2])
        (by simp only [arm64_norm, hrun])
      refine decodeState_epoch_skip_53860_cl_placed_ofEnv (v20 := v20)
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc.toDecodeStateCalleeContractsClPlaced x st0 st curSt curEpoch rest1 limitEpoch tag iwt
        ⟨by omega, by omega⟩ hrest1_le hrest1_suf hlen_bound
        (fun hnone => herr_of_none (by
          rw [chainEpochPB_mergeField_other curEpoch tag htag1 htag2 (by omega) iwt rest1 98, hnone]
          rfl))
        s0 _ _ R post hpost hs0A
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
          lift_postEnv hpost_env
            (decodeStateEnv_of_loop_epochDrop_push2_free (by decide : 0 + 1 ≤ 4) (by omega)
              (hacc.append (decodeStateLoopEnv_of_skipField3 hevs_sf))
              (by rw [M.stepEvents_append, hst]) evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree))
        (by dsimp only [decodeStatePlacedEntry]
            simp only [arm64_norm, hx1, htw32, hbeq1, hbne1, hbeq2, hbne2])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0, hwt8])
        (by simp only [arm64_norm, hx1, htw32])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
        (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29])
        (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl) ?_
      intro rest2 evs_sf sf P' hsf hevs_sf hle2 hsuf2 hpc'
      have hsf_loop := decodeStateLoopEnv_of_skipField3
        (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16) hevs_sf
      exact hnext curEpoch rest2 evs_sf sf P' hle2 hsuf2
        (by rw [chainEpochPB_mergeField_other curEpoch tag htag1 htag2 (by omega) iwt rest1 98, hsf]
            rfl)
        ((hacc.append hsf_loop).mono_fuel (by omega))
        (by rw [M.stepEvents_append, hst])
        (FitsEnv.decodeStateLoop_split hsf_loop
          (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
        hpc'

theorem decodeState_epoch_dispatch_538a8_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (match (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption with
       | none => none
       | some (ep', rest2) => mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98) = none →
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
    (hpc : s.pc = decodeStatePlacedEntry + 1036#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_step : List AllocEvent)
        (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption =
        some (ep', rest2) →
      DecodeStateLoopEnv (f + (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_dispatch_538a8_cl_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem curSt curEpoch rest1 limitEpoch tag iwt
    htag1_le htag29 hrest1_le hrest1_suf hlen_bound herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hnext

theorem decodeState_epoch_dispatch_538a8_cl_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (match (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption with
       | none => none
       | some (ep', rest2) => mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98) = none →
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
    (hpc : s.pc = decodeStatePlacedEntry + 1036#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_step : List AllocEvent)
        (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (ChainEpochPB.mergeField curEpoch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 98).toOption =
        some (ep', rest2) →
      DecodeStateLoopEnv (f + (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_dispatch_538a8_cl_placed
    (v20 := v20) hc x st0 st evs_acc f rem curSt curEpoch rest1 limitEpoch tag iwt
    htag1_le htag29 hrest1_le hrest1_suf hlen_bound herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost hs0A
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hnext

/-- Envelope-parameterized code-loaded single field-key decode + tag dispatch step of `ChainEpochPB`
at `+996`, when `¬ cur.length ≤ limitEpoch`. -/
theorem decodeState_epoch_body_53880_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (cur : List (BitVec 8)) (limitEpoch : Nat) (hgt : ¬ cur.length ≤ limitEpoch)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * cur.length + 8 ≤ rem)
    (hf : f + 4 * cur.length + 9 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_body : List AllocEvent)
        (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
        mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98 →
      DecodeStateLoopEnv (f + 4 * (cur.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_body) →
      M.stepEvents (evs_acc ++ evs_body) st0 = M.stepEvents evs_body st →
      FitsEnv M lim (M.stepEvents evs_body st)
        (DecodeStateLoopEnv (rem - 4 * (cur.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_body st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur st
    (ret_pc := (blkPl_325).base + 1004#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := fitsEnv_decodeVarint2_of_loop (by omega) hFit)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 key rest1 evs_dv hdv hevs_dv hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
    have hdv_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv hevs_dv
    subst hdv_nil
    rw [stepEvents_nil_of_acc hst]
    have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
    have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
    have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · have hk_ne : (key >>> 32 == 0#64) = false := key_lsr32_ne_zero_of_ge hk
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1872#64)
      wp_steps 3
      have hfold := after_decodeVarint2_to_epochErrFrame_placed H_inner A lim st x
        hcur_le hcur_suf hle1 curSt curEpoch s0 s1
      dsimp only [decodeStateLoopCommonPlaced] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1])
      exact decodeState_err_epoch_key_overflow_53bec_cl_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc.toDecodeStateCalleeContractsClPlaced x st0 st curSt curEpoch s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_of_key_ge protoPrefixStep_chainEpochPB_mergeField hgt hdv hk))
        (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
        (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
        (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
        (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
          lift_postEnv hpost_env
            (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
              evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by
          dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
          pool_reg_norm
          try sep_ac_rfl)
    · have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk
      rcases hwt : WireType.ofNat? (key.toNat % 8) with _ | iwt
      · rcases key_and7_of_wt_none hwt with hand7 | hand7
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1884#64)
          wp_steps 6
          have hfold := after_decodeVarint2_to_epochErrFrame_placed H_inner A lim st x
            hcur_le hcur_suf hle1 curSt curEpoch s0 s1
          dsimp only [decodeStateLoopCommonPlaced] at hfold
          refine SepWP.fold hfold (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1])
          exact decodeState_err_epoch_invalid_wt_53bf8_cl_placed_ofEnv
            (PreEnv := PreEnv) (PostEnv := PostEnv)
            hc.toDecodeStateCalleeContractsClPlaced x st0 st curSt curEpoch s0 _ _ R post hpost
            (herr_of_none
              (mergeLoopBin_of_wt_none protoPrefixStep_chainEpochPB_mergeField hgt hdv hk hwt))
            (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
            (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
            (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
            (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
              lift_postEnv hpost_env
                (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
                  evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by
              dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
              pool_reg_norm
              try sep_ac_rfl)
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1884#64)
          wp_steps 6
          have hfold := after_decodeVarint2_to_epochErrFrame_placed H_inner A lim st x
            hcur_le hcur_suf hle1 curSt curEpoch s0 s1
          dsimp only [decodeStateLoopCommonPlaced] at hfold
          refine SepWP.fold hfold (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1])
          exact decodeState_err_epoch_invalid_wt_53bf8_cl_placed_ofEnv
            (PreEnv := PreEnv) (PostEnv := PostEnv)
            hc.toDecodeStateCalleeContractsClPlaced x st0 st curSt curEpoch s0 _ _ R post hpost
            (herr_of_none
              (mergeLoopBin_of_wt_none protoPrefixStep_chainEpochPB_mergeField hgt hdv hk hwt))
            (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
            (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
            (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
            (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
              lift_postEnv hpost_env
                (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
                  evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by
              dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
              pool_reg_norm
              try sep_ac_rfl)
      · have hand7 : key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := key_and7_of_wt_some hwt
        have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 iwt
        have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) := key_lsr3_32_eq hk
        have htag29 : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hk
        have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) = BitVec.ofNat 64 (key.toNat / 8) :=
          tag_zeroExtend64_ofNat32 htag29
        have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) = BitVec.ofNat 32 (key.toNat / 8) :=
          tag_setWidth32_ofNat (key.toNat / 8)
        by_cases htag0 : key.toNat / 8 < 1
        · have htag_eq0 : key.toNat / 8 = 0 := by omega
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1896#64)
          wp_steps 8
          have hfold := after_decodeVarint2_to_epochErrFrame_placed H_inner A lim st x
            hcur_le hcur_suf hle1 curSt curEpoch s0 s1
          dsimp only [decodeStateLoopCommonPlaced] at hfold
          refine SepWP.fold hfold (by sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1])
          exact decodeState_err_epoch_zero_tag_53c04_cl_placed_ofEnv
            (PreEnv := PreEnv) (PostEnv := PostEnv)
            hc.toDecodeStateCalleeContractsClPlaced x st0 st curSt curEpoch s0 _ _ R post hpost
            (herr_of_none
              (mergeLoopBin_of_tag_zero protoPrefixStep_chainEpochPB_mergeField hgt hdv hk hwt htag0))
            (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
            (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
            (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
            (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
              lift_postEnv hpost_env
                (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
                  evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by
              dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
              pool_reg_norm
              try sep_ac_rfl)
        · have hloop_step := mergeLoopBin_of_key_ok protoPrefixStep_chainEpochPB_mergeField
            (m := curEpoch) (depth' := 98) hgt hdv hk hwt htag0
          have hcbz64 := tag_cbz64_false (by omega : 1 ≤ key.toNat / 8) htag29
          have hcbz32 := tag_cbz32_false (by omega : 1 ≤ key.toNat / 8) htag29
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1036#64)
          wp_steps 8
          refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
            hcur_le hcur_suf hle1) (by sep_focus) ?_
          refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
            (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
            (st := curSt) hle1) (by sep_focus) ?_
          refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A.repAlloc)
            (a := s0.sp - 688#64) (rem1 := cur.length) (rem2 := rest1.length)
            (ep := curEpoch) hle1) (by sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1])
          refine decodeState_epoch_dispatch_538a8_cl_placed_ofEnv (v20 := v20)
            (PreEnv := PreEnv) (PostEnv := PostEnv)
            hc x st0 st evs_acc f rem curSt curEpoch rest1 limitEpoch (key.toNat / 8) iwt
            (by omega) htag29 hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [hloop_step]
              revert hnone
              rcases (curEpoch.mergeField (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt) rest1 98).toOption with _ | ⟨_, _⟩ <;>
                intro hnone <;> exact hnone))
            hacc hst hFit (by omega) (by omega)
            s0 _ _ R post hpost hpost_env hs0A
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3, hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, hand7, *])
            (by simp only [arm64_norm, hlsr3, hze, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl) ?_
          intro ep' rest2 evs_step sf P' hle2 hsuf2 hmf hacc_step hst_step hFit_step
          exact hnext ep' rest2 evs_step sf P'
            (Nat.lt_of_le_of_lt hle2 hlt1) (Nat.le_trans hle2 hrest1_le)
            (suffix_trans hrest1_le hrest1_suf hle2 hsuf2)
            (by rw [hloop_step, hmf])
            (hacc_step.mono_fuel (by omega))
            hst_step
            (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit_step)
  · intro s1 evs_dv hdv hevs_dv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hdv_iter : DecodeStateIterEnv x.st.bytes.length (2 * x.st.bytes.length + 16) evs_dv :=
      DecodeStateIterEnv.of_decodeVarint2 hevs_dv
    have hdv_loop : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_dv :=
      DecodeStateLoopEnv.single (fuel := 0) hdv_iter
    have hFit1 : FitsEnv M lim (M.stepEvents evs_dv st)
        (DecodeStateLoopEnv (rem - 1) x.st.bytes.length (2 * x.st.bytes.length + 16)) :=
      FitsEnv.decodeStateLoop_tail hdv_iter
        (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1916#64)
    wp_steps 1
    have hfold := after_decodeVarint2_err_to_epochErrFrame_placed H_inner A lim
      (M.stepEvents evs_dv st) x hcur_le hcur_suf curSt curEpoch s0 s1
    dsimp only [decodeStateLoopCommonPlaced] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_1]) (by simp only [arm64_norm, hrun1])
    exact decodeState_err_drop_epoch_53c18_cl_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc.toDecodeStateCalleeContractsClPlaced x st0 (M.stepEvents evs_dv st) curSt curEpoch
      0 (by decide) (s1.readReg64 (Reg.gpr 1#5)) s0 _ _ R post hpost
      (herr_of_none
        (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chainEpochPB_mergeField hgt hdv))
      (fitsEnv_epochDrop_push1_of_loop (by decide : 0 ≤ 4) (by omega) hFit1)
      (fitsEnv_epochDrop_push2_of_loop (by decide : 0 + 1 ≤ 4) (by omega) hFit1)
      (fun evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree =>
        lift_postEnv hpost_env
          (decodeStateEnv_of_loop_epochDrop_push2_free (by decide : 0 + 1 ≤ 4) (by omega)
            (hacc.append hdv_loop) (by rw [M.stepEvents_append, hst])
            evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree))
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
        pool_reg_norm
        try sep_ac_rfl)

theorem decodeState_epoch_body_53880_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (cur : List (BitVec 8)) (limitEpoch : Nat) (hgt : ¬ cur.length ≤ limitEpoch)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * cur.length + 8 ≤ rem)
    (hf : f + 4 * cur.length + 9 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_body : List AllocEvent)
        (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
        mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98 →
      DecodeStateLoopEnv (f + 4 * (cur.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_body) →
      M.stepEvents (evs_acc ++ evs_body) st0 = M.stepEvents evs_body st →
      FitsEnv M lim (M.stepEvents evs_body st)
        (DecodeStateLoopEnv (rem - 4 * (cur.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_body st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_body_53880_cl_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem curSt curEpoch cur limitEpoch hgt
    hcur_le hcur_suf hlen_bound herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hnext

theorem decodeState_epoch_body_53880_cl_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (cur : List (BitVec 8)) (limitEpoch : Nat) (hgt : ¬ cur.length ≤ limitEpoch)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * cur.length + 8 ≤ rem)
    (hf : f + 4 * cur.length + 9 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_body : List AllocEvent)
        (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
        mergeLoopBin ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2 limitEpoch 98 →
      DecodeStateLoopEnv (f + 4 * (cur.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_body) →
      M.stepEvents (evs_acc ++ evs_body) st0 = M.stepEvents evs_body st →
      FitsEnv M lim (M.stepEvents evs_body st)
        (DecodeStateLoopEnv (rem - 4 * (cur.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_body st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_body_53880_cl_placed
    (v20 := v20) hc x st0 st evs_acc f rem curSt curEpoch cur limitEpoch hgt
    hcur_le hcur_suf hlen_bound herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hnext

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopClPlacedBudgetAux
