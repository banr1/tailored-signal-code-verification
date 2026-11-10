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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Merge Loop

Budget-threaded relocatable `[LibsignalPlacement]` proofs of the inductive `ChainEpochPB` merge loop
(`+984`) and length-delimited entry (`+600`), re-exporting dispatch and body helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (decodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (mergeLoopBin protoPrefixStep_chainEpochPB_mergeField)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred bv_len_sub_limit chainEpochPBCapOkAt
   chainEpochPBCapOkAt_eq_placed chainEpochPBCapOkAt_mono cmp_len_limit_bne_of_lt
   cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt decodeStatePlacedEntry
   decodeStatePlacedProg len_ult_of_ge len_ult_of_lt mergeLoopBin_eq_limit
   mergeLoopBin_lt_limit mergeMessage_toOption_of_decodeVarint_none
   mergeMessage_toOption_of_ge mergeMessage_toOption_of_lt optEpochDirectionPBCapOkAt
   protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned
   suffix_eq_drop_of_len_eq truncate32_zeroExtend64_lsr3)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_mono
   FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (fitsEnv_decodeErrorFrom_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   decodeStateEnv_of_loop_epochDrop_push2_free decodeStateEnv_of_loop_from_epochDrop_push2_free
   decodeState_err_drop_epoch_53c18_placed_ofEnv decodeState_err_epoch_corrupt_54038_placed_ofEnv
   decodeState_err_epoch_truncated_54028_placed_ofEnv fitsEnv_epochDrop_push1_of_loop
   fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced SepWPpIPlaced.call_decodeVarint2 decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
  (epochLoop_cursor_to_epochErrFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
  (after_decodeVarint2_err_to_epochErrFrame_placed decodeState_epoch_body_53880_placed_ofEnv
   decodeVarint2Env_eq_nil_of_some fitsEnv_decodeVarint2_of_loop
   fitsEnv_from_epochDrop_push1_of_loop fitsEnv_from_epochDrop_push2_of_loop lift_postEnv
   stepEvents_nil_of_acc)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
  (lift_postEnv stepEvents_nil_of_acc decodeVarint2Env_eq_nil_of_some
   fitsEnv_decodeVarint2_of_loop fitsEnv_from_epochDrop_push1_of_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
  (fitsEnv_from_epochDrop_push2_of_loop after_decodeVarint2_to_epochErrFrame_placed
   after_decodeVarint2_err_to_epochErrFrame_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
  (decodeState_epoch_dispatch_538a8_placed_ofEnv decodeState_epoch_dispatch_538a8_placed
   decodeState_epoch_dispatch_538a8_placed_loop)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudgetAux
  (decodeState_epoch_body_53880_placed_ofEnv decodeState_epoch_body_53880_placed
   decodeState_epoch_body_53880_placed_loop)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] truncate32_zeroExtend64_lsr3

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

/-! ## Full `ChainEpochPB` Merge Loop (`+984`) -/

/-- Envelope-parameterized inlined `ChainEpochPB` merge loop at `+984`, proved by induction on
`fuel`. -/
theorem decodeState_epoch_loop_53874_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ) (curSt : PqRatchetState)
    (limitEpoch : Nat) (hlim_bound : limitEpoch < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
      (curEpoch : ChainEpochPB) (cur : List (BitVec 8)) (s : State) (P : SepProp),
      cur.length - limitEpoch ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc →
      M.stepEvents evs_acc st0 = st →
      FitsEnv M lim st
        (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      4 * cur.length + 8 ≤ rem →
      f + 4 * cur.length + 9 ≤ 16 * x.st.bytes.length + 32 →
      s.pc = decodeStatePlacedEntry + 984#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → s.readReg64 .x28 = 1#64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (ep' : ChainEpochPB) (rest : List (BitVec 8)) (evs_loop : List AllocEvent)
          (sf : State) (P' : SepProp),
        mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
          some ep' →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limitEpoch →
        DecodeStateLoopEnv (f + 4 * (cur.length - rest.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16) (evs_acc ++ evs_loop) →
        M.stepEvents (evs_acc ++ evs_loop) st0 = M.stepEvents evs_loop st →
        FitsEnv M lim (M.stepEvents evs_loop st)
          (DecodeStateLoopEnv (rem - 4 * (cur.length - rest.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16)) →
        sf.pc = decodeStatePlacedEntry + 624#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
        sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
        sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
        sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length curSt ∗
          chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest.length ep' ∗
          memRegion (s0.sp - 576#64) 240 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st evs_acc f rem curEpoch cur s P hfuel hcur_le hcur_suf herr_of_none
      hacc hst hFit hrem hf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hle : cur.length ≤ limitEpoch := by omega
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := stepEvents_nil_of_acc hst
    subst hP
    dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc ⊢
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 624#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq]) (by simp only [arm64_norm, hrun])
      exact hdone curEpoch cur [] _ _
        (mergeLoopBin_eq_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 heq)
        hcur_le hcur_suf heq
        (by rw [List.append_nil]; exact hacc.mono_fuel (by omega))
        (by rw [List.append_nil, hst, hst_nil])
        (by rw [hst_nil]; exact FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29])
        (by rw [hst_nil]; dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl)
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
      have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2972#64)
      wp_steps 5
      refine SepWP.fold
        (epochLoop_cursor_to_epochErrFrame_placed H_inner A lim st x cur cur.length cur.length
          curSt curEpoch s0 s)
        (by dsimp only [sliceCursorAfter]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_corrupt_54038_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc.toDecodeStateCalleeContractsPlaced x st0 st curSt curEpoch s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_lt_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 hlt))
        (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
        (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
        (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
        (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
          lift_postEnv hpost_env
            (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
              evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx29])
        (by
          dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
          pool_reg_norm
          try sep_ac_rfl))
  | succ fuel ih =>
    intro st evs_acc f rem curEpoch cur s P hfuel hcur_le hcur_suf herr_of_none
      hacc hst hFit hrem hf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := stepEvents_nil_of_acc hst
    by_cases hle : cur.length ≤ limitEpoch
    · subst hP
      dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc ⊢
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 624#64)
        wp_steps 4
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq]) (by simp only [arm64_norm, hrun])
        exact hdone curEpoch cur [] _ _
          (mergeLoopBin_eq_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 heq)
          hcur_le hcur_suf heq
          (by rw [List.append_nil]; exact hacc.mono_fuel (by omega))
          (by rw [List.append_nil, hst, hst_nil])
          (by rw [hst_nil]; exact FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx29])
          (by rw [hst_nil]; dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl)
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
        have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2972#64)
        wp_steps 5
        refine SepWP.fold
          (epochLoop_cursor_to_epochErrFrame_placed H_inner A lim st x cur cur.length cur.length
            curSt curEpoch s0 s)
          (by dsimp only [sliceCursorAfter]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_corrupt_54038_placed_ofEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          hc.toDecodeStateCalleeContractsPlaced x st0 st curSt curEpoch s0 _ _ R post hpost
          (herr_of_none (mergeLoopBin_lt_limit ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 hlt))
          (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
          (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
          (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
          (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
            lift_postEnv hpost_env
              (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
                evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
          (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx29])
          (by
            dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
            pool_reg_norm
            try sep_ac_rfl))
    · have ⟨hult, hule⟩ := cmp_len_limit_of_gt hle (by omega)
      subst hP
      dsimp only [decodeStatePlacedEntry, decodeStatePlacedProg, sliceCursorAfter] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 996#64)
      wp_steps 3
      apply SepWP.done (by simp only [arm64_norm, hult, hule]) (by simp only [arm64_norm, hrun])
      refine decodeState_epoch_body_53880_placed_ofEnv (v20 := v20)
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc x st0 st evs_acc f rem curSt curEpoch cur limitEpoch
        hle hcur_le hcur_suf hlen_bound herr_of_none
        hacc hst hFit hrem hf s0 _ _ R post hpost hpost_env hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
        (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
        (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
        (by dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; pool_reg_norm; try sep_ac_rfl) ?_
      intro ep' rest2 evs_body sf P' hlt2 hle2 hsuf2 hmerge_eq hacc_body hst_body hFit_body
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
      refine ih (M.stepEvents evs_body st) (evs_acc ++ evs_body)
        (f + 4 * (cur.length - rest2.length)) (rem - 4 * (cur.length - rest2.length))
        ep' rest2 sf P' (by omega) hle2 hsuf2
        (fun hnone => herr_of_none (by rw [hmerge_eq, hnone]))
        hacc_body hst_body hFit_body (by omega) (by omega)
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP' ?_
      intro ep'' rest3 evs_tail sf' P'' hok hrest3_le hrest3_suf hrest3_eq
        hacc_tail hst_tail hFit_tail
      have hrest3_le2 : rest3.length ≤ rest2.length := by
        by_contra hgt
        have hlt_lim : rest2.length < limitEpoch := by omega
        rw [mergeLoopBin_lt_limit ChainEpochPB.mergeField (rest2.length - limitEpoch) ep' rest2
          limitEpoch 98 hlt_lim] at hok
        cases hok
      have hacc_comb :
          DecodeStateLoopEnv (f + 4 * (cur.length - rest3.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16) (evs_acc ++ (evs_body ++ evs_tail)) := by
        rw [← List.append_assoc]
        exact hacc_tail.mono_fuel (by omega)
      have hst_comb :
          M.stepEvents (evs_acc ++ (evs_body ++ evs_tail)) st0 =
            M.stepEvents (evs_body ++ evs_tail) st := by
        rw [← List.append_assoc, hst_tail, M.stepEvents_append]
      have hFit_comb :
          FitsEnv M lim (M.stepEvents (evs_body ++ evs_tail) st)
            (DecodeStateLoopEnv (rem - 4 * (cur.length - rest3.length)) x.st.bytes.length
              (2 * x.st.bytes.length + 16)) := by
        rw [M.stepEvents_append]
        exact FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit_tail
      intro hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26''
        hx28'' hx29'' hP''
      exact hdone ep'' rest3 (evs_body ++ evs_tail) sf' P''
        (by rw [hmerge_eq, hok]) hrest3_le hrest3_suf hrest3_eq
        hacc_comb hst_comb hFit_comb
        hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26''
        hx28'' hx29'' (by rw [M.stepEvents_append]; exact hP'')

theorem decodeState_epoch_loop_53874_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ) (curSt : PqRatchetState)
    (limitEpoch : Nat) (hlim_bound : limitEpoch < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
      (curEpoch : ChainEpochPB) (cur : List (BitVec 8)) (s : State) (P : SepProp),
      cur.length - limitEpoch ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc →
      M.stepEvents evs_acc st0 = st →
      FitsEnv M lim st
        (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      4 * cur.length + 8 ≤ rem →
      f + 4 * cur.length + 9 ≤ 16 * x.st.bytes.length + 32 →
      s.pc = decodeStatePlacedEntry + 984#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → s.readReg64 .x28 = 1#64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (ep' : ChainEpochPB) (rest : List (BitVec 8)) (evs_loop : List AllocEvent)
          (sf : State) (P' : SepProp),
        mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
          some ep' →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limitEpoch →
        DecodeStateLoopEnv (f + 4 * (cur.length - rest.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16) (evs_acc ++ evs_loop) →
        M.stepEvents (evs_acc ++ evs_loop) st0 = M.stepEvents evs_loop st →
        FitsEnv M lim (M.stepEvents evs_loop st)
          (DecodeStateLoopEnv (rem - 4 * (cur.length - rest.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16)) →
        sf.pc = decodeStatePlacedEntry + 624#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
        sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
        sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
        sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length curSt ∗
          chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest.length ep' ∗
          memRegion (s0.sp - 576#64) 240 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_loop_53874_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 curSt limitEpoch hlim_bound hlen_bound s0 R post hpost (fun _ h => h) hs0A

theorem decodeState_epoch_loop_53874_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ) (curSt : PqRatchetState)
    (limitEpoch : Nat) (hlim_bound : limitEpoch < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
      (curEpoch : ChainEpochPB) (cur : List (BitVec 8)) (s : State) (P : SepProp),
      cur.length - limitEpoch ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc →
      M.stepEvents evs_acc st0 = st →
      FitsEnv M lim st
        (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      4 * cur.length + 8 ≤ rem →
      f + 4 * cur.length + 9 ≤ 16 * x.st.bytes.length + 32 →
      s.pc = decodeStatePlacedEntry + 984#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch → s.readReg64 .x28 = 1#64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) cur.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (ep' : ChainEpochPB) (rest : List (BitVec 8)) (evs_loop : List AllocEvent)
          (sf : State) (P' : SepProp),
        mergeLoopBin ChainEpochPB.mergeField (cur.length - limitEpoch) curEpoch cur limitEpoch 98 =
          some ep' →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limitEpoch →
        DecodeStateLoopEnv (f + 4 * (cur.length - rest.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16) (evs_acc ++ evs_loop) →
        M.stepEvents (evs_acc ++ evs_loop) st0 = M.stepEvents evs_loop st →
        FitsEnv M lim (M.stepEvents evs_loop st)
          (DecodeStateLoopEnv (rem - 4 * (cur.length - rest.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16)) →
        sf.pc = decodeStatePlacedEntry + 624#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
        sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
        sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
        sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length curSt ∗
          chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest.length ep' ∗
          memRegion (s0.sp - 576#64) 240 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_loop_53874_placed
    (v20 := v20) hc x st0 curSt limitEpoch hlim_bound hlen_bound s0 R post hpost hs0A

/-! ## Delimited `ChainEpochPB::merge` Entry (`+600`) -/

private theorem epoch_scratch_split_recv_240 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      ∃∗ w_recv : BitVec 64,
        memRegion (sp - 680#64) 48 ∗
        ((sp - 632#64) ↦₆₄ w_recv) ∗
        memRegion (sp - 624#64) 48 ∗
        memRegion (sp - 576#64) 240 := by
  have hs1 := ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
    (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have hs2 := ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 288)
    (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have hs3 := ProofLib.memRegion_split' (b := sp - 624#64) (n := 48) (k := 240)
    (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  have hj := ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
    (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  rw [hs1, hs2, hs3, ProofLib.memRegion_eight (sp - 632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_recv
  refine Entails.sepExists_right w_recv ?_
  rw [hj]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem chainEpochPBCapOkAt_default_init (A : CryptoVerification.RustHeap.RustAlloc)
    (sp : BitVec 64) (remLen : Nat) :
    ((sp - 688#64) ↦₆₄ -1#64) ∗ memRegion (sp - 680#64) 48 ∗
      ((sp - 632#64) ↦₆₄ -1#64) ∗ memRegion (sp - 624#64) 48 ⊢
      chainEpochPBCapOkAt A (sp - 688#64) remLen default := by
  rw [show (default : ChainEpochPB) = { send := none, recv := none } from rfl,
    chainEpochPBCapOkAt_eq_placed]
  unfold optEpochDirectionPBCapOkAt
  dsimp only
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 632#64 + 8#64 = sp - 624#64 := by bv_omega
  have hnc : (-1#64 : BitVec 64) = noneCap := rfl
  rw [ha1, ha2, hnc]
  exact Entails.of_eq (by sep_ac_rfl)

attribute [local irreducible] mergeMessage mergeLoopBin
  CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

/-- Envelope-parameterized delimited `ChainEpochPB::merge` entry at `+600`, after `x0 = 2` has been
checked, reaching `+624` with the merged `ChainEpochPB` at `s0.sp - 688#64`. -/
theorem decodeState_epoch_merge_536f4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8))
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 4 ≤ rem)
    (hf : f + 4 * rest1.length + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_em : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption =
        some (ep', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_em) →
      M.stepEvents (evs_acc ++ evs_em) st0 = M.stepEvents evs_em st →
      FitsEnv M lim (M.stepEvents evs_em st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 624#64 →
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
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_em st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  refine SepWP.fold (epoch_scratch_split_recv_240 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (chainEpochPBCapOkAt_default_init A.repAlloc s0.sp rest1.length)
    (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2 hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 616#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := fitsEnv_decodeVarint2_of_loop (by omega) hFit)
    (hP := by pool_reg_norm; sep_focus) ?_ ?_
  · intro s1 len64 rest2 evs_dv hdv hevs_dv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_len
    have hdv_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv hevs_dv
    subst hdv_nil
    rw [stepEvents_nil_of_acc hst]
    have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
    have hrest2_le : rest2.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
    have hrest2_suf : IsDropSuffix x.st.bytes rest2 := suffix_trans hrest1_le hrest1_suf hle2 hsuf2
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_len hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hsp1A : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    by_cases hlt_len : rest2.length < len64.toNat
    · have ⟨hult, hule⟩ := len_ult_of_lt hlt_len
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2956#64)
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      dsimp only [sliceCursorAfter]
      wp_steps 5
      have hfold := epochLoop_cursor_to_epochErrFrame_placed H_inner A lim st x rest2
        rest1.length rest1.length curSt default s0 s1
      dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
        (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_truncated_54028_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc.toDecodeStateCalleeContractsPlaced x st0 st curSt default s0 _ _ R post hpost
        (herr_of_none (mergeMessage_toOption_of_lt ChainEpochPB.mergeField hdv hlt_len))
        (fitsEnv_decodeErrorFrom_of_loop (by omega) hFit)
        (fitsEnv_from_epochDrop_push1_of_loop (by omega) hFit)
        (fitsEnv_from_epochDrop_push2_of_loop (by omega) hFit)
        (fun evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree =>
          lift_postEnv hpost_env
            (decodeStateEnv_of_loop_from_epochDrop_push2_free (by omega) hacc hst
              evs_fr evs_d evs_p1 evs_p2 evs_f hfr hd hp1 hp2 hfree))
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by
          dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
          pool_reg_norm
          try sep_ac_rfl))
    · have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
      have hsub_lim := bv_len_sub_limit hlt_len
      have hmm_eq := mergeMessage_toOption_of_ge protoPrefixStep_chainEpochPB_mergeField
        (m := default) (depth' := 98) hdv hlt_len
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      dsimp only [sliceCursorAfter]
      wp_steps 4
      refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
        (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
        (st := curSt) hle2) (by sep_focus) ?_
      refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A.repAlloc)
        (a := s0.sp - 688#64) (rem1 := rest1.length) (rem2 := rest2.length)
        (ep := default) hle2) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
        (by simp only [arm64_norm, hrun1])
      refine decodeState_epoch_loop_53874_placed_ofEnv (v20 := v20)
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc x st0 curSt (rest2.length - len64.toNat) (by omega) hlen_bound
        s0 R post hpost hpost_env hs0A
        (rest2.length - (rest2.length - len64.toNat)) st evs_acc f rem default rest2 _ _
        (Nat.le_refl _) hrest2_le hrest2_suf
        (fun hnone => herr_of_none (by rw [hmm_eq, hnone]; rfl))
        hacc hst hFit (by omega) (by omega)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsub_lim, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by
          dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter]
          rw [hsp1048]
          pool_reg_norm
          try sep_ac_rfl) ?_
      intro ep' rest3 evs_loop sf P' hloop_ok hrest3_le hrest3_suf hrest3_eq
        hacc_loop hst_loop hFit_loop
      have hdrop : rest3 = rest2.drop len64.toNat :=
        suffix_eq_drop_of_len_eq hrest2_le hrest2_suf hlt_len hrest3_le hrest3_suf hrest3_eq
      have hle3_2 : rest3.length ≤ rest2.length := by omega
      have hle3_1 : rest3.length ≤ rest1.length := Nat.le_trans hle3_2 hle2
      have hsuf3_2 : IsDropSuffix rest2 rest3 := by
        unfold IsDropSuffix
        rw [hrest3_eq, Nat.sub_sub_self (Nat.not_lt.mp hlt_len)]
        exact hdrop
      have hsuf3_1 : IsDropSuffix rest1 rest3 :=
        suffix_trans hle2 hsuf2 hle3_2 hsuf3_2
      have hok_mm :
          (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption =
            some (ep', rest3) := by
        rw [hmm_eq, hloop_ok, ← hdrop]; rfl
      exact hdone ep' rest3 evs_loop sf P' hok_mm hle3_1 hsuf3_1
        (hacc_loop.mono_fuel (by omega))
        hst_loop
        (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit_loop)
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
    have hcbz : (s1.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_ne
    have hcbnz : (s1.readReg64 (Reg.gpr 1#5) != 0#64) = true := bne_iff_ne.mpr hx1_ne
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1916#64)
    wp_steps 2
    have hfold := after_decodeVarint2_err_to_epochErrFrame_placed H_inner A lim
      (M.stepEvents evs_dv st) x hrest1_le hrest1_suf curSt default s0 s1
    dsimp only [decodeStateLoopCommonPlaced] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_1, hcbz, hcbnz])
      (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_drop_epoch_53c18_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc.toDecodeStateCalleeContractsPlaced x st0 (M.stepEvents evs_dv st) curSt default
      0 (by decide) (s1.readReg64 (Reg.gpr 1#5)) s0 _ _ R post hpost
      (herr_of_none (mergeMessage_toOption_of_decodeVarint_none ChainEpochPB.mergeField hdv))
      (fitsEnv_epochDrop_push1_of_loop (by decide : 0 ≤ 4) (by omega) hFit1)
      (fitsEnv_epochDrop_push2_of_loop (by decide : 0 + 1 ≤ 4) (by omega) hFit1)
      (fun evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree =>
        lift_postEnv hpost_env
          (decodeStateEnv_of_loop_epochDrop_push2_free (by decide : 0 + 1 ≤ 4) (by omega)
            (hacc.append hdv_loop) (by rw [M.stepEvents_append, hst])
            evs_d evs_p1 evs_p2 evs_f hd hp1 hp2 hfree))
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_1, hcbz, hcbnz])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        dsimp only [decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
        pool_reg_norm
        try sep_ac_rfl))

theorem decodeState_epoch_merge_536f4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8))
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 4 ≤ rem)
    (hf : f + 4 * rest1.length + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_em : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption =
        some (ep', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_em) →
      M.stepEvents (evs_acc ++ evs_em) st0 = M.stepEvents evs_em st →
      FitsEnv M lim (M.stepEvents evs_em st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 624#64 →
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
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_em st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_merge_536f4_placed_ofEnv
    (v20 := v20) (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 curSt rest1 hrest1_le hrest1_suf hlen_bound herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29 hP hdone

theorem decodeState_epoch_merge_536f4_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8))
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 4 ≤ rem)
    (hf : f + 4 * rest1.length + 5 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (evs_em : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainEpochPB.mergeField .lengthDelimited default rest1 99).toOption =
        some (ep', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_em) →
      M.stepEvents (evs_acc ++ evs_em) st0 = M.stepEvents evs_em st →
      FitsEnv M lim (M.stepEvents evs_em st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 624#64 →
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
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_em st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_epoch_merge_536f4_placed
    (v20 := v20) hc x st0 st evs_acc f rem w0 curSt rest1 hrest1_le hrest1_suf hlen_bound
    herr_of_none hacc hst hFit hrem hf s0 s P R post hpost hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 hx29 hP hdone

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopPlacedBudget
