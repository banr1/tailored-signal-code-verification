/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# SPQR V1: Budget-Threaded Loop & Top-Level Proof for `Chunked.Ct1Received::merge` (Block `303`)

Proves the budget-threaded `[LibsignalPlacement]` loop invariant and top-level contracts
`chunkedCt1Received_merge_cl_placed_ok_of_contracts` and
`chunkedCt1Received_merge_placed_ok_of_contracts` for `V1State.Chunked.Ct1Received::merge`
(Block `303`) against `withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix decodeVarint_suffix itag_beq_tag_false
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAt suffix_trans ule_len_of_ge ule_len_of_lt)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1ReceivedMergeGhost ChunkedLoopRegs SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedBelow chunkedBelow_leaf chunkedBelow_leaf_entails
   chunkedCt1ReceivedMerge_fnOff chunkedCt1ReceivedPBCapAt
   chunkedCt1ReceivedPBCapAt_entails_pb chunkedCt1ReceivedPBCapAt_mono
   chunkedCt1Received_mergeField_other chunkedCt1Received_mergeField_tag1
   chunkedCt1Received_mergeField_tag2
   chunkedMergeStack chunkedSavedRegs cmp_len_limit_of_eq cmp_len_limit_of_lt
   codecWireTypeToProto memRegion_48_split_128 memRegion_48_wtErr128
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_key_ok
   mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   optPolyEncoderPolysLen optPolyEncoderPtsLen
   optPolyEncoder_getD_default_polys_len optPolyEncoder_getD_default_pts_len
   polyEncoder_mergeMessage_pts_polys_len
   protoPrefixStep_chunked_ct1Received_mergeField proto_mergeMessage_suffix
   stackAt_chunkedMerge subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   withLscroProp wtErr128_entails_memRegion40
   wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_303 blkPl_303)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
  (ct1ReceivedErrFrame ct1ReceivedLoopPre
   ct1Received_decode_key_step_cl_placed ct1Received_from_err_exit_cl_placed
   ct1Received_ret_err_exit_placed ct1Received_skip_step_cl_placed
   stackAt_chunkedMerge_epilogue subroutine_ok_withLsCodeRoLoaded_of_bare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux2
  (ct1Received_tag1_step_cl_placed ct1Received_tag2_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1ReceivedMergeEnv ChunkedCt1ReceivedMergePostEnv
   SpqrMergeIterEnv SpqrMergeLoopEnv
   chunkedCt1ReceivedMergeSpec chunkedCt1ReceivedMergeSpecOfEnv
   ct1ReceivedPolyCapBound decodeErrorPushMergeBudgetSpec
   unchunkedEkSentCt1ReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   pool_spqr_mono sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim
   spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget (polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1ReceivedMerge_fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem pool_entails_spqrPoolAt_snoc0 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {maxLen polyBound : Nat}
    {evs : List AllocEvent} (h : SpqrMergeIterEnv maxLen polyBound evs) :
    A.pool lim (M.stepEvents evs st) s ⊢ spqrPoolAt A lim st 1 maxLen polyBound s :=
  pool_entails_spqrPoolAt_snoc (evs₁ := []) (evs₂ := evs) A lim st (VmPreserved.refl s)
    (Nat.le_refl 1) (SpqrMergeLoopEnv.nil (fuel := 0)) h

private theorem pool_entails_spqrPoolAt_nil0 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (f maxLen polyBound : Nat)
    {evs : List AllocEvent} (hnil : evs = []) :
    A.pool lim (M.stepEvents evs st) s ⊢ spqrPoolAt A lim st f maxLen polyBound s :=
  pool_entails_spqrPoolAt_nil (evs₁ := []) (evs₂ := evs) A lim st (VmPreserved.refl s)
    (Nat.zero_le f) (SpqrMergeLoopEnv.nil (fuel := 0)) hnil

private theorem pool_entails_spqrPoolAt_init {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (maxLen polyBound : Nat) :
    A.pool lim st s ⊢ spqrPoolAt A lim st 0 maxLen polyBound s := by
  simpa only [AllocCostModel.stepEvents, List.foldl] using
    pool_entails_spqrPoolAt_nil0 A lim st s 0 maxLen polyBound (evs := []) rfl

private theorem ct1_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChunkedCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.Ct1Received) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrMergeLoopEnv (6 * (x.bs.length - cur.length)) x.bs.length
      (ct1ReceivedPolyCapBound x) evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (chunkedCt1ReceivedMergeSpec A lim).post (x, st) s0 sf := by
  dsimp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv,
    ChunkedCt1ReceivedMergePostEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (pool_spqr_mono A lim st hvm (Nat.le_refl _) hevs)
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

/-! ## 1. Loop Exit, Loop Induction, and Top-Level Proofs (Block `303`) -/

section Placed

set_option quotPrecheck false in
local notation "blkBase" => (blkPl_303).base

theorem ct1Received_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.Ct1Received.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_303).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply sepWPpLscro_of_ret_vm
    by_vm_steps
      (conv => arg 4; rw [ct1ReceivedLoopPre, spqrPoolAt, chunkedSavedRegs,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        arm64_norm, hsp])
      apply SepWP.exists_elim; intro evs
      wp_focus_pure; intro hevs
      wp_steps
      apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
      have hcur_fold :
          (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗
            (x.ptr ↦ₛ x.bs.take (x.bs.length - cur.length)) ∗ (curPtr ↦ₛ cur) ⊢
          sliceCursorAfter x.slot x.ptr x.bs cur := by
        rw [sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
        exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
        by simp only [arm64_norm, wp_norm, hsp],
        by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
      refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (ct1_ok_exit_entails A lim st x s0 s _ m cur evs hsome hvm
          (by simp only [arm64_norm, wp_norm, htr])
          (by simp only [arm64_norm, wp_norm]) hevs)
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := fun {s_err : State} =>
      @ct1Received_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0 s_err m
    apply sepWPpLscro_of_vm (mid := blkBase + 108#64)
    by_vm_steps
      (conv => arg 4; rw [ct1ReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, memRegion_48_split_128 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.fold
        (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length))
        (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
          chunkedBelow s0.sp ∗
          ct1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
            (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
      exact hfrom_exit hFit hnone (by omega)
        (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26],
         by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem ct1Received_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.Ct1Received) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      optPolyEncoderPtsLen m.sendingEk + cur.length < 2 ^ 56 →
      optPolyEncoderPolysLen m.sendingEk + cur.length < 2 ^ 56 →
      Nat.max (optPolyEncoderPtsLen m.sendingEk) (optPolyEncoderPolysLen m.sendingEk) +
        cur.length ≤ ct1ReceivedPolyCapBound x →
      (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.Ct1Received.mergeField (cur.length - limit) m cur limit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_303).base + 192#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
        (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
          (ct1ReceivedPolyCapBound x))
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have htag1_step := fun {s m rest iwt} =>
    @ct1Received_tag1_step_cl_placed _ M A lim H hUcCall hPushCall x st R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} =>
    @ct1Received_tag2_step_cl_placed _ M A lim H hPolyCall hPushCall x st R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} =>
    @ct1Received_skip_step_cl_placed _ M A lim H hSkipCall x st R s0 s m rest iwt tag limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ _ _ hres_cur hpc hrun hsp htr _ _ hx21 hx22 hcs
    exact ct1Received_loop_le_exit_cl_placed hFromCall hFit (by omega) hsp_align
      hcur_le hcur_suf hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hpts hpolys hcap hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
    by_cases hle_lim : cur.length ≤ limit
    · exact ct1Received_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align
        hcur_le hcur_suf hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ct1Received_decode_key_step_cl_placed hFromCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr'
        hx0' hx1' hx19' hx20' hx21' hx22' hcs'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chunked_ct1Received_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [chunkedCt1Received_mergeField_tag1] at hloop_ok
        apply sepWPpLscro_of_vm (mid := blkBase + 312#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
          apply SepWPpLscro.weaken_pre
            (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
              (ct1ReceivedPolyCapBound x))
            (by dsimp only [ct1ReceivedLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
          have hnone_uc : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
              (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
              (mergeMessage V1State.Chunked.Ct1Received.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            intro huc; simp only [hres_cur, hloop_ok, huc, Option.map_none]
          refine htag1_step hFit hsp_align hrest_le hrest_lt hrest_suf hnone_uc
            (fun u' rest' s'' huc hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrun'])
            (by simp only [arm64_norm, wp_norm, hsp'])
            (by simp only [arm64_norm, wp_norm, htr'])
            (by simp only [arm64_norm, wp_norm, hx0'])
            (by simp only [arm64_norm, wp_norm, hx19'])
            (by simp only [arm64_norm, wp_norm, hx20'])
            (by simp only [arm64_norm, wp_norm, hx21'])
            (by simp only [arm64_norm, wp_norm, hx22'])
            ⟨by simp only [arm64_norm, wp_norm, hx23'],
             by simp only [arm64_norm, wp_norm, hx24'],
             by simp only [arm64_norm, wp_norm, hx25'],
             ⟨by simp only [arm64_norm, wp_norm, hx26'],
              by simp only [arm64_norm, wp_norm, hx27'],
              by simp only [arm64_norm, wp_norm, hx28'],
              by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
          have huf := proto_mergeMessage_suffix huc
          have hres_next : (mergeMessage V1State.Chunked.Ct1Received.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.Ct1Received.mergeField
                (rest'.length - limit) { m with uc := some u' } rest' limit 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, huc, Option.map_some]
          exact ih { m with uc := some u' } rest' s'' (by have := huf.1; omega)
            (by have := huf.1; omega) (suffix_trans hrest_le hrest_suf huf.1 huf.2)
            (by dsimp (config := { failIfUnchanged := false }) only; have := huf.1; omega)
            (by dsimp (config := { failIfUnchanged := false }) only; have := huf.1; omega)
            (by dsimp (config := { failIfUnchanged := false }) only; have := huf.1; omega)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [chunkedCt1Received_mergeField_tag2] at hloop_ok
          apply sepWPpLscro_of_vm (mid := blkBase + 260#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            apply SepWPpLscro.weaken_pre
              (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                (ct1ReceivedPolyCapBound x))
              (by dsimp only [ct1ReceivedLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
            have hnone_pe : (mergeMessage PolynomialEncoder.mergeField
                (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption = none →
                (mergeMessage V1State.Chunked.Ct1Received.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hpe; simp only [hres_cur, hloop_ok, hpe, Option.map_none]
            refine htag2_step hFit hsp_align hrest_le hrest_suf (by omega) (by omega) (by omega) hnone_pe
              (fun pe' rest' s'' hpe hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp'])
              (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              (by simp only [arm64_norm, wp_norm, hx19'])
              (by simp only [arm64_norm, wp_norm, hx20'])
              (by simp only [arm64_norm, wp_norm, hx21'])
              (by simp only [arm64_norm, wp_norm, hx22'])
              ⟨by simp only [arm64_norm, wp_norm, hx23'],
               by simp only [arm64_norm, wp_norm, hx24'],
               by simp only [arm64_norm, wp_norm, hx25'],
               ⟨by simp only [arm64_norm, wp_norm, hx26'],
                by simp only [arm64_norm, wp_norm, hx27'],
                by simp only [arm64_norm, wp_norm, hx28'],
                by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
            have hpf := proto_mergeMessage_suffix hpe
            obtain ⟨hpts_le, hpolys_le⟩ := polyEncoder_mergeMessage_pts_polys_len hpe
            have hpts_eq : (m.sendingEk.getD default).pts.length = optPolyEncoderPtsLen m.sendingEk :=
              optPolyEncoder_getD_default_pts_len m.sendingEk
            have hpolys_eq : (m.sendingEk.getD default).polys.length = optPolyEncoderPolysLen m.sendingEk :=
              optPolyEncoder_getD_default_polys_len m.sendingEk
            have hres_next : (mergeMessage V1State.Chunked.Ct1Received.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Received.mergeField
                  (rest'.length - limit) { m with sendingEk := some pe' } rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hpe, Option.map_some]
            have hcap_next :
                Nat.max (optPolyEncoderPtsLen (some pe')) (optPolyEncoderPolysLen (some pe')) +
                  rest'.length ≤ ct1ReceivedPolyCapBound x := by
              dsimp only [optPolyEncoderPtsLen, optPolyEncoderPolysLen]
              simp only [Nat.max_eq_max, Nat.max_def] at hcap ⊢
              split <;> split at hcap <;> omega
            exact ih { m with sendingEk := some pe' } rest' s'' (by have := hpf.1; omega)
              (by have := hpf.1; omega) (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
              (by dsimp (config := { failIfUnchanged := false }) only [optPolyEncoderPtsLen]; omega)
              (by dsimp (config := { failIfUnchanged := false }) only [optPolyEncoderPolysLen]; omega)
              hcap_next
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''
        · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
          obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by
            simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by
            simp only [bne, hb2_2, Bool.not_false]
          rw [chunkedCt1Received_mergeField_other m iwt rest 98 hitag_lt htag1 htag2] at hloop_ok
          apply sepWPpLscro_of_vm (mid := blkBase + 172#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            apply SepWPpLscro.weaken_pre
              (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                (ct1ReceivedPolyCapBound x))
              (by dsimp only [ct1ReceivedLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
            have hnone_sf : skipField (2 * rest.length + 2) 98 (key.toNat / 8) iwt rest = none →
                (mergeMessage V1State.Chunked.Ct1Received.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            refine hskip_step hFit hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp'])
              (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              (by simp only [arm64_norm, wp_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, wp_norm, hx19'])
              (by simp only [arm64_norm, wp_norm, hx20'])
              (by simp only [arm64_norm, wp_norm, hx21'])
              (by simp only [arm64_norm, wp_norm, hx22'])
              ⟨by simp only [arm64_norm, wp_norm, hx23'],
               by simp only [arm64_norm, wp_norm, hx24'],
               by simp only [arm64_norm, wp_norm, hx25'],
               ⟨by simp only [arm64_norm, wp_norm, hx26'],
                by simp only [arm64_norm, wp_norm, hx27'],
                by simp only [arm64_norm, wp_norm, hx28'],
                by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
            have hrest'_le_rest : rest'.length ≤ rest.length :=
              (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next : (mergeMessage V1State.Chunked.Ct1Received.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Received.mergeField
                  (rest'.length - limit) m rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest
                ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              (by omega) (by omega) (by omega)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''

theorem chunkedCt1Received_merge_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim))) :
    subroutine_ok ((blkPC_303).rebase (blkPl_303).base H)
      (blkPl_303).base (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedCt1ReceivedMergeSpec chunkedCt1ReceivedMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨hx0_wt, hx1_msg, hx2_buf, hpts_0, hpolys_0, hFit⟩
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have hcap_0 : Nat.max (optPolyEncoderPtsLen x.msg.sendingEk)
      (optPolyEncoderPolysLen x.msg.sendingEk) + x.bs.length ≤ ct1ReceivedPolyCapBound x :=
    Nat.le_refl _
  have hret_err := fun {s_err : State} =>
    @ct1Received_ret_err_exit_placed _ M A lim H x st R s0 s_err x.msg
  have hfrom_exit := fun {s_err : State} =>
    @ct1Received_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0 s_err x.msg
  have hloop := fun {limit : Nat} => @ct1Received_loop_ok_cl_placed _ M A lim H
    hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyCall x st R s0 limit
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64
        (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64
        (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    let x_dv0 : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩
    have hFit_loop : FitsEnv M lim st
        (SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1ReceivedPolyCapBound x)) := hFit
    have hfit_dv0 := fitsEnv_decodeVarint2_of_spqr (bs := x.bs) (f₀ := 0) (evs₀ := [])
      (by omega : 0 + 1 ≤ 6 * x.bs.length + 12) (SpqrMergeLoopEnv.nil (fuel := 0)) hFit_loop
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [stackAt_chunkedMerge s0.sp, chunkedBelow_leaf s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
      apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
      apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr
      apply SepWP.exists_elim; intro v_fp
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_dv0, st))
        (ret_pc := blkBase + 56#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm,
                stackAt_decodeVarint2_raw_eq])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx2_buf], hbs_lt,
          by simpa only [AllocCostModel.stepEvents, List.foldl] using hfit_dv0⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hx1_msg, hx2_buf]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint x.bs with
      | none =>
        have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Received_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := blkBase + 124#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
            stackAt_decodeVarint2_raw_eq,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          wp_focus_pure; intro hsm1
          (conv => arg 4; simp only [arm64_norm, wp_norm])
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg)
            (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_snoc0 A lim st sm (decodeVarint2Env_to_spqr hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
              memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
              ct1ReceivedErrFrame A lim st 1 (ct1ReceivedPolyCapBound x)
                s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
            (by dsimp only [ct1ReceivedErrFrame, chunkedSavedRegs]; sep_entail)
          exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      | some p =>
        rcases p with ⟨len, rest0⟩
        have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
        have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
        have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
        have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
        let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
        by_cases hlt_len : rest0.length < len.toNat
        · have hule := ule_len_of_lt hlt_len hrest0_lt
          have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Received_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by
                rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
              simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
          apply sepWPpLscro_of_vm (mid := blkBase + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
              stackAt_decodeVarint2_raw_eq, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, memRegion_48_split_128 s0.sp,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.exists_elim; intro evs_dv
            wp_focus_pure; intro hsm01
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_dv
            rcases hsm01 with ⟨hsm0, hsm1⟩
            (conv => arg 4; simp only [arm64_norm, wp_norm])
            apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg)
              (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm 0 x.bs.length (ct1ReceivedPolyCapBound x)
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold
              (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length))
              (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
                chunkedBelow s0.sp ∗
                ct1ReceivedErrFrame A lim st 0 (ct1ReceivedPolyCapBound x)
                  s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
              (by dsimp only [ct1ReceivedErrFrame, chunkedSavedRegs]; sep_entail)
            exact hfrom_exit hFit hnone (by omega)
              (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              (by simp only [arm64_norm, wp_norm])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hres0 : (mergeMessage V1State.Chunked.Ct1Received.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.Ct1Received.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0
                (rest0.length - len.toNat) 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Received_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by
                rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
              have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
                (conv_rhs => rw [hrest0_suf, List.drop_drop]); congr 1; omega
              simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true,
                ↓reduceIte, hdv0_p, Except.toOption, hlt_len, hdrop_eq]
              rcases mergeLoopBin V1State.Chunked.Ct1Received.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
          apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
              stackAt_decodeVarint2_raw_eq, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_dv
            wp_focus_pure; intro hsm01
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_dv
            rcases hsm01 with ⟨hsm0, hsm1⟩
            (conv => arg 4; simp only [arm64_norm, wp_norm])
            apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le)
              (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm (6 * (x.bs.length - rest0.length))
                x.bs.length (ct1ReceivedPolyCapBound x)
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            have hrest0_fold :
                (x.slot ↦₆₄ rest0Ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗
                  (x.ptr ↦ₛ x.bs.take (x.bs.length - rest0.length)) ∗ (rest0Ptr ↦ₛ rest0) ⊢
                sliceCursorAfter x.slot x.ptr x.bs rest0 := by
              rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
              exact Entails.of_eq (by sep_ac_rfl)
            apply SepWP.fold hrest0_fold (by dsimp only [rest0Ptr]; sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
                x.msg x.bs rest0 (ct1ReceivedPolyCapBound x))
              (by dsimp only [ct1ReceivedLoopPre, chunkedSavedRegs]; sep_entail)
            exact hloop hFit hsp_align hbs_lt hlim_lt rest0.length x.msg rest0 _
              (Nat.le_refl _) hrest0_le hrest0_suf (by omega) (by omega) (by omega) hres0
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hsm1, hsub])
              ⟨by simp only [arm64_norm, wp_norm],
               by simp only [arm64_norm, wp_norm],
               by simp only [arm64_norm, wp_norm],
               ⟨by simp only [arm64_norm, wp_norm, hx26_m],
                by simp only [arm64_norm, wp_norm, hx27_m],
                by simp only [arm64_norm, wp_norm, hx28_m],
                by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited hx0_wt hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64
        (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64
            (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) =
          BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64
        (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64
            (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
          BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Received_mergeField]
      unfold mergeMessageBin; cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    apply sepWPpLscro_of_vm (mid := blkBase + 108#64)
    by_vm_steps
      (conv => arg 4; rw [stackAt_chunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr128 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
      apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
      apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr
      apply SepWP.exists_elim; intro v_fp
      apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
      apply SepWP.exists_elim; intro v_wt0
      apply SepWP.fold
        (pool_entails_spqrPoolAt_init A lim st s0 x.bs.length (ct1ReceivedPolyCapBound x))
        (by sep_focus)
      wp_steps
      apply SepWP.fold (wtErr128_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold
        (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length))
        (by sep_focus)
      apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm, hx1_msg, hx2_buf], fun hvm => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ v_wt0) ∗ memRegion (s0.sp - 120#64) 40 ∗
          chunkedBelow s0.sp ∗
          ct1ReceivedErrFrame A lim st 0 (ct1ReceivedPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [ct1ReceivedErrFrame, chunkedSavedRegs]; sep_entail)
      exact hfrom_exit hFit hnone (by omega)
        (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm]⟩

theorem chunkedCt1Received_merge_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 263)
      (skipField3Spec A lim))
    (hUcCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim))) :
    subroutine_ok ((blkPC_303).rebase (blkPl_303).base H)
      (blkPl_303).base (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)) :=
  chunkedCt1Received_merge_cl_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_bare hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hSkipCall)
    hUcCall
    hPolyCall

alias chunkedCt1ReceivedMerge_cl_placed_ok_of_contracts :=
  chunkedCt1Received_merge_cl_placed_ok_of_contracts

alias chunkedCt1ReceivedMerge_placed_ok_of_contracts :=
  chunkedCt1Received_merge_placed_ok_of_contracts

alias chunked_ct1_received_merge_cl_placed_ok_of_contracts :=
  chunkedCt1Received_merge_cl_placed_ok_of_contracts

alias chunked_ct1_received_merge_placed_ok_of_contracts :=
  chunkedCt1Received_merge_placed_ok_of_contracts

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudget
