/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepClPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.Merge
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Budget Tag-4/5 & Key-Decode Lemmas for `Unchunked.Ct1Sent::merge` (Block `312`)

Proves the `withLsCodeRoLoaded lsmpl` budget-threaded tag-4 (`es`), tag-5 (`ct1`), loop-limit exit,
and key-decode step lemmas for `Unchunked.Ct1Sent::merge` on Block `312`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl blkPC_312 blkPl_312)
open CryptoVerification.RustHeap
  (vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost IsDropSuffix
   bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_ge key_shr32_of_lt
   key_wt_none key_wt_some pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1
  (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (WppPost setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro
   bv64_add_zero_u bv64_sub_zero_u
   cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt
   codecWireTypeToProto
   memRegion_48_split2_112 memRegion_48_split_112
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt optProtoAuthenticatorCapAt_mono
   pointsTo64_memRegion32_entails_40_112
   protoPrefixStep_unchunked_ct1Sent_mergeField
   protoUnchunkedCt1SentCapAt protoUnchunkedCt1SentCapAt_mono
   unchunkedMergeBelow unchunkedMergeBelow_bytesMerge3 unchunkedMergeBelow_bytesMerge3_entails
   unchunkedMergeBelow_leaf unchunkedMergeBelow_leaf_entails
   unchunkedOwnStack
   vecU8CapAt vecU8CapAt_entails_vecU8_u vecU8CapAt_mono_u)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (bytesMerge3RawSpec bytesMerge3RawSpecOfEnv bytesMerge3RawSpecOfEnv2)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeLoopEnv UnchunkedCt1SentMergeEnv UnchunkedCt1SentMergePostEnv
   decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro
   decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   pool_spqr_mono sepWPpLscro_of_ret_vm sepWPpLscro_of_vm
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedCt1SentMergeOwnSpec unchunkedCt1SentMergeOwnSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
  (bytesMergeEnv_to_spqr_err bytesMergeEnv_to_spqr_ok
   ct1SentErrFrame ct1SentLoopPre ct1Sent_err0_ret_exit_placed
   ct1Sent_fields_entails_any fitsEnv_bytesMerge3_of_spqr
   protoUnchunkedCt1SentCapAt_entails_any stackAt_decodeVarint2_raw_eq
   stackAt_unchunkedMerge_epilogue unchunkedSavedRegs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepClPlacedBudget
  (ct1Sent_from_err_exit_cl_placed ct1Sent_push_err_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u

private theorem ct1Sent_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : UnchunkedCt1SentMergeGhost)
    (s0 s sf : State) (m : V1State.Unchunked.Ct1Sent) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrMergeLoopEnv (4 * (x.bs.length - cur.length)) x.bs.length 0 evs) :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (unchunkedCt1SentMergeOwnSpec A lim).post (x, st) s0 sf := by
  dsimp only [unchunkedCt1SentMergeOwnSpec, unchunkedCt1SentMergeOwnSpecOfEnv,
    UnchunkedCt1SentMergePostEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (show
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp unchunkedOwnStack ∗
          (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))) by sep_ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono
    (pool_spqr_mono A lim st hvm (Nat.le_refl _) hevs)
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_312).base

theorem ct1Sent_tag4_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with es := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [ct1SentLoopPre, spqrPoolAt, protoUnchunkedCt1SentCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    (conv => arg 4; rw [show vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗
        vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap ptr m.es) from rfl])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap2
    apply SepWP.exists_elim; intro ptr2
    wp_focus_pure; intro hcap2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.es, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (spec := bytesMerge3RawSpec A lim) (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 360#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv, bytesMerge3RawSpecOfEnv2, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap2,
        fitsEnv_bytesMerge3_of_spqr (x_bm := x_bm) (by dsimp only [x_bm]; omega) hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes iwt rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply sepWPpLscro_of_vm (mid := entry + 684#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv,
          bytesMerge3RawSpecOfEnv2, x_bm, hmb, memRegion_48_split_112 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_bm
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have hes : vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.es ⊢ vecU8 A.repAlloc (x.msgPtr + 0x18#64) m.es :=
          Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
        apply SepWP.fold hes (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc x.msgPtr rest.length m.hdr) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1) (by sep_focus)
        apply SepWP.fold (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A.repAlloc (x.msgPtr + 0x48#64) rest.length m.auth) (by sep_focus)
        apply SepWP.fold (ct1Sent_fields_entails_any A.repAlloc x.msgPtr m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (bytesMergeEnv_to_spqr_err (x_bm := x_bm) hmb hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 712#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 104#64) 40 ∗
            unchunkedMergeBelow s0.sp ∗
            ct1SentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ct1SentErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) hsm0 (Nat.zero_le 1) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hlen_bound : rest'.length + v.length + 1 ≤ rest.length := mergeBytes_len_bound hmb
      have hrest'_le : rest'.length ≤ rest.length := by omega
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv,
          bytesMerge3RawSpecOfEnv2, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm
        apply SepWP.exists_elim; intro cap2'
        apply SepWP.exists_elim; intro ptr2'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap2'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        have hes_cap : vecU8At A.repAlloc (x.msgPtr + 24#64) cap2' ptr2' v ⊢ vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest'.length v := by
          unfold vecU8CapAt
          refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
          exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
        apply SepWP.fold hes_cap (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.hdr hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x30#64) m.ct1 hrest'_le) (by sep_focus)
        apply SepWP.fold (optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x48#64) m.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) + (2 * v.length + 1) ≤
              4 * (x.bs.length - rest'.length))
            hevs (bytesMergeEnv_to_spqr_ok (x_bm := x_bm) hmb hrest_le hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with es := v } x.bs rest')
          (by dsimp only [ct1SentLoopPre, protoUnchunkedCt1SentCapAt]; sep_entail)
        exact hcont v rest' _ hmb
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ct1Sent_tag5_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [ct1SentLoopPre, spqrPoolAt, protoUnchunkedCt1SentCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    (conv => arg 4; rw [show vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1 =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗
        vecU8At A.repAlloc (x.msgPtr + 0x30#64) cap ptr m.ct1) from rfl])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap3
    apply SepWP.exists_elim; intro ptr3
    wp_focus_pure; intro hcap3
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr + 0x30#64, cap3, ptr3, m.ct1, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (spec := bytesMerge3RawSpec A lim) (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 248#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv, bytesMerge3RawSpecOfEnv2, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap3,
        fitsEnv_bytesMerge3_of_spqr (x_bm := x_bm) (by dsimp only [x_bm]; omega) hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes iwt rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply sepWPpLscro_of_vm (mid := entry + 588#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv,
          bytesMerge3RawSpecOfEnv2, x_bm, hmb, memRegion_48_split_112 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_bm
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have hct1 : vecU8At A.repAlloc (x.msgPtr + 48#64) cap3 ptr3 m.ct1 ⊢ vecU8 A.repAlloc (x.msgPtr + 0x30#64) m.ct1 :=
          Entails.sepExists_right cap3 (Entails.sepExists_right ptr3 (Entails.refl _))
        apply SepWP.fold hct1 (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc x.msgPtr rest.length m.hdr) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es) (by sep_focus)
        apply SepWP.fold (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A.repAlloc (x.msgPtr + 0x48#64) rest.length m.auth) (by sep_focus)
        apply SepWP.fold (ct1Sent_fields_entails_any A.repAlloc x.msgPtr m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (bytesMergeEnv_to_spqr_err (x_bm := x_bm) hmb hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 712#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 104#64) 40 ∗
            unchunkedMergeBelow s0.sp ∗
            ct1SentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ct1SentErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) hsm0 (Nat.zero_le 1) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hlen_bound : rest'.length + v.length + 1 ≤ rest.length := mergeBytes_len_bound hmb
      have hrest'_le : rest'.length ≤ rest.length := by omega
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv,
          bytesMerge3RawSpecOfEnv2, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm
        apply SepWP.exists_elim; intro cap3'
        apply SepWP.exists_elim; intro ptr3'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap3'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        have hct1_cap : vecU8At A.repAlloc (x.msgPtr + 48#64) cap3' ptr3' v ⊢ vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest'.length v := by
          unfold vecU8CapAt
          refine Entails.trans (Entails.pure_right hcap3' (Entails.refl _)) ?_
          exact Entails.sepExists_right cap3' (Entails.sepExists_right ptr3' (Entails.refl _))
        apply SepWP.fold hct1_cap (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.hdr hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.es hrest'_le) (by sep_focus)
        apply SepWP.fold (optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x48#64) m.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) + (2 * v.length + 1) ≤
              4 * (x.bs.length - rest'.length))
            hevs (bytesMergeEnv_to_spqr_ok (x_bm := x_bm) hmb hrest_le hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with ct1 := v } x.bs rest')
          (by dsimp only [ct1SentLoopPre, protoUnchunkedCt1SentCapAt]; sep_entail)
        exact hcont v rest' _ hmb
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ct1Sent_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hle_lim : cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply sepWPpLscro_of_ret_vm
    by_vm_steps
      (conv => arg 4; simp only [ct1SentLoopPre, spqrPoolAt, unchunkedSavedRegs,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm,
        arm64_norm, hsp])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (stackAt_unchunkedMerge_epilogue s0.sp s0)
        (by unfold unchunkedSavedRegs; sep_focus)
      have hsca : (x.ptr ↦ₛ x.bs.take (x.bs.length - cur.length)) ∗
          ((x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗ (curPtr ↦ₛ cur)) ⊢
          sliceCursorAfter x.slot x.ptr x.bs cur :=
        Entails.of_eq (sliceCursorAfter_eq_split hcur_le hcur_suf).symm
      apply SepWP.fold hsca (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
        by simp only [arm64_norm, wp_norm, hsp],
        by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx24, hx25, hx26, hx27, hx28, hvregs]⟩
      refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (ct1Sent_ok_exit_entails A lim st x s0 s _ m cur evs hsome hvm
          (by simp only [arm64_norm, wp_norm, htr])
          (by simp only [arm64_norm, wp_norm]) hevs)
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ct1Sent_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0
    apply sepWPpLscro_of_vm (mid := entry + 108#64)
    by_vm_steps
      (conv => arg 4; rw [ct1SentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, memRegion_48_split_112 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr cur.length m) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000008#64) ∗
          memRegion (s0.sp - 104#64) 40 ∗
          unchunkedMergeBelow s0.sp ∗
          ct1SentErrFrame A lim st (4 * (x.bs.length - cur.length)) s0 _
            x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ct1SentErrFrame]; sep_entail)
      exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        ⟨by simp only [arm64_norm, wp_norm, hx24],
         by simp only [arm64_norm, wp_norm, hx25],
         by simp only [arm64_norm, wp_norm, hx26],
         by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem ct1Sent_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) →
      ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt →
      ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_312).base + 204#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  let x_dv : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, curPtr, cur⟩
  have herr0_exit := @ct1Sent_err0_ret_exit_placed _ M A lim H x st R s0
  have hfrom_exit := @ct1Sent_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [ct1SentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim) (x := (x_dv, M.stepEvents evs st))
      (ret_pc := entry + 172#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hcur_lt,
        fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit⟩)
      (by dsimp only [sliceCursorAt, x_dv, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hd : decodeVarint cur with
    | none =>
      have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ct1Sent_mergeField hgt_lim hd, Option.map_none]
      apply sepWPpLscro_of_vm (mid := entry + 120#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
          stackAt_decodeVarint2_raw_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        wp_focus_pure; intro hsm1
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr cur.length m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - cur.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            memRegion (s0.sp - 112#64) 48 ∗
            unchunkedMergeBelow s0.sp ∗
            ct1SentErrFrame A lim st (4 * (x.bs.length - cur.length) + 1) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ct1SentErrFrame]; sep_entail)
        exact herr0_exit hnone (by omega) (Nat.zero_le 2) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm]) hsm1
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ct1Sent_mergeField hgt_lim hd hk_ge, Option.map_none]
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := entry + 108#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
            stackAt_decodeVarint2_raw_eq,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_112 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (4 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr cur.length m) (by sep_focus)
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp key) (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000004#64) ∗
              memRegion (s0.sp - 104#64) 40 ∗
              unchunkedMergeBelow s0.sp ∗
              ct1SentErrFrame A lim st (4 * (x.bs.length - cur.length)) s0 _
                x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [ct1SentErrFrame]; sep_entail)
          exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            ⟨by simp only [arm64_norm, wp_norm, hx24_m],
             by simp only [arm64_norm, wp_norm, hx25_m],
             by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ct1Sent_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := entry + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
              stackAt_decodeVarint2_raw_eq,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_dv
            wp_focus_pure; rintro ⟨hsm0, hsm1⟩
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_dv
            (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
            apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_112 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (4 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr cur.length m) (by sep_focus)
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp (key &&& 7#64)) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000003#64) ∗
                memRegion (s0.sp - 104#64) 40 ∗
                unchunkedMergeBelow s0.sp ∗
                ct1SentErrFrame A lim st (4 * (x.bs.length - cur.length)) s0 _
                  x.msgPtr x.bufRef x.slot x.ptr x.bs)
              (by dsimp only [ct1SentErrFrame]; sep_entail)
            exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ct1Sent_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := entry + 108#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
                stackAt_decodeVarint2_raw_eq,
                sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro evs_dv
              wp_focus_pure; rintro ⟨hsm0, hsm1⟩
              wp_focus_pure; intro htrm
              wp_focus_pure; intro hevs_dv
              (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
              apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_112 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (4 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              wp_steps
              apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr cur.length m) (by sep_focus)
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000005#64) ∗
                  memRegion (s0.sp - 104#64) 40 ∗
                  unchunkedMergeBelow s0.sp ∗
                  ct1SentErrFrame A lim st (4 * (x.bs.length - cur.length)) s0 _
                    x.msgPtr x.bufRef x.slot x.ptr x.bs)
                (by dsimp only [ct1SentErrFrame]; sep_entail)
              exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                ⟨by simp only [arm64_norm, wp_norm, hx24_m],
                 by simp only [arm64_norm, wp_norm, hx25_m],
                 by simp only [arm64_norm, wp_norm, hx26_m],
                 by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
              rw [beq_eq_false_iff_ne]; intro h
              have h1 := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
              omega
            apply sepWPpLscro_of_vm (mid := entry + 204#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
                stackAt_decodeVarint2_raw_eq,
                sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro evs_dv
              wp_focus_pure; rintro ⟨hsm0, hsm1⟩
              wp_focus_pure; intro htrm
              wp_focus_pure; intro hevs_dv
              (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
              apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (protoUnchunkedCt1SentCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (by omega : 4 * (x.bs.length - cur.length) ≤ 4 * (x.bs.length - rest.length))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
                (by dsimp only [ct1SentLoopPre]; sep_entail)
              exact hcont key iwt rest _ hd hk_ge hwt hitag0
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
                (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
                (by simp only [arm64_norm, wp_norm, hx19_m])
                (by simp only [arm64_norm, wp_norm, hx20_m])
                (by simp only [arm64_norm, wp_norm, hx21_m])
                (by simp only [arm64_norm, wp_norm, hx22_m])
                (by simp only [arm64_norm, wp_norm, hx23_m])
                ⟨by simp only [arm64_norm, wp_norm, hx24_m],
                 by simp only [arm64_norm, wp_norm, hx25_m],
                 by simp only [arm64_norm, wp_norm, hx26_m],
                 by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudgetAux
