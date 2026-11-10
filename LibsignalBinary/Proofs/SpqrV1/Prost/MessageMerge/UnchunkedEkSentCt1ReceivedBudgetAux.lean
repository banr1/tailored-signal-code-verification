/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Tag-4, Exit & Key-Decode Lemmas for `Unchunked.EkSentCt1Received::merge` (Block `311`)

Proves the budget-threaded tag-4 (`ct1`), loop-limit exit, and key-decode step lemmas (in both
`withLsCodeRoLoaded` and bare-callee `[LibsignalPlacement]` forms) for
`Unchunked.EkSentCt1Received::merge` on Block `311`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_311 blkPl_311 lsmpl)
open CryptoVerification.RustHeap
  (vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix bv32_zeroExtend_ofNat
   decodeVarint_suffix key_shr32_of_ge key_shr32_of_lt
   key_wt_none key_wt_some pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans
   tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (WppPost setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedEkSentCt1ReceivedMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro bv64_add_zero_u bv64_sub_zero_u cmp_len_limit_of_eq
   cmp_len_limit_of_gt cmp_len_limit_of_lt codecWireTypeToProto
   ekSent_fields_entails_exists memRegion_48_split2_112 memRegion_48_split_112 mergeBytes_length
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_decodeVarint_none
   mergeLoopBin_of_key_ge mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt optProtoAuthenticatorCapAt_mono
   pointsTo64_memRegion32_entails_40_112 protoPrefixStep_unchunked_ekSentCt1Received_mergeField
   protoUnchunkedEkSentCt1ReceivedCapAt protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists
   protoUnchunkedEkSentCt1ReceivedCapAt_mono
   unchunkedMergeBelow unchunkedMergeBelow_bytesMerge3 unchunkedMergeBelow_bytesMerge3_entails
   unchunkedMergeBelow_leaf unchunkedMergeBelow_leaf_entails unchunkedOwnStack vecU8CapAt
   vecU8CapAt_entails_vecU8_u vecU8CapAt_mono_u)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_bytesHead FitsEnv.spqrMergeLoop_split SpqrMergeLoopEnv
   UnchunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv
   decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil
   pool_entails_spqrPoolAt_snoc pool_spqr_mono sepWPpLscro_of_ret_vm sepWPpLscro_of_vm
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedEkSentCt1ReceivedMergeOwnSpec unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlacedBudget
  (ekSentErrFrame ekSentLoopPre ekSentSavedRegs ekSent_err0_ret_exit_placed
   ekSent_from_err_exit_cl_placed ekSent_push_err_exit_cl_placed
   stackAt_unchunkedMerge_epilogue subroutine_ok_withLsCodeRoLoaded_of_bare)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

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

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem ekSent_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : UnchunkedEkSentCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Unchunked.EkSentCt1Received) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrMergeLoopEnv (4 * (x.bs.length - cur.length)) x.bs.length 0 evs) :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim).post (x, st) s0 sf := by
  dsimp only [unchunkedEkSentCt1ReceivedMergeOwnSpec, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv,
    UnchunkedEkSentCt1ReceivedMergePostEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp unchunkedOwnStack ∗
          (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (pool_spqr_mono A lim st hvm (Nat.le_refl _) hevs)
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_311).base

/-- Tag-4 (`ct1`) step from `+0x124` (`(blkPl_311).base + 292#64`): calls `bytesMerge3RawBudgetSpec`
(Block `290`) on `x.msgPtr + 0x18#64`. -/
theorem ekSent_tag4_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 292#64)
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
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ekSent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [ekSentLoopPre, spqrPoolAt]; simp only [sepExists_sepConj_left, sepConj_assoc])
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    (conv => arg 4; rw [protoUnchunkedEkSentCt1ReceivedCapAt,
      show vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.ct1 =
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap ptr m.ct1) from rfl,
      sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap2
    apply SepWP.exists_elim; intro ptr2
    wp_focus_pure; intro hcap2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost :=
      ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.ct1, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 304#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap2,
        FitsEnv.spqrMergeLoop_bytesHead hrest_le (Nat.le_refl _)
          (FitsEnv.spqrMergeLoop_split (f₂ := max 1 (2 * rest.length)) hevs
            (hFit.mono fun _ (h : SpqrMergeLoopEnv _ _ _ _) => by
              unfold UnchunkedEkSentCt1ReceivedMergeEnv at hFit; exact h.mono_fuel (by omega)))⟩)
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
      apply sepWPpLscro_of_vm (mid := entry + 488#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
          memRegion_48_split_112 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_bm
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have hct1 : vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.ct1 ⊢
            vecU8 A.repAlloc (x.msgPtr + 0x18#64) m.ct1 :=
          Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
        apply SepWP.fold hct1 (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc x.msgPtr rest.length m.dk)
          (by sep_focus)
        apply SepWP.fold
          (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A.repAlloc
            (x.msgPtr + 0x30#64) rest.length m.auth)
          (by sep_focus)
        apply SepWP.fold (ekSent_fields_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (.bytesMergeErr iwt cap2 rest hmb hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 656#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        refine SepWPpLscro.weaken_pre ?_
          (hpush_exit (n := 0) (f := 4 * (x.bs.length - rest.length) + 1)
            hFit hnone hsm0 (Nat.zero_le 1) (by omega) hsp_align
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
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
        dsimp only [ekSentErrFrame]; sep_entail
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      have hv_len : rest'.length + v.length + 1 ≤ rest.length := mergeBytes_len_bound hmb
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
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
        have hct1_cap : vecU8At A.repAlloc (x.msgPtr + 24#64) cap2' ptr2' v ⊢
            vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest'.length v := by
          unfold vecU8CapAt
          refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
          exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
        apply SepWP.fold hct1_cap (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.dk hrest'_le) (by sep_focus)
        apply SepWP.fold
          (optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) m.auth hrest'_le)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) + (0 + 2 * v.length + 1) ≤
              4 * (x.bs.length - rest'.length))
            hevs
            (SpqrMergeLoopEnv.bytesSingle (fuel := 0) (maxLen := x.bs.length) (polyCapBound := 0)
              hmb hrest_le hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        refine SepWPpLscro.weaken_pre ?_
          (hcont v rest' _ hmb
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
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
        dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]; sep_entail

theorem ekSent_tag4_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (bytesMerge3RawBudgetSpec A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 292#64)
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
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_tag4_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hBytesCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_mb hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

/-- Loop-header exit at `+0x098` (`(blkPl_311).base + 152#64`) when `cur.length ≤ limit`. -/
theorem ekSent_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hle_lim : cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField
        (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply sepWPpLscro_of_ret_vm
    by_vm_steps
      (conv => arg 4; simp only [ekSentLoopPre, spqrPoolAt,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, ekSentSavedRegs,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        sepConj_pure_left_comm, arm64_norm, hsp])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (stackAt_unchunkedMerge_epilogue s0.sp s0)
        (by unfold ekSentSavedRegs; sep_focus)
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
        by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx24, hx25, hx26, hx27, hx28, hvregs]⟩
      refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (ekSent_ok_exit_entails A lim st x s0 s _ m cur evs hsome hvm
          (by simp only [arm64_norm, wp_norm, htr])
          (by simp only [arm64_norm, wp_norm]) hevs)
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ekSent_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0
    apply sepWPpLscro_of_vm (mid := entry + 108#64)
    by_vm_steps
      (conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, memRegion_48_split_112 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length))
        (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.fold
        (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr cur.length m)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      refine SepWPpLscro.weaken_pre ?_
        (hfrom_exit (w := 0x8000000000000008#64) (f := 4 * (x.bs.length - cur.length))
          hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrun])
          (by simp only [arm64_norm, wp_norm, hsp])
          (by simp only [arm64_norm, wp_norm, htr])
          ⟨by simp only [arm64_norm, wp_norm, hx24],
           by simp only [arm64_norm, wp_norm, hx25],
           by simp only [arm64_norm, wp_norm, hx26],
           by simp only [arm64_norm, wp_norm, hx27],
           by simp only [arm64_norm, wp_norm, hx28],
           by simp only [arm64_norm, wp_norm, hvregs]⟩)
      dsimp only [ekSentErrFrame]; sep_entail

theorem ekSent_loop_le_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hle_lim : cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField
        (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_loop_le_exit_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hFromCall)
    hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt hres_cur
    hpc hrun hsp htr hx21 hx22 hcs

/-- Loop-header key-decode step from `+0x098` (`(blkPl_311).base + 152#64`) when `¬ cur.length ≤ limit`. -/
theorem ekSent_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField
        (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) →
      ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt →
      ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_311).base + 204#64 →
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
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @ekSent_err0_ret_exit_placed _ M A lim H x st R s0
  have hfrom_exit := @ekSent_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [ekSentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 172#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm, hsp, hx19])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hcur_lt,
        fitsEnv_decodeVarint2_of_spqr (by unfold UnchunkedEkSentCt1ReceivedMergeEnv at hFit; omega)
          hevs hFit⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hd : decodeVarint cur with
    | none =>
      have hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur,
          mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ekSentCt1Received_mergeField
            hgt_lim hd,
          Option.map_none]
      apply sepWPpLscro_of_vm (mid := entry + 120#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
          stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold
          (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr cur.length m)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - cur.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        refine SepWPpLscro.weaken_pre ?_
          (herr0_exit (err := sm.readReg64 (Reg.gpr 1#5)) (f := 4 * (x.bs.length - cur.length) + 1)
            hnone (by omega) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            (by simp only [arm64_norm, wp_norm])
            hsm1
            ⟨by simp only [arm64_norm, wp_norm, hx24_m],
             by simp only [arm64_norm, wp_norm, hx25_m],
             by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
        dsimp only [ekSentErrFrame]; sep_entail
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur,
            mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ekSentCt1Received_mergeField
              hgt_lim hd hk_ge,
            Option.map_none]
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := entry + 108#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
            sepConj_assoc, arm64_norm, wp_norm, hsp])
          apply SepWP.exists_elim; intro evs_v
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (4 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
            memRegion_48_split2_112 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold
            (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr cur.length m)
            (by sep_focus)
          apply SepWP.fold
            (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
            (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp key) (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hfrom_exit (w := 0x8000000000000004#64) (f := 4 * (x.bs.length - cur.length))
              hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [ekSentErrFrame]; sep_entail
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur,
              mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ekSentCt1Received_mergeField
                hgt_lim hd hk_ge hwt,
              Option.map_none]
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := entry + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
              stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, wp_norm, hsp])
            apply SepWP.exists_elim; intro evs_v
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
            apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (4 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
              memRegion_48_split2_112 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps
            apply SepWP.fold
              (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr cur.length m)
              (by sep_focus)
            apply SepWP.fold
              (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
              (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp (key &&& 7#64))
              (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            refine SepWPpLscro.weaken_pre ?_
              (hfrom_exit (w := 0x8000000000000003#64) (f := 4 * (x.bs.length - cur.length))
                hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                ⟨by simp only [arm64_norm, wp_norm, hx24_m],
                 by simp only [arm64_norm, wp_norm, hx25_m],
                 by simp only [arm64_norm, wp_norm, hx26_m],
                 by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
            dsimp only [ekSentErrFrame]; sep_entail
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              rw [hres_cur,
                mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ekSentCt1Received_mergeField
                  hgt_lim hd hk_ge hwt hitag0,
                Option.map_none]
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := entry + 108#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
                stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_v
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
              apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (4 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
                (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
                memRegion_48_split_112 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold
                (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr cur.length m)
                (by sep_focus)
              apply SepWP.fold
                (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
                (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              refine SepWPpLscro.weaken_pre ?_
                (hfrom_exit (w := 0x8000000000000005#64) (f := 4 * (x.bs.length - cur.length))
                  hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
                  (by simp only [arm64_norm, wp_norm])
                  (by simp only [arm64_norm, wp_norm, hrunm])
                  (by simp only [arm64_norm, wp_norm, hspm])
                  (by simp only [arm64_norm, wp_norm, htrm, htr])
                  ⟨by simp only [arm64_norm, wp_norm, hx24_m],
                   by simp only [arm64_norm, wp_norm, hx25_m],
                   by simp only [arm64_norm, wp_norm, hx26_m],
                   by simp only [arm64_norm, wp_norm, hx27_m],
                   by simp only [arm64_norm, wp_norm, hx28_m],
                   by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
              dsimp only [ekSentErrFrame]; sep_entail
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
              rw [beq_eq_false_iff_ne]; intro h
              have h1 := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
              omega
            apply sepWPpLscro_of_vm (mid := entry + 204#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
                stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_v
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
              apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold
                (protoUnchunkedEkSentCt1ReceivedCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur)
                (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (by omega : 4 * (x.bs.length - cur.length) ≤ 4 * (x.bs.length - rest.length))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
                (by sep_focus)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              refine SepWPpLscro.weaken_pre ?_
                (hcont key iwt rest _ hd hk_ge hwt hitag0
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
                   by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
              dsimp only [ekSentLoopPre]; sep_entail

theorem ekSent_decode_key_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField
        (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) →
      ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt →
      ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_311).base + 204#64 →
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
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_decode_key_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hVarintCall)
    hFit hgt_lim hsp_align hcur_le hcur_lt hcur_suf hres_cur hcont
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudgetAux
