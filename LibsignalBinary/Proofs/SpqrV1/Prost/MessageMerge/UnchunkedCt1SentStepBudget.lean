/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Step Lemmas for `Unchunked.Ct1Sent::merge` (Block `312`)

Re-exports `UnchunkedCt1SentStepBudgetAux` and proves `[LibsignalPlacement]` budget-threaded
per-field step lemmas (`skip`, `tag1`–`tag3`) for `Unchunked.Ct1Sent::merge` on Block `312`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl blkPC_312 blkPl_312)
open CryptoVerification.RustHeap
  (vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost IsDropSuffix SkipFieldGhost
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1
  (ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authenticatorPBCapAt setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro
   authenticatorPBAt_entails_optExists bv64_add_zero_u bv64_sub_zero_u
   cap_add_one_ne_zero_of_lt63 codecWireTypeToProto default_auth_cells_entails_cap
   iwt_cbnz_false_of_varint_u iwt_cbnz_true_of_ne_varint_u
   memRegion_40_split_5_cells memRegion_48_split_112 memRegion_48_wtErr112
   optProtoAuthenticatorCapAt optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt
   optProtoAuthenticatorCapAt_mono protoUnchunkedCt1SentCapAt protoUnchunkedCt1SentCapAt_mono
   proto_mergeMessage_suffix unchunkedMergeBelow unchunkedMergeBelow_bytesMerge3
   unchunkedMergeBelow_bytesMerge3_entails unchunkedMergeBelow_eq_authMergeStack
   unchunkedMergeBelow_err unchunkedMergeBelow_err_entails
   unchunkedMergeBelow_leaf unchunkedMergeBelow_leaf_entails
   vecU8CapAt vecU8CapAt_entails_vecU8_u vecU8CapAt_mono_u wtErr112_entails_memRegion40)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergePostEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (bytesMerge3RawSpec bytesMerge3RawSpecOfEnv bytesMerge3RawSpecOfEnv2)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (UnchunkedCt1SentMergeEnv decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse authMergeLoopEnv_to_spqr call_budget_lscro
   decodeErrorFromEnv_to_spqr decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_authMerge_of_spqr fitsEnv_decodeErrorFrom_of_spqr
   fitsEnv_decodeVarint2_of_spqr fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedCt1SentMergeOwnSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
  (ct1SentErrFrame ct1SentLoopPre ct1Sent_err0_ret_exit_placed
   ct1Sent_fields_entails_any ct1Sent_parts_entails_any ct1Sent_push_err_exit_cl_placed
   ct1Sent_tag1_push_exit_cl_placed fitsEnv_bytesMerge3_of_spqr
   bytesMergeEnv_to_spqr_err bytesMergeEnv_to_spqr_ok
   protoUnchunkedCt1SentCapAt_entails_any stackAt_decodeVarint2_raw_eq
   subroutine_ok_withLsCodeRoLoaded_of_plain unchunkedSavedRegs)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
  (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_312).base

theorem ct1Sent_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 (WireType.varint).toNat)
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
  have hcbnz := iwt_cbnz_false_of_varint_u
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_dv : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, restPtr, rest⟩
  have htag1_exit := @ct1Sent_tag1_push_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [ct1SentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim) (x := (x_dv, M.stepEvents evs st))
      (ret_pc := entry + 384#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hrest_lt,
        fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit⟩)
      (by dsimp only [sliceCursorAt, x_dv, restPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv hdv
      apply sepWPpLscro_of_vm (mid := entry + 552#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hdv,
          stackAt_decodeVarint2_raw_eq, memRegion_48_split_112 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        wp_focus_pure; intro hsm1
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr rest.length m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            memRegion (s0.sp - 104#64) 40 ∗
            unchunkedMergeBelow s0.sp ∗
            ct1SentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ct1SentErrFrame]; sep_entail)
        exact htag1_exit hFit hnone (by omega) hsm1 hsp_align
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
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hdv,
          stackAt_decodeVarint2_raw_eq, protoUnchunkedCt1SentCapAt,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.hdr hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.es hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x30#64) m.ct1 hrest'_le) (by sep_focus)
        apply SepWP.fold (optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x48#64) m.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) ≤ 4 * (x.bs.length - rest'.length))
            hevs (decodeVarint2Env_eq_nil_of_some hdv hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with epoch := v } x.bs rest')
          (by dsimp only [ct1SentLoopPre, protoUnchunkedCt1SentCapAt]; sep_entail)
        exact hcont v rest' _ hdv
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

theorem ct1Sent_tag1_varint_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 (WireType.varint).toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_tag1_varint_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_dv hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag2_call_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 300#64)
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
      (spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 s ∗
        vecU8CapAt A.repAlloc x.msgPtr rest.length m.hdr ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x78#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedSavedRegs s0.sp s0 ∗
        unchunkedMergeBelow s0.sp)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_am : AuthMergeGhost := ⟨iwt, x.msgPtr + 0x48#64, m.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpush_exit := @ct1Sent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_eq_authMergeStack s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := authMergeSpec A lim) (x := (x_am, M.stepEvents evs st))
      (ret_pc := entry + 312#64) hAuthCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [authMergeSpec, authMergeSpecOfEnv, x_am]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        fitsEnv_authMerge_of_spqr (errRem := 4) (byteRem := rest.length)
          (by omega) hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases ham : (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption with
    | none =>
      have hnone := hnone_of_am ham
      apply sepWPpLscro_of_vm (mid := entry + 612#64)
      by_vm_steps
        (conv => arg 4; simp only [authMergeSpec, authMergeSpecOfEnv, AuthMergePostEnv, x_am, ham,
          memRegion_48_split_112 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_am
        apply SepWP.exists_elim; intro m_auth'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_am
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp, ← unchunkedMergeBelow_eq_authMergeStack])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc x.msgPtr rest.length m.hdr) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1) (by sep_focus)
        apply SepWP.fold (authenticatorPBAt_entails_optExists A.repAlloc (x.msgPtr + 0x48#64) m_auth') (by sep_focus)
        apply SepWP.fold (ct1Sent_parts_entails_any A.repAlloc x.msgPtr m.hdr m.es m.ct1 m.epoch) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl ((4 * (x.bs.length - rest.length)) + (4 + 2 * rest.length)))
            hevs (authMergeLoopEnv_to_spqr hrest_le hevs_am))
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
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 104#64) 40 ∗
            unchunkedMergeBelow s0.sp ∗
            ct1SentErrFrame A lim st ((4 * (x.bs.length - rest.length)) + (4 + 2 * rest.length)) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ct1SentErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) hsm0 hn_err hsp_align
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
      have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix ham).1
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [authMergeSpec, authMergeSpecOfEnv, AuthMergePostEnv, x_am, ham,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_am
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_am
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp, ← unchunkedMergeBelow_eq_authMergeStack])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.hdr hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.es hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x30#64) m.ct1 hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) + (0 + 2 * (rest.length - rest'.length)) ≤
              4 * (x.bs.length - rest'.length))
            hevs (authMergeLoopEnv_to_spqr (by omega) hevs_am))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with auth := some v } x.bs rest')
          (by dsimp only [ct1SentLoopPre, protoUnchunkedCt1SentCapAt, optProtoAuthenticatorCapAt]; sep_entail)
        exact hcont v rest' _ ham
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

theorem ct1Sent_tag2_call_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 300#64)
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
      (spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 s ∗
        vecU8CapAt A.repAlloc x.msgPtr rest.length m.hdr ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x78#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedSavedRegs s0.sp s0 ∗
        unchunkedMergeBelow s0.sp)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_tag2_call_step_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) hAuthCall
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 276#64)
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
  have hcall := fun {s_c} => @ct1Sent_tag2_call_step_cl_placed _ M A lim H hPushCall hAuthCall
    x st R s0 s_c m rest iwt limit hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
  cases hauth : m.auth with
  | none =>
    have h80 : (x.msgPtr + 0x48#64) + 8#64 = x.msgPtr + 80#64 := by bv_lin
    have h88 : (x.msgPtr + 0x48#64) + 16#64 = x.msgPtr + 88#64 := by bv_lin
    have h96 : (x.msgPtr + 0x48#64) + 24#64 = x.msgPtr + 96#64 := by bv_lin
    have h104 : (x.msgPtr + 0x48#64) + 32#64 = x.msgPtr + 104#64 := by bv_lin
    have h112 : (x.msgPtr + 0x48#64) + 40#64 = x.msgPtr + 112#64 := by bv_lin
    have h72 : x.msgPtr + 0x48#64 = x.msgPtr + 72#64 := rfl
    have hdef_cap := default_auth_cells_entails_cap A.repAlloc (x.msgPtr + 0x48#64) rest.length
    rw [h80, h88, h96, h104, h112] at hdef_cap
    conv at hdef_cap => arg 1; rw [h72]
    apply sepWPpLscro_of_vm (mid := entry + 300#64)
    by_vm_steps
      (conv => arg 4; rw [ct1SentLoopPre, protoUnchunkedCt1SentCapAt, hauth,
        optProtoAuthenticatorCapAt, memRegion_40_split_5_cells (x.msgPtr + 0x48#64),
        h80, h88, h96, h104, h112, h72])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v5
      apply SepWP.exists_elim; intro v4
      apply SepWP.exists_elim; intro v3
      apply SepWP.exists_elim; intro v2
      apply SepWP.exists_elim; intro v1
      wp_steps
      apply SepWP.fold hdef_cap (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 _ ∗
          vecU8CapAt A.repAlloc x.msgPtr rest.length m.hdr ∗
          vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es ∗
          vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1 ∗
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) rest.length (m.auth.getD default) ∗
          ((x.msgPtr + 0x78#64) ↦₆₄ m.epoch) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 112#64) 48 ∗
          unchunkedSavedRegs s0.sp s0 ∗
          unchunkedMergeBelow s0.sp)
        (by simp only [hauth, Option.getD_none]; sep_entail)
      exact hcall
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx0])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by simp only [arm64_norm, wp_norm, hx20])
        (by simp only [arm64_norm, wp_norm, hx21])
        (by simp only [arm64_norm, wp_norm, hx22])
        (by simp only [arm64_norm, wp_norm, hx23])
        ⟨by simp only [arm64_norm, wp_norm, hx24],
         by simp only [arm64_norm, wp_norm, hx25],
         by simp only [arm64_norm, wp_norm, hx26],
         by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩
  | some auth0 =>
    apply sepWPpLscro_of_vm (mid := entry + 300#64)
    by_vm_steps
      (conv => arg 4; rw [ct1SentLoopPre, protoUnchunkedCt1SentCapAt, hauth,
        optProtoAuthenticatorCapAt, authenticatorPBCapAt])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro cap2
      apply SepWP.exists_elim; intro ptr2
      apply SepWP.exists_elim; intro cap1
      apply SepWP.exists_elim; intro ptr1
      (conv => arg 4; rw [vecU8At, vecHeader]; simp only [sepConj_assoc, arm64_norm])
      wp_focus_pure; rintro ⟨hcap1_ok, ⟨hcap1_len, hcap1_lt, hptr1_ne⟩, hcap2_ok⟩
      obtain ⟨hcmn1, hcmn2⟩ := cap_add_one_ne_zero_of_lt63 hcap1_lt
      wp_steps
      have hrepack :
          (((x.msgPtr + 72#64) ↦₆₄ cap1) ∗
            ((x.msgPtr + 80#64) ↦₆₄ ptr1) ∗
            ((x.msgPtr + 88#64) ↦₆₄ BitVec.ofNat 64 auth0.rootKey.length) ∗
            (if cap1 = 0 then emp else A.repAlloc.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ auth0.rootKey) ∗
              memRegion (ptr1 + BitVec.ofNat 64 auth0.rootKey.length) (cap1.toNat - auth0.rootKey.length))) ∗
            vecU8At A.repAlloc (x.msgPtr + 96#64) cap2 ptr2 auth0.macKey ⊢
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) rest.length auth0 := by
        unfold authenticatorPBCapAt
        refine sepConj_mono ?_ ?_
        · refine Entails.trans ?_ (Entails.sepExists_intro cap1)
          refine Entails.trans ?_ (Entails.sepExists_intro ptr1)
          unfold vecU8At vecHeader
          have h80 : (x.msgPtr + 0x48#64) + 8#64 = x.msgPtr + 80#64 := by bv_lin
          have h88 : (x.msgPtr + 0x48#64) + 16#64 = x.msgPtr + 88#64 := by bv_lin
          have h72 : x.msgPtr + 0x48#64 = x.msgPtr + 72#64 := rfl
          have hpure1 : auth0.rootKey.length ≤ cap1.toNat ∧ cap1.toNat < 2 ^ 63 ∧ ptr1 ≠ 0 :=
            ⟨hcap1_len, hcap1_lt, hptr1_ne⟩
          rw [h80, h88, h72]
          simp only [hcap1_ok, eq_true hpure1, pure_true, emp_sepConj, sepConj_assoc]
          exact Entails.refl _
        · refine Entails.trans ?_ (Entails.sepExists_intro cap2)
          refine Entails.trans ?_ (Entails.sepExists_intro ptr2)
          have h96 : (x.msgPtr + 0x48#64) + 0x18#64 = x.msgPtr + 96#64 := by bv_lin
          rw [h96]
          simp only [hcap2_ok, pure_true, emp_sepConj]
          exact Entails.refl _
      apply SepWP.fold hrepack (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 _ ∗
          vecU8CapAt A.repAlloc x.msgPtr rest.length m.hdr ∗
          vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es ∗
          vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1 ∗
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) rest.length (m.auth.getD default) ∗
          ((x.msgPtr + 0x78#64) ↦₆₄ m.epoch) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 112#64) 48 ∗
          unchunkedSavedRegs s0.sp s0 ∗
          unchunkedMergeBelow s0.sp)
        (by simp only [hauth, Option.getD_some]; sep_entail)
      exact hcall
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx0])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by simp only [arm64_norm, wp_norm, hx20])
        (by simp only [arm64_norm, wp_norm, hx21])
        (by simp only [arm64_norm, wp_norm, hx22])
        (by simp only [arm64_norm, wp_norm, hx23])
        ⟨by simp only [arm64_norm, wp_norm, hx24],
         by simp only [arm64_norm, wp_norm, hx25],
         by simp only [arm64_norm, wp_norm, hx26],
         by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem ct1Sent_tag2_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 276#64)
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
      (WppPanicFalse R) :=
  ct1Sent_tag2_step_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) hAuthCall
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag3_step_cl_placed [LibsignalPlacement]
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with hdr := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 324#64)
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
    (conv => arg 4; rw [vecU8CapAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap1
    apply SepWP.exists_elim; intro ptr1
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    wp_focus_pure; intro hcap1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr, cap1, ptr1, m.hdr, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (spec := bytesMerge3RawSpec A lim) (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 336#64) hBytesCall
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
        hcap1,
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
      apply sepWPpLscro_of_vm (mid := entry + 660#64)
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
      have hhdr : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.hdr ⊢ vecU8 A.repAlloc x.msgPtr m.hdr :=
        Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
      apply SepWP.fold hhdr (by sep_focus)
      apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es) (by sep_focus)
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
      refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply sepWPpLscro_of_vm (mid := entry + 712#64)
      by_vm_steps
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
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
        apply SepWP.exists_elim; intro cap1'
        apply SepWP.exists_elim; intro ptr1'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap1'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        have hhdr_cap : vecU8At A.repAlloc x.msgPtr cap1' ptr1' v ⊢ vecU8CapAt A.repAlloc x.msgPtr rest'.length v := by
          unfold vecU8CapAt
          refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
          exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
        apply SepWP.fold hhdr_cap (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.es hrest'_le) (by sep_focus)
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
            { m with hdr := v } x.bs rest')
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

theorem ct1Sent_tag3_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with hdr := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 324#64)
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
      (WppPanicFalse R) :=
  ct1Sent_tag3_step_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) hBytesCall
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_mb hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget
