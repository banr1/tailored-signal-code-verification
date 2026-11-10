/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Field-Step Lemmas for `unchunked::EkSentCt1Received::merge` (Block `311`)

`RustCliAllocBudget`-threaded per-field step lemmas for tags 1–3 (`epoch`, `auth`, `dk`) of
`prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (Block `311`),
re-exporting exit, `skip_field`, and frame definitions from
`UnchunkedEkSentCt1ReceivedStepBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_311 blkPl_311 lsmpl)
open CryptoVerification.RustHeap
  (vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1
  (ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBAt)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authenticatorPBCapAt setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedEkSentCt1ReceivedMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro authenticatorPBAt_entails_optExists bv64_add_zero_u bv64_sub_zero_u
   cap_add_one_ne_zero_of_lt63 codecWireTypeToProto default_auth_cells_entails_cap
   ekSent_fields_entails_exists ekSent_parts_entails_exists memRegion_40_split_5_cells
   memRegion_48_split_112 mergeBytes_length optProtoAuthenticatorCapAt
   optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt optProtoAuthenticatorCapAt_mono
   protoUnchunkedEkSentCt1ReceivedCapAt protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists
   proto_mergeMessage_suffix unchunkedMergeBelow unchunkedMergeBelow_bytesMerge3
   unchunkedMergeBelow_bytesMerge3_entails unchunkedMergeBelow_eq_authMergeStack
   unchunkedMergeBelow_leaf unchunkedMergeBelow_leaf_entails vecU8CapAt vecU8CapAt_entails_vecU8_u
   vecU8CapAt_mono_u)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergeEnv AuthMergePostEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_bytesHead FitsEnv.spqrMergeLoop_split SpqrMergeLoopEnv
   UnchunkedEkSentCt1ReceivedMergeEnv decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse authMergeLoopEnv_to_spqr call_budget_lscro decodeVarint2Env_eq_nil_of_some
   decodeVarint2Env_to_spqr fitsEnv_authMerge_of_spqr fitsEnv_decodeVarint2_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedEkSentCt1ReceivedMergeOwnSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
  (ekSentErrFrame ekSentLoopPre ekSentSavedRegs ekSent_err0_ret_exit_placed
   ekSent_from_err_exit_cl_placed ekSent_from_err_exit_placed ekSent_push_err_exit_cl_placed
   ekSent_push_err_exit_placed ekSent_ret_err_exit_placed ekSent_skip_step_cl_placed
   ekSent_skip_step_placed ekSent_tag1_push_exit_cl_placed ekSent_tag1_push_exit_placed
   ekSent_tag1_wt_err_step_cl_placed ekSent_tag1_wt_err_step_placed
   stackAt_unchunkedMerge_epilogue subroutine_ok_withLsCodeRoLoaded_of_bare)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
  (ekSentErrFrame ekSentLoopPre ekSentSavedRegs ekSent_err0_ret_exit_placed
   ekSent_from_err_exit_cl_placed ekSent_from_err_exit_placed ekSent_push_err_exit_cl_placed
   ekSent_push_err_exit_placed ekSent_ret_err_exit_placed ekSent_skip_step_cl_placed
   ekSent_skip_step_placed ekSent_tag1_push_exit_cl_placed ekSent_tag1_push_exit_placed
   ekSent_tag1_wt_err_step_cl_placed ekSent_tag1_wt_err_step_placed
   stackAt_unchunkedMerge_epilogue subroutine_ok_withLsCodeRoLoaded_of_bare)

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

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_311).base

/-- Tag-1 (`epoch`) varint step from `+0x154` (`(blkPl_311).base + 340#64`) when `iwt = .varint`
(`X0 = 0#64`): calls `decodeVarint2Spec` (Block `291`). -/
theorem ekSent_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
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
  have htag1_push := @ekSent_tag1_push_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [ekSentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
      (ret_pc := entry + 352#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19,
            stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hrest_lt
        (fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit))
      (by sep_focus) ?_
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
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
          stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr rest.length m)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        refine SepWPpLscro.weaken_pre ?_
          (htag1_push (f := 4 * (x.bs.length - rest.length) + 1)
            hFit hnone hsm1 (by omega) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx24_m],
             by simp only [arm64_norm, wp_norm, hx25_m],
             by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
        dsimp only [ekSentErrFrame]; sep_entail
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
          protoUnchunkedEkSentCt1ReceivedCapAt, stackAt_decodeVarint2_raw_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.dk hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.ct1 hrest'_le) (by sep_focus)
        apply SepWP.fold (optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) m.auth hrest'_le)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) ≤ 4 * (x.bs.length - rest'.length))
            hevs (decodeVarint2Env_eq_nil_of_some hdv hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        refine SepWPpLscro.weaken_pre ?_
          (hcont v rest' _ hdv
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
        dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]
        simp only [arm64_norm]; sep_entail

theorem ekSent_tag1_varint_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
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
  ekSent_tag1_varint_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hVarintCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_dv hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

/-- Tag-2 (`auth`) call step from `+0x0fc` (`(blkPl_311).base + 252#64`): calls `authMergeSpec`
(Block `295`) on `m.auth.getD default` at `x.msgPtr + 0x30#64`. -/
theorem ekSent_tag2_call_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 252#64)
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
      (spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 s ∗
        vecU8CapAt A.repAlloc x.msgPtr rest.length m.dk ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x60#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        memRegion (s0.sp - 112#64) 48 ∗
        ekSentSavedRegs s0.sp s0 ∗
        unchunkedMergeBelow s0.sp)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_am : AuthMergeGhost := ⟨iwt, x.msgPtr + 0x30#64, m.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpush_exit := @ekSent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_eq_authMergeStack s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_am, M.stepEvents evs st))
      (ret_pc := entry + 264#64) hAuthCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [authMergeSpec, authMergeSpecOfEnv, AuthMergeEnv, x_am]
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
      apply sepWPpLscro_of_vm (mid := entry + 592#64)
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
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc x.msgPtr rest.length m.dk) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x18#64) rest.length m.ct1)
          (by sep_focus)
        apply SepWP.fold (authenticatorPBAt_entails_optExists A.repAlloc (x.msgPtr + 0x30#64) m_auth')
          (by sep_focus)
        apply SepWP.fold (ekSent_parts_entails_exists A.repAlloc x.msgPtr m.dk m.ct1 m.epoch)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + (4 + 2 * rest.length)))
            hevs (authMergeLoopEnv_to_spqr hrest_le hevs_am))
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
          (hpush_exit (n := n_err) (f := 4 * (x.bs.length - rest.length) + (4 + 2 * rest.length))
            hFit hnone hsm0 hn_err (by omega) hsp_align
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
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc x.msgPtr m.dk hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.ct1 hrest'_le) (by sep_focus)
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
        refine SepWPpLscro.weaken_pre ?_
          (hcont v rest' _ ham
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
        dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt,
          optProtoAuthenticatorCapAt]; sep_entail

theorem ekSent_tag2_call_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (authMergeSpec A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 252#64)
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
      (spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 s ∗
        vecU8CapAt A.repAlloc x.msgPtr rest.length m.dk ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x60#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        memRegion (s0.sp - 112#64) 48 ∗
        ekSentSavedRegs s0.sp s0 ∗
        unchunkedMergeBelow s0.sp)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_tag2_call_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hAuthCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

/-- Tag-2 (`auth`) step from `+0x0e4` (`(blkPl_311).base + 228#64`): initializes default
`ProtoAuthenticator` if `m.auth = none`, then delegates to `ekSent_tag2_call_step_cl_placed`. -/
theorem ekSent_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 228#64)
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
  have hcall := fun {s_c} => @ekSent_tag2_call_step_cl_placed _ M A lim H hPushCall hAuthCall
    x st R s0 s_c m rest iwt limit hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
  cases hauth : m.auth with
  | none =>
    have h56 : (x.msgPtr + 0x30#64) + 8#64 = x.msgPtr + 56#64 := by bv_lin
    have h64 : (x.msgPtr + 0x30#64) + 16#64 = x.msgPtr + 64#64 := by bv_lin
    have h72 : (x.msgPtr + 0x30#64) + 24#64 = x.msgPtr + 72#64 := by bv_lin
    have h80 : (x.msgPtr + 0x30#64) + 32#64 = x.msgPtr + 80#64 := by bv_lin
    have h88 : (x.msgPtr + 0x30#64) + 40#64 = x.msgPtr + 88#64 := by bv_lin
    have h48 : x.msgPtr + 0x30#64 = x.msgPtr + 48#64 := rfl
    have hdef_cap := default_auth_cells_entails_cap A.repAlloc (x.msgPtr + 0x30#64) rest.length
    rw [h56, h64, h72, h80, h88] at hdef_cap
    conv at hdef_cap => arg 1; rw [h48]
    apply sepWPpLscro_of_vm (mid := entry + 252#64)
    by_vm_steps
      (conv => arg 4; rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt, hauth,
        optProtoAuthenticatorCapAt, memRegion_40_split_5_cells (x.msgPtr + 0x30#64),
        h56, h64, h72, h80, h88, h48])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v5
      apply SepWP.exists_elim; intro v4
      apply SepWP.exists_elim; intro v3
      apply SepWP.exists_elim; intro v2
      apply SepWP.exists_elim; intro v1
      wp_steps
      apply SepWP.fold hdef_cap (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      refine SepWPpLscro.weaken_pre ?_
        (hcall
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
           by simp only [arm64_norm, wp_norm, hvregs]⟩)
      simp only [hauth, Option.getD_none]; sep_entail
  | some auth0 =>
    apply sepWPpLscro_of_vm (mid := entry + 252#64)
    by_vm_steps
      (conv => arg 4; rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt, hauth,
        optProtoAuthenticatorCapAt, authenticatorPBCapAt])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro cap2
      apply SepWP.exists_elim; intro ptr2
      apply SepWP.exists_elim; intro cap1
      apply SepWP.exists_elim; intro ptr1
      (conv => arg 4; rw [vecU8At, vecHeader])
      (conv => arg 4; simp only [sepConj_assoc])
      wp_focus_pure; intro hcap1_ok
      wp_focus_pure; rintro ⟨hcap1_len, hcap1_lt, hptr1_ne⟩
      wp_focus_pure; intro hcap2_ok
      (conv => arg 4; simp only [arm64_norm])
      obtain ⟨hcmn1, hcmn2⟩ := cap_add_one_ne_zero_of_lt63 hcap1_lt
      wp_steps
      have hrepack :
          (((x.msgPtr + 48#64) ↦₆₄ cap1) ∗
            ((x.msgPtr + 56#64) ↦₆₄ ptr1) ∗
            ((x.msgPtr + 64#64) ↦₆₄ BitVec.ofNat 64 auth0.rootKey.length) ∗
            (if cap1 = 0 then emp else A.repAlloc.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ auth0.rootKey) ∗
              memRegion (ptr1 + BitVec.ofNat 64 auth0.rootKey.length) (cap1.toNat - auth0.rootKey.length))) ∗
            vecU8At A.repAlloc (x.msgPtr + 72#64) cap2 ptr2 auth0.macKey ⊢
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length auth0 := by
        unfold authenticatorPBCapAt
        refine sepConj_mono ?_ ?_
        · refine Entails.trans ?_ (Entails.sepExists_intro cap1)
          refine Entails.trans ?_ (Entails.sepExists_intro ptr1)
          unfold vecU8At vecHeader
          have h56 : (x.msgPtr + 0x30#64) + 8#64 = x.msgPtr + 56#64 := by bv_lin
          have h64 : (x.msgPtr + 0x30#64) + 16#64 = x.msgPtr + 64#64 := by bv_lin
          have h48 : x.msgPtr + 0x30#64 = x.msgPtr + 48#64 := rfl
          have hpure1 : auth0.rootKey.length ≤ cap1.toNat ∧ cap1.toNat < 2 ^ 63 ∧ ptr1 ≠ 0 :=
            ⟨hcap1_len, hcap1_lt, hptr1_ne⟩
          rw [h56, h64, h48]
          simp only [hcap1_ok, eq_true hpure1, pure_true, emp_sepConj, sepConj_assoc]
          exact Entails.refl _
        · refine Entails.trans ?_ (Entails.sepExists_intro cap2)
          refine Entails.trans ?_ (Entails.sepExists_intro ptr2)
          have h72 : (x.msgPtr + 0x30#64) + 0x18#64 = x.msgPtr + 72#64 := by bv_lin
          rw [h72]
          simp only [hcap2_ok, pure_true, emp_sepConj]
          exact Entails.refl _
      apply SepWP.fold hrepack (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      refine SepWPpLscro.weaken_pre ?_
        (hcall
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
           by simp only [arm64_norm, wp_norm, hvregs]⟩)
      simp only [hauth, Option.getD_some]; sep_entail

theorem ekSent_tag2_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (authMergeSpec A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 228#64)
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
  ekSent_tag2_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hAuthCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

/-- Tag-3 (`dk`) bytes-merge step from `+0x174` (`(blkPl_311).base + 372#64`): calls
`bytesMerge3RawBudgetSpec` (Block `290`) on `m.dk` at `x.msgPtr`. -/
theorem ekSent_tag3_step_cl_placed [LibsignalPlacement]
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with dk := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 372#64)
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
    (conv => arg 4; rw [ekSentLoopPre, spqrPoolAt, protoUnchunkedEkSentCt1ReceivedCapAt,
      show vecU8CapAt A.repAlloc x.msgPtr rest.length m.dk =
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc x.msgPtr cap ptr m.dk) from rfl,
      sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap1
    apply SepWP.exists_elim; intro ptr1
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    wp_focus_pure; intro hcap1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr, cap1, ptr1, m.dk, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 384#64) hBytesCall
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
        hcap1,
        FitsEnv.spqrMergeLoop_bytesHead hrest_le (Nat.le_refl _)
          (FitsEnv.spqrMergeLoop_split (f₂ := max 1 (2 * rest.length)) hevs
            (hFit.mono fun _ (h : SpqrMergeLoopEnv _ _ _ _) => h.mono_fuel (by omega)))⟩)
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
      apply sepWPpLscro_of_vm (mid := entry + 628#64)
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
        have hdk : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.dk ⊢ vecU8 A.repAlloc x.msgPtr m.dk :=
          Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
        apply SepWP.fold hdk (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8_u A.repAlloc (x.msgPtr + 0x18#64) rest.length m.ct1)
          (by sep_focus)
        apply SepWP.fold
          (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A.repAlloc
            (x.msgPtr + 0x30#64) rest.length m.auth)
          (by sep_focus)
        apply SepWP.fold (ekSent_fields_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (.bytesMergeErr iwt cap1 rest hmb hevs_bm))
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
        apply SepWP.exists_elim; intro cap1'
        apply SepWP.exists_elim; intro ptr1'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap1'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        have hdk_cap : vecU8At A.repAlloc x.msgPtr cap1' ptr1' v ⊢
            vecU8CapAt A.repAlloc x.msgPtr rest'.length v := by
          unfold vecU8CapAt
          refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
          exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
        apply SepWP.fold hdk_cap (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) m.ct1 hrest'_le)
          (by sep_focus)
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

theorem ekSent_tag3_step_placed [LibsignalPlacement]
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with dk := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 372#64)
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
  ekSent_tag3_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hBytesCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_mb hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudget
