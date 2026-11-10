/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Inner `Unchunked.EkSent` Loop for `Chunked.HeaderSent::merge` (Block `302`)

Proves the budget-threaded `decode_varint`, `bytes::merge` (`tag = 3`), `skip_field`, and inner
`Unchunked.EkSent` loop induction (`chunkedHeaderSent_uc_loop_ok_cl_placed`) on Block `302`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix SkipFieldGhost bv32_zeroExtend_ofNat
   decodeVarint_suffix itag_beq_tag_false key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (WppPost mergeBytes_length mergeBytes_suffix
   optAuthenticatorPBCapAt optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt
   optAuthenticatorPBCapAt_mono setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3Stack)
open CryptoVerification.SpqrV1.ProtoRepr
  (chunkedHeaderSentPBAt ekSentPBAt optAuthenticatorPBAt optEkSentPBAt
   optPolynomialDecoderPBAt optPolynomialEncoderPBAt rustBytesVecAt unchunked3At)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderSentMergeGhost ChunkedInl10CalleeSaved SepWPpLscro
   blkPC_302 blkPl_302 bv64_add_zero bv64_sub_zero cells2_memRegion32_entails_40_160
   chunkedHeaderSentMerge_fnOff
   chunkedInlBelowStack chunkedInlBelow_bytesMerge3 chunkedInlBelow_bytesMerge3_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlBelow_skipField97 chunkedInlBelow_skipField97_entails
   cmp_len_limit_of_gt codecWireTypeToProto
   memRegion_48_cells1_160 memRegion_48_cells2_160
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   protoPrefixStep_unchunked_ekSent_mergeField proto_mergeMessage_suffix
   unchunked3CapAt unchunked3CapAt_entails_chunkedHeaderSentPBAt unchunked3CapAt_mono
   unchunkedEkSent_mergeField_other unchunkedEkSent_mergeField_tag1
   unchunkedEkSent_mergeField_tag2 unchunkedEkSent_mergeField_tag3
   vecU8At_entails_rustBytesVecAt)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack skipField3Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_bytesHead FitsEnv.spqrMergeLoop_split
   SpqrMergeIterEnv SpqrMergeLoopEnv decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderSentMergeEnv chunkedHeaderSentMergeSpec headerSentPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   decodeVarint2Env_to_spqr fitsEnv_decodeVarint2_of_spqr fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
  (chunkedHeaderSentErrFrame chunkedHeaderSentLoopPre chunkedHeaderSentUcLoopPre
   chunkedHeaderSent_uc_field_push_exit_placed
   chunkedHeaderSent_uc_from_push_exit_placed
   chunkedHeaderSent_uc_loop_le_exit_placed
   chunkedHeaderSent_uc_push_exit_placed
   chunkedHeaderSent_uc_tag1_wt_err_step_placed
   chunkedHeaderSent_uc_tag2_step_placed
   hsVecU8CapAt hsVecU8CapAt_mono unchunked3CapAt_eq vecU8At_entails_hsVecU8CapAt)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderSentMerge_fnOff

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_302).base

theorem chunkedHeaderSent_uc_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with epoch := v } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderSent_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderSentUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
      (ret_pc := entry + 616#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hrest_lt (fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit))
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
      apply sepWPpLscro_of_vm (mid := entry + 1068#64)
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
        stackAt_decodeVarint2_raw_eq,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
          (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
          hevs (decodeVarint2Env_to_spqr hevs_v))
        (by sep_focus)
      (conv => arg 4; rw [memRegion_48_cells1_160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply sepWPpLscro_of_vm (mid := entry + 1072#64)
      by_vm_steps
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm1 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
      apply sepWPpLscro_of_vm (mid := entry + 464#64)
      by_vm_steps
        (conv => arg 4; rw [unchunked3CapAt_eq]; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
          stackAt_decodeVarint2_raw_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (hsVecU8CapAt_mono A.repAlloc x.msgPtr uc.dk hrest'_le) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest'.length))
            hevs (decodeVarint2Env_eq_nil_of_some hdv hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc with epoch := v } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; simp only [arm64_norm, hsm1]; sep_entail)
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
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          uc sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 540#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩
  have hpush_exit := @chunkedHeaderSent_uc_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderSentUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField97 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 552#64) hSkipCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [skipField3Spec, x_sf]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx1],
        htag_lt,
        by simp only [arm64_norm, wp_norm, hx19],
        by simp only [arm64_norm, wp_norm],
        by decide,
        hrest_lt,
        fitsEnv_skipField_of_spqr (by omega) hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
    | none =>
      have hnone := hnone_of_sf hsf
      apply sepWPpLscro_of_vm (mid := entry + 792#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
            hevs (skipFieldEnv_to_spqr hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            memRegion (s0.sp - 128#64) 48 ∗
            chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some rest' =>
      have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
      apply sepWPpLscro_of_vm (mid := entry + 464#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_mono A.repAlloc x.msgPtr uc.epoch uc.auth uc.dk hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest'.length))
            hevs (skipFieldEnv_eq_nil_of_some hsf hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            uc sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentUcLoopPre]; sep_entail)
        exact hcont rest' _ hsf
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm]) (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m]) (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m]) (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m]) (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m]) (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with dk := v } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderSent_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq, hsVecU8CapAt,
      spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap1
    apply SepWP.exists_elim; intro ptr1
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    wp_focus_pure; intro hcap1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr, cap1, ptr1, uc.dk, x.bufRef, x.slot, restPtr, rest⟩
    have hFit_bm : FitsEnv M lim (M.stepEvents evs st) (BytesMerge3Env x_bm) :=
      FitsEnv.spqrMergeLoop_bytesHead (bs := rest) hrest_le (Nat.le_refl _)
        (FitsEnv.spqrMergeLoop_split (f₂ := max 1 (2 * rest.length)) hevs
          (hFit.mono fun _ h => h.mono_fuel (by omega)))
    refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 452#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawBudgetSpec, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap1,
        hFit_bm⟩)
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
      apply sepWPpLscro_of_vm (mid := entry + 976#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_rustBytesVecAt A.repAlloc x.msgPtr cap1 ptr1 uc.dk) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A.repAlloc (x.msgPtr + 0x18#64) rest.length uc.auth) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
            hevs (.bytesMergeErr iwt cap1 rest hmb hevs_bm))
          (by sep_focus)
        (conv => arg 4; rw [memRegion_48_cells1_160 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 1072#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt,
                optEkSentPBAt, ekSentPBAt, unchunked3At];
              simp only [arm64_norm]; sep_entail)
        exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
      have hlen_b : rest'.length + v.length + 1 ≤ rest.length := mergeBytes_len_bound hmb
      apply sepWPpLscro_of_vm (mid := entry + 464#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm
        apply SepWP.exists_elim; intro cap1'
        apply SepWP.exists_elim; intro ptr1'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap1'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_hsVecU8CapAt A.repAlloc x.msgPtr cap1' ptr1' rest'.length v hcap1') (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (f₃ := 6 * (x.bs.length - rest'.length)) (by omega)
            hevs (SpqrMergeLoopEnv.bytesSingle (fuel := 0) hmb hrest_le hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc with dk := v } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; simp only [arm64_norm]; sep_entail)
        exact hcont v rest' _ hmb
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm]) (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m]) (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m]) (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m]) (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m]) (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_302).base + 516#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs cur (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedHeaderSent_uc_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  have hfrom_push := @chunkedHeaderSent_uc_from_push_exit_placed _ M A lim H hFromCall hPushCall x st R s0
    { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderSentUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 484#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hd : decodeVarint cur with
    | none =>
      have hnone := hnone_of_uc_none
        (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd)
      apply sepWPpLscro_of_vm (mid := entry + 792#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
          stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - cur.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
            chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length) + 1)
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm1 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
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
      · have hnone := hnone_of_uc_none
          (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge)
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := entry + 780#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
            sepConj_assoc, arm64_norm, wp_norm, hsp])
          apply SepWP.exists_elim; intro evs_v
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (6 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
            rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
          apply SepWP.fold h40 (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗
              memRegion (s0.sp - 120#64) 40 ∗
              stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
              chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
                (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
            (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
          exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone := hnone_of_uc_none
            (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge hwt)
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := entry + 780#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
              stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, wp_norm, hsp])
            apply SepWP.exists_elim; intro evs_v
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (key.toNat % 8)) ∗ memRegion (s0.sp - 112#64) 32 ⊢
                memRegion (s0.sp - 120#64) 40 := by
              rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp _
            apply SepWP.fold h40 (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗
                memRegion (s0.sp - 120#64) 40 ∗
                stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
                  (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                  { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
              (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
            exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr])
              ⟨by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone := hnone_of_uc_none
              (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge hwt hitag0)
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := entry + 780#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
                stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_v
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (6 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
                (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗
                  memRegion (s0.sp - 120#64) 40 ∗
                  stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                  chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - cur.length))
                    (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                    { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
                (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
              exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                ⟨by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
              rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
            apply sepWPpLscro_of_vm (mid := entry + 516#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
                stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_v
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (unchunked3CapAt_mono A.repAlloc x.msgPtr uc.epoch uc.auth uc.dk hrest_le_cur) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (by omega : 6 * (x.bs.length - cur.length) ≤ 6 * (x.bs.length - rest.length))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
                (by sep_focus)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
                  uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
                (by dsimp only [chunkedHeaderSentUcLoopPre]; sep_entail)
              exact hcont key iwt rest _ hd hk_ge hwt hitag0
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm]) (by simp only [arm64_norm, wp_norm, htrm, htr])
                (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
                (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
                (by simp only [arm64_norm, wp_norm, hx19_m]) (by simp only [arm64_norm, wp_norm, hx20_m])
                (by simp only [arm64_norm, wp_norm, hx21_m]) (by simp only [arm64_norm, wp_norm, hx22_m])
                (by simp only [arm64_norm, wp_norm, hx23_m]) (by simp only [arm64_norm, wp_norm, hx24_m])
                (by simp only [arm64_norm, wp_norm, hx25_m]) (by simp only [arm64_norm, wp_norm, hx26_m])
                ⟨by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.EkSent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.EkSent) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_302).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
        s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
            { uc := some uc', sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs rest' (headerSentPolyCapBound x))
          (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) →
      (mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (mergeMessage V1State.Chunked.HeaderSent.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_302).base + 464#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
          uc sendingEk receivingCt1 x.bs cur (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have htag1_varint := fun {s uc rest} =>
    @chunkedHeaderSent_uc_tag1_varint_step_cl_placed _ M A lim H hPushCall hVarintCall x st R s0 s
      uc sendingEk receivingCt1 rest outerLimit innerLimit hFit
  have htag1_wt_err := fun {s uc rest iwt} =>
    @chunkedHeaderSent_uc_tag1_wt_err_step_placed _ M A lim H hFromCall hPushCall x st R s0 s
      uc sendingEk receivingCt1 rest iwt hFit
  have htag2_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderSent_uc_tag2_step_placed _ M A lim H hPushCall hAuthCall x st R s0 s
      uc sendingEk receivingCt1 rest iwt outerLimit innerLimit hFit
  have htag3_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderSent_uc_tag3_step_cl_placed _ M A lim H hPushCall hBytesCall x st R s0 s
      uc sendingEk receivingCt1 rest iwt outerLimit innerLimit hFit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) =>
    @chunkedHeaderSent_uc_skip_step_cl_placed _ M A lim H hPushCall hSkipCall x st R s0 s
      uc sendingEk receivingCt1 rest iwt tag outerLimit innerLimit hFit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedHeaderSent_uc_loop_le_exit_placed hFromCall hPushCall hFit (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
      (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedHeaderSent_uc_loop_le_exit_placed hFromCall hPushCall hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderSent_uc_decode_key_step_cl_placed hFromCall hPushCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_cont ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97)
        protoPrefixStep_unchunked_ekSent_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag1] at hstep
        by_cases hiwt : iwt = .varint
        · subst hiwt
          apply sepWPpLscro_of_vm (mid := entry + 604#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            rw [chunkedHeaderSentUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderSentUcLoopPre]
            refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf
              (fun hdv => hnone_cont (by simp [hstep, hdv]))
              (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
              (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
              (by simp only [arm64_norm, wp_norm, hx23']) (by simp only [arm64_norm, wp_norm, hx24'])
              (by simp only [arm64_norm, wp_norm, hx25']) (by simp only [arm64_norm, wp_norm, hx26'])
              ⟨by simp only [arm64_norm, wp_norm, hx27'],
               by simp only [arm64_norm, wp_norm, hx28'],
               by simp only [arm64_norm, wp_norm, hvregs']⟩
            have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
            have hrest'_le_r : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
            have hrest'_le : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le_r hrest_le
            have hrest'_suf : IsDropSuffix x.bs rest' := suffix_trans hrest_le hrest_suf hrest'_le_r (decodeVarint_suffix hdv)
            have hstep' : mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.EkSent.mergeField (rest'.length - innerLimit) { uc with epoch := v } rest' innerLimit 97 := by
              simp [hstep, hdv]
            exact ih { uc with epoch := v } rest' s'' (by omega) hrest'_le hrest'_suf
              (fun uc' rest'' s3 heq hle3 hsuf3 hml => hok_cont uc' rest'' s3 heq hle3 hsuf3 (hstep'.trans hml))
              (fun hml => hnone_cont (hstep'.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · have hnone := hnone_cont (by simp [hstep, hiwt])
          apply sepWPpLscro_of_vm (mid := entry + 604#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            rw [chunkedHeaderSentUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderSentUcLoopPre]
            exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf hnone
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              ⟨by simp only [arm64_norm, wp_norm, hx27'],
               by simp only [arm64_norm, wp_norm, hx28'],
               by simp only [arm64_norm, wp_norm, hvregs']⟩
      · obtain ⟨hb1_1, hb1_2⟩ := itag_beq_tag_false htag1 htag_lt (by decide)
        by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag2] at hstep
          apply sepWPpLscro_of_vm (mid := entry + 560#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            rw [chunkedHeaderSentUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderSentUcLoopPre]
            refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf
              (fun ha => hnone_cont (by simp [hstep, ha]))
              (fun auth' rest' s'' ha hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
              (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
              (by simp only [arm64_norm, wp_norm, hx23']) (by simp only [arm64_norm, wp_norm, hx24'])
              (by simp only [arm64_norm, wp_norm, hx25']) (by simp only [arm64_norm, wp_norm, hx26'])
              ⟨by simp only [arm64_norm, wp_norm, hx27'],
               by simp only [arm64_norm, wp_norm, hx28'],
               by simp only [arm64_norm, wp_norm, hvregs']⟩
            obtain ⟨hrest'_le_r, hrest'_suf_r⟩ := proto_mergeMessage_suffix ha
            have hrest'_le : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le_r hrest_le
            have hrest'_suf : IsDropSuffix x.bs rest' := suffix_trans hrest_le hrest_suf hrest'_le_r hrest'_suf_r
            have hstep' : mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.EkSent.mergeField (rest'.length - innerLimit) { uc with auth := some auth' } rest' innerLimit 97 := by
              simp [hstep, ha]
            exact ih { uc with auth := some auth' } rest' s'' (by omega) hrest'_le hrest'_suf
              (fun uc' rest'' s3 heq hle3 hsuf3 hml => hok_cont uc' rest'' s3 heq hle3 hsuf3 (hstep'.trans hml))
              (fun hml => hnone_cont (hstep'.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · obtain ⟨hb2_1, hb2_2⟩ := itag_beq_tag_false htag2 htag_lt (by decide)
          by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag3] at hstep
            apply sepWPpLscro_of_vm (mid := entry + 440#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
              rw [chunkedHeaderSentUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderSentUcLoopPre]
              refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf
                (fun hmb => hnone_cont (by simp [hstep, hmb]))
                (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0'])
                (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
                (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
                (by simp only [arm64_norm, wp_norm, hx23']) (by simp only [arm64_norm, wp_norm, hx24'])
                (by simp only [arm64_norm, wp_norm, hx25']) (by simp only [arm64_norm, wp_norm, hx26'])
                ⟨by simp only [arm64_norm, wp_norm, hx27'],
                 by simp only [arm64_norm, wp_norm, hx28'],
                 by simp only [arm64_norm, wp_norm, hvregs']⟩
              have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
              have hrest'_le_r : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
              have hrest'_le : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le_r hrest_le
              have hrest'_suf : IsDropSuffix x.bs rest' := suffix_trans hrest_le hrest_suf hrest'_le_r (mergeBytes_suffix hmb)
              have hstep' : mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                  mergeLoopBin V1State.Unchunked.EkSent.mergeField (rest'.length - innerLimit) { uc with dk := v } rest' innerLimit 97 := by
                simp [hstep, hmb]
              exact ih { uc with dk := v } rest' s'' (by omega) hrest'_le hrest'_suf
                (fun uc' rest'' s3 heq hle3 hsuf3 hml => hok_cont uc' rest'' s3 heq hle3 hsuf3 (hstep'.trans hml))
                (fun hml => hnone_cont (hstep'.trans hml))
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · obtain ⟨hb3_1, hb3_2⟩ := itag_beq_tag_false htag3 htag_lt (by decide)
            rw [unchunkedEkSent_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3] at hstep
            have hx1_32 := sf_truncate32_ofNat64 (key.toNat / 8)
            apply sepWPpLscro_of_vm (mid := entry + 540#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
              rw [chunkedHeaderSentUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderSentUcLoopPre]
              refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
                (fun hsf => hnone_cont (by simp [hstep, hsf]))
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx1', hx1_32])
                (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
                (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
                (by simp only [arm64_norm, wp_norm, hx23']) (by simp only [arm64_norm, wp_norm, hx24'])
                (by simp only [arm64_norm, wp_norm, hx25']) (by simp only [arm64_norm, wp_norm, hx26'])
                ⟨by simp only [arm64_norm, wp_norm, hx27'],
                 by simp only [arm64_norm, wp_norm, hx28'],
                 by simp only [arm64_norm, wp_norm, hvregs']⟩
              have hrest'_le_r : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
              have hrest'_le : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le_r hrest_le
              have hrest'_suf : IsDropSuffix x.bs rest' :=
                suffix_trans hrest_le hrest_suf hrest'_le_r ((skip_suffix _).1 _ _ _ _ _ hsf)
              have hstep' : mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                  mergeLoopBin V1State.Unchunked.EkSent.mergeField (rest'.length - innerLimit) uc rest' innerLimit 97 := by
                simp [hstep, hsf]
              exact ih uc rest' s'' (by omega) hrest'_le hrest'_suf
                (fun uc' rest'' s3 heq hle3 hsuf3 hml => hok_cont uc' rest'' s3 heq hle3 hsuf3 (hstep'.trans hml))
                (fun hml => hnone_cont (hstep'.trans hml))
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget
