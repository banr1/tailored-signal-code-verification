/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Tag Arm 9 (`EkReceivedCt1Sampled`) for `V1State::merge` (Block `298`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` verification of tag arm 9
(`EkReceivedCt1Sampled`, `v1State_tag9_step_cl_placed`) with `withLsCl`-wrapped cross-block drop
callees (`286`, `271`, `267`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
  (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedEkReceivedCt1SampledMergeEnv ChunkedEkReceivedCt1SampledMergePostEnv
   chunkedEkReceivedCt1SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpecOfEnv
   ekReceivedCt1SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (optInnerStatePolyCapBound v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagEntryBudgetPlaced WppPanicFalse
   ekReceivedCt1SampledPolyCapBound_le
   optInnerStatePolyCapBound_ge_len optInnerStatePolyCapBound_of_ekReceivedCt1Sampled
   pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   tag_err_env_inplace tag_err_env_of_free tag_fitsEnv_sub
   tag_ok_env_inplace tag_ok_env_of_free wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
  (V1StateTagContClPlaced V1StateTagStepHypClPlaced)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudgetAux
  (v1Tag9_copy_err_1964_placed v1Tag9_copy_ok_1964_placed v1Tag9_discrFull_other
   v1Tag9_err_2028_cl_placed v1Tag9_post_drop_3204_cl_placed v1Tag9_pre_drop_3144_placed
   v1Tag9_setup_1944_placed)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt
   protoChunkedEkReceivedCt1SampledAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (InnerStateDiscrFull OptInnerStatePolyBound OptPolyEncoderBound
   SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
   V1StateMergeGhost WppPost
   bv64_add_zero bv64_sub_zero
   chunkedEkReceivedCt1SampledPBAt chunkedEkReceivedCt1SampledPBAt_eq_proto
   chunkedInlStack
   codecWireTypeToProto discrFull_none_add2 discrFull_some_add2
   ekReceivedCt1Sampled_polyBound_extract innerStatePolyBound_of_ekReceivedCt1Sampled
   optInnerStatePolyBound_lt_2_56 optPolyEncoderBound_none
   optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
   protoInnerStateCapAt proto_mergeMessage_len_le sepWP_seq_keep_lscl
   v1StateBelowRest v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1State_mergeField_tag9
   v1Tag9_capHeap v1Tag9_chunkedEkReceivedCt1SampledPBAt_entails_cap_zero
   v1Tag9_extract_words v1Tag9_memRegion_184_split_init
   v1Tag9_memRegion_fold_temp v1Tag9_memRegion_split_temp
   v1Tag9_reconstruct_innerState v1Tag9_words23At
   v1Tag9_words_entails_protoChunkedEkReceivedCt1Sampled)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## 1. Main Tag 9 Entry & Dispatch (`v1State_tag9_step_cl_placed`) -/

theorem v1Tag9_inplace_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {ek : V1State.Chunked.EkReceivedCt1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 748#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 9 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000008#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000008#64) = false := by rw [hx9_eq]; decide
  have hpe_bound : OptPolyEncoderBound ek.sendingCt1 rest.length := by
    simpa only [hm_is] using ekReceivedCt1Sampled_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hsub_cap : ekReceivedCt1SampledPolyCapBound
      ⟨iwt, x.msgPtr + 8#64, ek, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
    Nat.le_trans
      (by simpa only [hm_is] using
        ekReceivedCt1SampledPolyCapBound_le iwt (x.msgPtr + 8#64) x.bufRef x.slot restPtr rest m.innerState)
      hpoly_cap
  have hFit_sub : FitsEnv M lim st
      (ChunkedEkReceivedCt1SampledMergeEnv ⟨iwt, x.msgPtr + 8#64, ek, x.bufRef, x.slot, restPtr, rest⟩) :=
    tag_fitsEnv_sub hrest_le hsub_cap hFit
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 310) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps_sync_pool (lsmpl.base 310); wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, x.msgPtr + 8#64, ek, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 788#64) hEkCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by
      dsimp only [chunkedEkReceivedCt1SampledMergeSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv]
      simp only [arm64_norm, hsp, hx0]; rfl)
    (⟨rfl, rfl, rfl, hpe_bound, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound ek.sendingCt1 rest.length ∧
        FitsEnv M lim st
          (ChunkedEkReceivedCt1SampledMergeEnv ⟨iwt, x.msgPtr + 8#64, ek, x.bufRef, x.slot, restPtr, rest⟩))
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag9 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hek_res : (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) ek rest 99).toOption with
  | none =>
    rw [hek_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv,
        ChunkedEkReceivedCt1SampledMergePostEnv, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro ek'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0, hn_err⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000008#64) ∗
        chunkedEkReceivedCt1SampledPBAt A.repAlloc (x.msgPtr + 8#64) ek' ∗ memRegion (x.msgPtr + 192#64) 32 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is' := by
      rw [chunkedEkReceivedCt1SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr (some (.ekReceivedCt1Sampled ek'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs st) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; sep_ac_rfl))
    exact honErr hm_field evs _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (tag_err_env_inplace hrest_le hsub_cap hevs)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨ek', rest'⟩
    rw [hek_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hek_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekReceivedCt1Sampled ek')) :=
      innerStatePolyBound_of_ekReceivedCt1Sampled hpe_bound hek_res
    have hcap' : optInnerStatePolyCapBound (some (.ekReceivedCt1Sampled ek')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ekReceivedCt1Sampled hek_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv,
        ChunkedEkReceivedCt1SampledMergePostEnv, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents evs st) s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ekReceivedCt1Sampled ek') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; sep_ac_rfl))
    exact honOk evs { m with innerState := some (.ekReceivedCt1Sampled ek') } rest' _
      hm_field hpoly' hcap' hrest'_le
      (tag_ok_env_inplace hrest_le hsub_cap hevs)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1Tag9_at_1944_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1944#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 9 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩, _hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have hfsp240 : fsp + 240#64 = s0.sp - 576#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest.length :=
    optPolyEncoderBound_none h56
  have hsub_cap : ekReceivedCt1SampledPolyCapBound
      ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length := by
    have hge := optInnerStatePolyCapBound_ge_len x.msg.innerState x.bs.length
    change 0 + rest.length ≤ optInnerStatePolyCapBound x.msg.innerState x.bs.length
    omega
  have hFit_sub : FitsEnv M lim st
      (ChunkedEkReceivedCt1SampledMergeEnv ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩) :=
    tag_fitsEnv_sub hrest_le hsub_cap hFit
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 310) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag9_memRegion_split_temp fsp, v1Tag9_memRegion_184_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp424
  apply SepWP.exists_elim; intro w_sp144
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
      A.pool lim st s ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
        memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1Tag9_setup_1944_placed (A := A) (lim := lim) (st := st) (restLen := rest.length)
    hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 1964#64) hEkCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by
      dsimp only [chunkedEkReceivedCt1SampledMergeSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv]
      simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpe0, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest.length ∧
        FitsEnv M lim st
          (ChunkedEkReceivedCt1SampledMergeEnv ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩))
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 9) (codecWireTypeToProto iwt) rest 99).toOption =
      (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ekReceivedCt1Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag9]
    rcases h : m.innerState with _ | st_is
    · rfl
    · cases st_is with
      | ekReceivedCt1Sampled ek => exact absurd h (hm_not ek)
      | _ => rfl
  cases hek_res : (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hek_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv,
        ChunkedEkReceivedCt1SampledMergePostEnv, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro ek'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0, hn_err⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hek_words : chunkedEkReceivedCt1SampledPBAt A.repAlloc (fsp + 16#64) ek' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64,
        ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
        ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
          v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          v1Tag9_capHeap A.repAlloc 0 ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 :=
      Entails.trans (v1Tag9_chunkedEkReceivedCt1SampledPBAt_entails_cap_zero A.repAlloc (fsp + 16#64) ek')
        (v1Tag9_extract_words A.repAlloc (fsp + 16#64) 0 ek')
    apply SepWP.fold hek_words (by sep_focus)
    (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
    apply SepWP.exists_elim; intro w22
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    rw [← hfsp240] at hx25_m
    let Frame_err : SepProp :=
      v1Tag9_capHeap A.repAlloc 0 ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      stackAt fsp chunkedInlStack ∗
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
      memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; sep_ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag9_copy_err_1964_placed (A := A) (lim := lim) (st := M.stepEvents evs st)
      hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx21_2, hx25_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (v1Tag9_words_entails_protoChunkedEkReceivedCt1Sampled A.repAlloc (fsp + 240#64) ek'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedEkReceivedCt1SampledAt A.repAlloc (fsp + 240#64) ek' ∗
        A.pool lim (M.stepEvents evs st) s2 ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
          memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
          memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_err_2028_cl_placed hDropUc hDropEnc hcl2 hfsp_align hpc2 hrun2
      (hsp2.trans hspm) (hx25_2.trans hx25_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx21_3⟩
    rw [← stepEvents_append_eq evs evs_d st] at hP3
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs ++ evs_d) st) s0 s3 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; sep_ac_rfl))
    exact hcont.onErr hm_field (evs ++ evs_d) s3 (sm.readReg64 (Reg.gpr 0#5)) n_err
      (tag_err_env_of_free hrest_le hsub_cap hevs hevs_d)
      hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err hinv3
  | some p =>
    rcases p with ⟨ek', rest'⟩
    rw [hek_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hek_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekReceivedCt1Sampled ek')) :=
      innerStatePolyBound_of_ekReceivedCt1Sampled hpe0 hek_res
    have hcap' : optInnerStatePolyCapBound (some (.ekReceivedCt1Sampled ek')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ekReceivedCt1Sampled hek_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv,
        ChunkedEkReceivedCt1SampledMergePostEnv, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag9_extract_words A.repAlloc (fsp + 16#64) rest'.length ek') (by sep_focus)
    (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
    apply SepWP.exists_elim; intro w22
    rw [v1StateBelow_dropStack96 fsp]
    rw [← hfsp720] at hfp_m
    dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag9_capHeap A.repAlloc rest'.length ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        A.pool lim (M.stepEvents evs st) sm ∗
        (memRegion (fsp + 480#64) 184 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; sep_ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag9_copy_ok_1964_placed (A := A) (lim := lim) (st := M.stepEvents evs st)
      hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
        A.pool lim (M.stepEvents evs st) s2 ∗
        (memRegion (fsp + 480#64) 184 ∗ Frame_ok) =
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 480#64) 184 ∗ A.pool lim (M.stepEvents evs st) s2 ∗
        (memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1Tag9_pre_drop_3144_placed (A := A) (lim := lim) (st := M.stepEvents evs st)
      hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗ A.pool lim (M.stepEvents evs st) s3 ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        (memRegion (fsp + 16#64) 184 ∗ memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
          v1Tag9_capHeap A.repAlloc rest'.length ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
          memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_post_drop_3204_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    rw [← stepEvents_append_eq evs evs_d st] at hP4
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag9_reconstruct_innerState A.repAlloc x.msgPtr rest'.length ek'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents (evs ++ evs_d) st) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ekReceivedCt1Sampled ek') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; sep_ac_rfl))
    exact hcont.onOk (evs ++ evs_d) { m with innerState := some (.ekReceivedCt1Sampled ek') } rest' s4
      hm_field hpoly' hcap' hrest'_le
      (tag_ok_env_of_free hrest_le hsub_cap hevs hevs_d)
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
       hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
       hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans hfsp720⟩
      hinv4

private theorem v1Tag9_branch_1944_placed [LibsignalPlacement] {M : AllocCostModel}
    {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st : M.σ} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : State → SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 748#64)
    (hP_vm : ∀ {s1 s2}, VmPreserved s1 s2 → P s1 = P s2)
    (hcont : ∀ s' : State,
      V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1944#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' (P s') post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s (P s) post panic := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1944#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (hP_vm ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun _ => by simp only [arm64_norm],
        fun _ _ _ => by simp only [arm64_norm]⟩) ?_
    exact hcont _
      ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩,
       hpoly_cap, hFit⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ ek, is ≠ .ekReceivedCt1Sampled ek := fun ek h => hm_not ek (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000008#64) = true :=
      v1Tag9_discrFull_other hne hx9_s
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (hP_vm ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun _ => by simp only [arm64_norm],
        fun _ _ _ => by simp only [arm64_norm]⟩) ?_
    exact hcont _
      ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩,
       hpoly_cap, hFit⟩
      (by simp only [arm64_norm])

theorem v1State_tag9_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim))) :
    V1StateTagStepHypClPlaced A lim H 9 748#64 := by
  intro s0 s x st0 st R m rest iwt limit hentry hpc hcont
  by_cases hex : ∃ ek, m.innerState = some (.ekReceivedCt1Sampled ek)
  · rcases hex with ⟨ek, hm_is⟩
    exact v1Tag9_inplace_cl_placed hEkCall hm_is hentry hpc hcont
  · have hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek) := fun ek h => hex ⟨ek, h⟩
    refine v1Tag9_branch_1944_placed
      (P := fun s' => v1StateLoopPrePlaced A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      hm_not hentry hpc
      (fun hvm => by dsimp only [v1StateLoopPrePlaced]; rw [pool_eq_of_vmPreserved A lim st hvm])
      fun s' hentry' hpc' => ?_
    exact v1Tag9_at_1944_cl_placed hEkCall hDropUc hDropEnc hDropInner hm_not hentry' hpc' hcont

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlacedBudget
