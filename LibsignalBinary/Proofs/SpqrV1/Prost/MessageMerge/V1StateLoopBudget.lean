/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoop
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Outer Loop and Jump-Table Dispatch for `V1State::merge` (Block `298`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` key decode, `skip_field` arm, 11-way
jump-table dispatch, and outer loop induction for `V1State::merge`, re-exporting loop exits and
latch continuations from `V1StateLoopBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_head FitsEnv.spqrMergeLoop_mono SpqrMergeIterEnv SpqrMergeLoopEnv
   decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergePostEnv optInnerStatePolyCapBound optInnerStatePolyCapBound_mono_len
   v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
  (spqrIter_of_decodeErrorFrom v1Loop_err_ret_exit_placed v1Loop_from_err_exit_placed
   v1Loop_latch_cont_placed v1Loop_le_exit_placed v1Loop_ok_ret_exit_placed
   v1Loop_push_err_exit_placed)
export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
  (v1Loop_err_ret_exit_placed v1Loop_from_err_exit_placed v1Loop_ok_ret_exit_placed
   v1Loop_push_err_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
   pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
  (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open CryptoVerification (LibsignalPlacement lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix
   key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop
  (optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound SepWPp.call_frame_keep_lscro SepWPp.of_sepWP_lscro
   V1StateLoopRegsPlaced V1StateMergeGhost WppPost
   bv64_add_zero bv64_sub_zero chunkedInlStack
   cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt codecWireTypeToProto
   decodeErrorWith_le4_intro
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge
   mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   optInnerStatePolyBound_mono optProtoInnerStateAt_entails_exists
   optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_discrFull
   optProtoInnerStateCapAt_entails_pb optProtoInnerStateCapAt_mono
   protoPrefixStep_v1State_mergeField
   stackAt_v1StateMerge_epilogue
   v1Loop_discr_tail_entails_cap v1Loop_err1_join_720 v1Loop_err2_entails_memRegion40
   v1Loop_err48_join_720 v1Loop_memRegion_720_split_err1 v1Loop_memRegion_720_split_err2
   v1Loop_mergeField_suffix
   v1StateBelow_decodeError v1StateBelow_decodeError_entails
   v1StateBelow_decodeVarint2 v1StateBelow_decodeVarint2_entails
   v1StateBelow_skipField99 v1StateBelow_skipField99_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1State_mergeField_other)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

private theorem setWidth8_ofNat64_wt_v1 (wt : WireType) :
    (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

private theorem key_tag_gt_11 {key : BitVec 64} (h : 11 < key.toNat / 8) :
    (BitVec.ule 96#64 key) = true ∧ (BitVec.ult key 96#64) = false := by
  have hge : 96 ≤ key.toNat := by omega
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not]
  change 96 ≤ key.toNat ∧ ¬ key.toNat < 96
  omega

private theorem key_tag_le_11 {key : BitVec 64} (h : key.toNat / 8 ≤ 11) :
    (BitVec.ule 96#64 key) = false ∧ (BitVec.ult key 96#64) = true := by
  have hlt : key.toNat < 96 := by omega
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not]
  change ¬ 96 ≤ key.toNat ∧ key.toNat < 96
  omega

/-! ## 1. Allocator Event Envelope Combinators for `decode_varint` & `skip_field` -/

private theorem spqrIter_of_decodeVarint2 {maxLen polyCap : Nat} {bs : List (BitVec 8)}
    {evs : List AllocEvent} (h : DecodeVarint2Env bs evs) :
    SpqrMergeIterEnv maxLen polyCap evs := by
  dsimp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at h
  cases hd : decodeVarint bs <;> rw [hd] at h <;> subst h
  · exact .fromErr
  · exact .nil

private theorem decodeVarint2Env_eq_nil {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  simpa only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using h

private theorem spqrIter_of_skipField3 {maxLen polyCap : Nat} {xg : CryptoVerification.LibsignalTripleRatchet.Prost.SkipFieldGhost}
    {evs : List AllocEvent} (h : SkipField3Env xg evs) :
    SpqrMergeIterEnv maxLen polyCap evs := by
  dsimp only [SkipField3Env, SkipFieldEnv, skipFieldEventsCore] at h
  cases hs : skipField (2 * xg.bs.length + 2) xg.depth xg.tag xg.wt xg.bs <;> rw [hs] at h <;> subst h
  · exact .fromErr
  · exact .nil

private theorem skipField3Env_eq_nil {xg : CryptoVerification.LibsignalTripleRatchet.Prost.SkipFieldGhost}
    {rest' : List (BitVec 8)} {evs : List AllocEvent}
    (hs : skipField (2 * xg.bs.length + 2) xg.depth xg.tag xg.wt xg.bs = some rest')
    (h : SkipField3Env xg evs) :
    evs = [] := by
  simpa only [SkipField3Env, SkipFieldEnv, skipFieldEventsCore, hs] using h

/-! ## 2. Loop Header (`+216..+296`), `skip_field` Arm (`+192..+212`), and 11-Way Jump-Table Dispatch -/

/-- Loop header key decode at `+216..+268` when `¬ cur.length ≤ limit`. -/
theorem v1Loop_decode_key_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (decodeVarint2Spec A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_acc : List AllocEvent} {R : SepProp} {s0 s : State}
    {m : V1State} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hevs_acc : SpqrMergeLoopEnv (8 * (x.bs.length - cur.length)) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc)
    (hFit : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SpqrMergeLoopEnv (8 * cur.length + 16) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hnone_of_loop_none :
      mergeLoopBin V1State.mergeField (cur.length - limit) m cur limit 99 = none →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_298).base + 268#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = key →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8) →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hFit_dv : FitsEnv M lim (M.stepEvents evs_acc st0) (DecodeVarint2Env cur) :=
    FitsEnv.spqrMergeLoop_head (fuel := 8 * cur.length + 15) (fun _ => spqrIter_of_decodeVarint2) hFit
  have hFit_from : FitsEnv M lim (M.stepEvents evs_acc st0) DecodeErrorFromEnv :=
    FitsEnv.spqrMergeLoop_head (fuel := 8 * cur.length + 15) (fun _ => spqrIter_of_decodeErrorFrom) hFit
  have herr_ret := @v1Loop_err_ret_exit_placed _ M A lim H x st0
  have hfrom_err := @v1Loop_from_err_exit_placed _ M A lim H hFromCall x st0 evs_acc R s0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      v1StateBelow_decodeVarint2 (s0.sp - 816#64)]
    simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291); wp_reach; intro hinv_c
  refine SepWPp.call_frame_keep_lscro
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs_acc st0))
    (ret_pc := (blkPl_298).base + 236#64) hVarintCall hinv_c
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by conv_lhs => dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]; simp only [arm64_norm, hsp, hx19])
    (by exact ⟨hcur_lt, hFit_dv⟩)
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_v1State_mergeField hgt_lim hd)
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
    conv =>
      arg 4
      simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm_eq
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    simp only [arm64_norm] at hsm0
    replace hsm1 : sm.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by simpa only [arm64_norm] using hsm1
    conv => arg 4; simp only [arm64_norm, hsp]
    have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
    apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 128#64); wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
        stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs_acc ++ evs_dv) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; rw [← stepEvents_append_eq]; sep_ac_rfl))
    exact herr_ret hnone
      ((hevs_acc.append (SpqrMergeLoopEnv.single (fuel := 0) (spqrIter_of_decodeVarint2 hevs_dv))).mono_fuel (by omega))
      (by decide : 0 ≤ 4) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
      conv =>
        arg 4
        simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; rintro ⟨hsm0, hsm1⟩
      wp_focus_pure; intro htrm_eq
      wp_focus_pure; intro hevs_dv
      simp only [arm64_norm] at hsm0 hsm1
      conv => arg 4; simp only [arm64_norm, hsp]
      have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv; subst hevs_nil
      have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
      apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      conv =>
        arg 4
        rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, v1Loop_memRegion_720_split_err2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0
      apply SepWP.exists_elim; intro v_err1
      wp_steps_sync_pool ((blkPl_298).base + 112#64)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (v1Loop_err2_entails_memRegion40 s0.sp key) (by sep_focus)
      apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_err0) (by sep_focus)
      apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr cur.length m.innerState)
        (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre
        (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
      exact hfrom_err hnone (hevs_acc.mono_fuel (by omega)) hFit_from
        (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
        conv =>
          arg 4
          simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm_eq
        wp_focus_pure; intro hevs_dv
        simp only [arm64_norm] at hsm0 hsm1
        conv => arg 4; simp only [arm64_norm, hsp]
        have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv; subst hevs_nil
        have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
        apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv =>
          arg 4
          rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, v1Loop_memRegion_720_split_err2 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps_sync_pool ((blkPl_298).base + 112#64)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (v1Loop_err2_entails_memRegion40 s0.sp (key &&& 7#64)) (by sep_focus)
        apply SepWP.fold (v1Loop_err1_join_720 s0.sp v_err0) (by sep_focus)
        apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr cur.length m.innerState)
          (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre
          (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
            v1StateErrFramePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
        exact hfrom_err hnone (hevs_acc.mono_fuel (by omega)) hFit_from
          (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_v1State_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
          conv =>
            arg 4
            simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm_eq
          wp_focus_pure; intro hevs_dv
          simp only [arm64_norm] at hsm0 hsm1
          conv => arg 4; simp only [arm64_norm, hsp]
          have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv; subst hevs_nil
          have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
          apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr cur.length m.innerState)
            (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
          conv =>
            arg 4
            rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt]
            simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_298).base + 112#64)
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPp.weaken_pre
            (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
              v1StateErrFramePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
          exact hfrom_err hnone (hevs_acc.mono_fuel (by omega)) hFit_from
            (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 268#64) hinv_m ?_
          conv =>
            arg 4
            simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm_eq
          wp_focus_pure; intro hevs_dv
          simp only [arm64_norm] at hsm0 hsm1
          conv => arg 4; simp only [arm64_norm, hsp]
          have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv; subst hevs_nil
          have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
          apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (optProtoInnerStateCapAt_mono A.repAlloc x.msgPtr m.innerState hrest_le_cur) (by sep_focus)
          wp_steps_sync_pool ((blkPl_298).base + 268#64); wp_reach; intro hinv'
          apply SepWPp.weaken_pre
            (P' := v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1])
            (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
             by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hx29_m]⟩ hinv'

/-- Unknown-tag `skip_field` arm at `+192..+212`. -/
theorem v1Loop_skip_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (skipField3Spec A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_acc : List AllocEvent} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_lt_bs : rest.length < x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hevs_acc : SpqrMergeLoopEnv (8 * (x.bs.length - (rest.length + 1))) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc)
    (hFit_rest : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hnone_of_skip : skipField (2 * rest.length + 2) 99 tag iwt rest = none →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 99 tag iwt rest = some rest' →
      SpqrMergeLoopEnv (8 * (x.bs.length - rest'.length)) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc →
      FitsEnv M lim (M.stepEvents evs_acc st0)
        (SpqrMergeLoopEnv (8 * rest'.length + 16) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx8 : (s.readReg64 (Reg.gpr 8#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  have hrest_le : rest.length ≤ x.bs.length := Nat.le_of_lt hrest_lt_bs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hFit_sf : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SkipField3Env ⟨iwt, tag, 99, x.bufRef, x.slot, restPtr, rest⟩) :=
    FitsEnv.spqrMergeLoop_head (fuel := 8 * rest.length + 23) (fun _ => spqrIter_of_skipField3) hFit_rest
  have herr_ret := @v1Loop_err_ret_exit_placed _ M A lim H x st0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_le hrest_suf,
      v1StateBelow_skipField99 (s0.sp - 816#64)]
    simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263); wp_reach; intro hinv_c
  refine SepWPp.call_frame_keep_lscro
    (x := (⟨iwt, tag, 99, x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs_acc st0))
    (ret_pc := (blkPl_298).base + 208#64) hSkipCall hinv_c
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by conv_lhs => dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx8, hx19, setWidth8_ofNat64_wt_v1])
    (by exact ⟨htag_lt, hrest_lt, hFit_sf⟩)
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 99 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
    conv =>
      arg 4
      simp only [skipField3Spec, hsf,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm_eq
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    replace hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by simpa only [arm64_norm] using hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (v1StateBelow_skipField99_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 128#64); wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs_acc ++ evs_sf) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; rw [← stepEvents_append_eq]; sep_ac_rfl))
    exact herr_ret hnone
      ((hevs_acc.append (SpqrMergeLoopEnv.single (fuel := 0) (spqrIter_of_skipField3 hevs_sf))).mono_fuel (by omega))
      (by decide : 0 ≤ 4) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinv_m ?_
    conv =>
      arg 4
      simp only [skipField3Spec, hsf,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm_eq
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    simp only [arm64_norm] at hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hevs_nil := skipField3Env_eq_nil hsf hevs_sf; subst hevs_nil
    have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
    apply SepWP.fold (v1StateBelow_skipField99_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_mono A.repAlloc x.msgPtr m.innerState hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 216#64); wp_reach; intro hinv'
    apply SepWPp.weaken_pre
      (P' := v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
    exact hcont rest' _ hsf
      (hevs_acc.mono_fuel (by omega))
      (FitsEnv.spqrMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit_rest)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
       by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hx29_m]⟩ hinv'

meta section
open Lean Meta Elab Tactic in
elab "wp_steps_sync_pool_target" : tactic => do
  let g ← getMainGoal
  let midStx ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    Lean.Elab.Term.exprToSyntax (ty.getArg! 1)
  evalTactic (← `(tactic| wp_steps_sync_pool $midStx))
end

set_option maxHeartbeats 1600000 in
/-- Jump-table dispatch at `+268..+296` for known tags `1..11`. -/
theorem v1Loop_jump_arm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (_hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptInnerStatePolyBound rest.length m.innerState)
    (hpoly_cap :
      optInnerStatePolyCapBound m.innerState rest.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length)
    (hFit : FitsEnv M lim st
      (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hk_le : key.toNat / 8 ≤ 11)
    (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (harm : ∀ s' : State, V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s' →
      s'.pc = (blkPl_298).base + off →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (_hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := key_tag_le_11 hk_le
  rw [htag_k] at hx8
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + off) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, v1StateMergeJumpTablePlacedExpanded]
    simp only [sepConj_assoc]
  apply SepWP.fold (optProtoInnerStateCapAt_entails_discrFull A.repAlloc x.msgPtr rest.length m.innerState)
    (by sep_focus)
  conv => arg 4; rw [sepExists_sepConj_left]; simp only [sepConj_assoc]
  apply SepWP.exists_elim; intro d
  apply SepWP.pure_elim; intro hd
  rcases hk_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
    wp_steps_sync_pool_target
    apply SepWP.fold (v1Loop_discr_tail_entails_cap A.repAlloc x.msgPtr rest.length m.innerState d hd) (by sep_focus)
    wp_reach; intro hinv'
    apply SepWPp.weaken_pre
      (P' := v1StateLoopPrePlaced A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, v1StateMergeJumpTablePlacedExpanded]; sep_ac_rfl))
    exact harm _ ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hbound,
      by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp], by simp only [arm64_norm, htr],
      by simp only [arm64_norm, hx0]; cases iwt <;> rfl, by simp only [arm64_norm]; exact hd,
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩, hinv'⟩, hpoly_cap, hFit⟩ (by simp only [arm64_norm])
  }

/-- Dispatch known tag `k ∈ 1..11` at `+268` through `htag` and `v1Loop_latch_cont_placed`. -/
theorem v1Loop_dispatch_known_tag_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_acc : List AllocEvent} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (htag : V1StateTagStepHypPlaced A lim H k off)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_lt_bs : rest.length < x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptInnerStatePolyBound rest.length m.innerState)
    (hpoly_cap :
      optInnerStatePolyCapBound m.innerState rest.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length)
    (hevs_acc : SpqrMergeLoopEnv (8 * (x.bs.length - (rest.length + 1))) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc)
    (hFit_rest : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hk_le : key.toNat / 8 ≤ 11) (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (hnone_of_field_none :
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont_loop : ∀ (evs_acc' : List AllocEvent) (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      optInnerStatePolyCapBound m'.innerState rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length →
      rest'.length ≤ rest.length →
      SpqrMergeLoopEnv (8 * (x.bs.length - rest'.length)) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc' →
      FitsEnv M lim (M.stepEvents evs_acc' st0)
        (SpqrMergeLoopEnv (8 * rest'.length + 16) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc' st0) s0 s' x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) :=
  v1Loop_jump_arm_placed hsp_align hbs_lt (Nat.le_of_lt hrest_lt_bs) hrest_lt hrest_suf hbound hpoly_cap hFit_rest
    hk_le htag_k hk_cases
    (fun _ hentry hpc' => htag hentry hpc'
      (v1Loop_latch_cont_placed hPushCall hsp_align hrest_lt_bs hevs_acc hFit_rest hnone_of_field_none hcont_loop))
    hpc hrun hsp htr hx0 hx1 hx8 hregs hinv

/-- Dispatch unknown tag `> 11` at `+268` to the `+192` `skip_field` arm. -/
theorem v1Loop_dispatch_unknown_tag_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (skipField3Spec A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_acc : List AllocEvent} {R : SepProp} {s0 s : State}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_lt_bs : rest.length < x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : key.toNat / 8 < 2 ^ 32)
    (hk_gt : 11 < key.toNat / 8)
    (hevs_acc : SpqrMergeLoopEnv (8 * (x.bs.length - (rest.length + 1))) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc)
    (hFit_rest : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hnone_of_skip : skipField (2 * rest.length + 2) 99 (key.toNat / 8) iwt rest = none →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 99 (key.toNat / 8) iwt rest = some rest' →
      SpqrMergeLoopEnv (8 * (x.bs.length - rest'.length)) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc →
      FitsEnv M lim (M.stepEvents evs_acc st0)
        (SpqrMergeLoopEnv (8 * rest'.length + 16) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) →
      s'.pc = (blkPl_298).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (_hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := key_tag_gt_11 hk_gt
  have hskip := @v1Loop_skip_step_placed _ M A lim H hSkipCall x st0 evs_acc R s0
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 192#64) hinv ?_
  conv => arg 4; rw [v1StateLoopPrePlaced]
  wp_steps_sync_pool ((blkPl_298).base + 192#64); wp_reach; intro hinv'
  apply SepWPp.weaken_pre
    (P' := v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced]; sep_ac_rfl))
  exact hskip hsp_align hrest_lt_bs hrest_lt hrest_suf htag_lt hevs_acc hFit_rest hnone_of_skip hcont
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx8, sf_truncate32_ofNat64])
    ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
     by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
     by simp only [arm64_norm, hx29]⟩ hinv'

/-- Main outer loop induction at `+216` for `V1State.mergeField`. -/
theorem v1Loop_loop_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 263) (skipField3Spec A lim))
    (htag1 : V1StateTagStepHypPlaced A lim H 1 300#64)
    (htag2 : V1StateTagStepHypPlaced A lim H 2 564#64)
    (htag3 : V1StateTagStepHypPlaced A lim H 3 428#64)
    (htag4 : V1StateTagStepHypPlaced A lim H 4 476#64)
    (htag5 : V1StateTagStepHypPlaced A lim H 5 336#64)
    (htag6 : V1StateTagStepHypPlaced A lim H 6 604#64)
    (htag7 : V1StateTagStepHypPlaced A lim H 7 652#64)
    (htag8 : V1StateTagStepHypPlaced A lim H 8 516#64)
    (htag9 : V1StateTagStepHypPlaced A lim H 9 748#64)
    (htag10 : V1StateTagStepHypPlaced A lim H 10 380#64)
    (htag11 : V1StateTagStepHypPlaced A lim H 11 700#64)
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (evs_acc : List AllocEvent) (m : V1State) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptInnerStatePolyBound cur.length m.innerState →
      optInnerStatePolyCapBound m.innerState cur.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length →
      SpqrMergeLoopEnv (8 * (x.bs.length - cur.length)) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc →
      FitsEnv M lim (M.stepEvents evs_acc st0)
        (SpqrMergeLoopEnv (8 * cur.length + 16) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        (mergeLoopBin V1State.mergeField (cur.length - limit) m cur limit 99).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_298).base + 216#64 →
      s.status = .Running → s.sp = s0.sp - 816#64 → s.v1TraceEq s0 →
      V1StateLoopRegsPlaced s0 x limit s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  intro n; induction n with
  | zero =>
    intro evs_acc m cur s hcur_n hcur_le hcur_suf hbound _hcap hevs_acc hFit hres hpc hrun hsp htr hregs _hinv
    exact v1Loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt hbound hevs_acc hFit
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hregs
  | succ n ih =>
    intro evs_acc m cur s hcur_n hcur_le hcur_suf hbound hcap hevs_acc hFit hres hpc hrun hsp htr hregs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact v1Loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt hbound hevs_acc hFit
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hregs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine v1Loop_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf
        hevs_acc hFit (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hregs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_lt_bs : rest.length < x.bs.length := Nat.lt_of_lt_of_le hrest_lt_cur hcur_le
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_of_lt hrest_lt_bs
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_rest : OptInnerStatePolyBound rest.length m.innerState := optInnerStatePolyBound_mono hbound hrest_le_cur
      have hcap_rest : optInnerStatePolyCapBound m.innerState rest.length ≤
          optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
        Nat.le_trans (optInnerStatePolyCapBound_mono_len hrest_le_cur) hcap
      have hevs_rest : SpqrMergeLoopEnv (8 * (x.bs.length - (rest.length + 1))) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc :=
        hevs_acc.mono_fuel (by omega)
      have hFit_rest : FitsEnv M lim (M.stepEvents evs_acc st0)
          (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
            (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) :=
        FitsEnv.spqrMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 99) protoPrefixStep_v1State_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases hk_le : key.toNat / 8 ≤ 11
      · have hknown : ∀ (k : Nat) (off : BitVec 64),
            V1StateTagStepHypPlaced A lim H k off → key.toNat / 8 = k →
            (k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
             k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
             k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
             k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64) →
            SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
              (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
          intro k off htag htag_k hk_cases
          refine v1Loop_dispatch_known_tag_placed hPushCall htag hsp_align hbs_lt hrest_lt_bs hrest_lt hrest_suf
            hbound_rest hcap_rest hevs_rest hFit_rest hk_le htag_k hk_cases
            (fun hfn => by rw [hres, hstep, htag_k, hfn]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
          intro evs_acc' m' rest' s'' hfsome hbound' hcap' hr'_le hevs_acc' hFit' hpc'' hrun'' hsp'' htr'' hregs'' hinv''
          obtain ⟨_, hr'_suf⟩ := v1Loop_mergeField_suffix hk_cases hfsome
          exact ih evs_acc' m' rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le hr'_suf) hbound' hcap' hevs_acc' hFit'
            (by rw [hres, hstep, htag_k, hfsome]) hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hk_cases11 : key.toNat / 8 = 1 ∨ key.toNat / 8 = 2 ∨ key.toNat / 8 = 3 ∨
            key.toNat / 8 = 4 ∨ key.toNat / 8 = 5 ∨ key.toNat / 8 = 6 ∨ key.toNat / 8 = 7 ∨
            key.toNat / 8 = 8 ∨ key.toNat / 8 = 9 ∨ key.toNat / 8 = 10 ∨ key.toNat / 8 = 11 := by omega
        rcases hk_cases11 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
        · exact hknown 1 300#64 htag1 h1 (by decide)
        · exact hknown 2 564#64 htag2 h2 (by decide)
        · exact hknown 3 428#64 htag3 h3 (by decide)
        · exact hknown 4 476#64 htag4 h4 (by decide)
        · exact hknown 5 336#64 htag5 h5 (by decide)
        · exact hknown 6 604#64 htag6 h6 (by decide)
        · exact hknown 7 652#64 htag7 h7 (by decide)
        · exact hknown 8 516#64 htag8 h8 (by decide)
        · exact hknown 9 748#64 htag9 h9 (by decide)
        · exact hknown 10 380#64 htag10 h10 (by decide)
        · exact hknown 11 700#64 htag11 h11 (by decide)
      · have hk_gt : 11 < key.toNat / 8 := by omega
        rw [v1State_mergeField_other m iwt rest 99 htag_lt (Or.inr hk_gt)] at hstep
        refine v1Loop_dispatch_unknown_tag_placed hSkipCall hsp_align hrest_lt_bs hrest_lt hrest_suf
          htag_lt hk_gt hevs_rest hFit_rest
          (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl) ?_ hpc' hrun' hsp' htr' hx0' hx1' hx8' hregs' hinv'
        intro rest' s'' hsf_some hevs_acc' hFit' hpc'' hrun'' hsp'' htr'' hregs'' hinv''
        have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
        exact ih evs_acc m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
          (optInnerStatePolyBound_mono hbound_rest hr'_le)
          (Nat.le_trans (optInnerStatePolyCapBound_mono_len hr'_le) hcap_rest)
          hevs_acc' hFit'
          (by rw [hres, hstep, hsf_some]; rfl) hpc'' hrun'' hsp'' htr'' hregs'' hinv''

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudget
