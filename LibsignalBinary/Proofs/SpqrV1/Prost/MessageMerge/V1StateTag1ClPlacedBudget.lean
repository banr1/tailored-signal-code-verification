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
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Tag Arm 1 (`KeysUnsampled`) for `V1State::merge` (Block `298`)

Defines the budget-threaded code-loaded continuation `V1StateTagContClPlaced` and verifies tag arm
1 (`KeysUnsampled`, `v1State_tag1_step_cl_placed`) with cross-block drop callee `267` wrapped in
`withLsCl lsmpl`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent AllocCallPreserved BudgetLimits FitsEnv FreeOnlyEvs
   PoolPreserved RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeIterEnv SpqrMergeLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedKeysUnsampledMergeEnv ChunkedKeysUnsampledMergePostEnv
   chunkedKeysUnsampledMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (optInnerStatePolyCapBound v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
   align_pre deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents
   optInnerStatePolyCapBound_ge_len optInnerStatePolyCapBound_of_keysUnsampled
   pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq
   subroutine_ok_deallocFreeOnly tag_err_env_inplace tag_err_env_of_free
   tag_fitsEnv_sub tag_ok_env_inplace tag_ok_env_of_free
   v1State_tail_2680_placed v1State_tail_2692_placed wppPanicFalse_of_false)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl withLsCl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt
   optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.ProtoRepr (noneCap2)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (InnerStateDiscrFull InnerStatePolyBound OptInnerStatePolyBound
   SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
   V1StateLoopRegsPlaced V1StateMergeGhost V1StateTagEntryHypPlaced WppPost
   bv64_add_zero bv64_sub_zero chunkedInlStack
   chunkedKeysUnsampledPBAt chunkedKeysUnsampledPBAt_entails_err_dealloc
   chunkedKeysUnsampledPBAt_eq_proto chunkedKeysUnsampledPBCapAt
   codecWireTypeToProto discrFull_none_add2 discrFull_other_tag1 discrFull_some_add2
   memRegion_224_split_tag1_ok memRegion_fold_tag1_temp memRegion_split_tag1_temp
   optInnerStatePolyBound_lt_2_56
   optKeysUnsampledPBCapAt optKeysUnsampledPBCapAt_eq_optUnchunked2
   optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
   optUnchunked2CapAt_extract_words optUnchunked2CapHeap
   protoInnerStateCapAt proto_mergeMessage_len_le sepWP_seq_keep_lscl tag1_reconstruct_innerState
   v1StateBelowRest v1StateBelow_allocHook v1StateBelow_allocHook_entails
   v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1State_mergeField_tag1 words7At)
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

/-! ## 1. Code-Loaded Continuation Bundle at `(blkPl_298).base + 2700#64` -/

/-- Budget-threaded continuation at `(blkPl_298).base + 2700#64` for tag `k` (`1..11`)
under `[LibsignalPlacement]`, carrying `LibsignalCodeRoLoaded lsmpl s'.mem` on both
`onErr` and `onOk`. -/
structure V1StateTagContClPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (s0 : State) (x : V1StateMergeGhost)
    (st0 st : M.σ) (R : SepProp) (k : Nat) (m : V1State)
    (rest : List (BitVec 8)) (iwt : WireType) (limit : Nat) : Prop where
  onErr :
    (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
    ∀ (evs_tag : List AllocEvent) (s' : State) (err : BitVec 64) (n_err : Nat),
      SpqrMergeLoopEnv (8 * rest.length + 16) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_tag →
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = err → err ≠ 0#64 → n_err ≤ 3 →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (decodeErrorAtStackLen A.repAlloc err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A lim (M.stepEvents evs_tag st) s0 s' x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)
  onOk :
    ∀ (evs_tag : List AllocEvent) (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      optInnerStatePolyCapBound m'.innerState rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length →
      rest'.length ≤ rest.length →
      SpqrMergeLoopEnv (8 * (rest.length - rest'.length) + 8) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_tag →
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = 0#64 →
      V1StateLoopRegsPlaced s0 x limit s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_tag st) s0 s' x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)

/-- Any `V1StateTagContPlaced` trivially weakens to `V1StateTagContClPlaced`. -/
theorem V1StateTagContPlaced.toClPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {s0 : State} {x : V1StateMergeGhost}
    {st0 st : M.σ} {R : SepProp} {k : Nat} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (h : V1StateTagContPlaced A lim H s0 x st0 st R k m rest iwt limit) :
    V1StateTagContClPlaced A lim H s0 x st0 st R k m rest iwt limit where
  onErr hnone evs_tag s' err n_err hevs hpc hrun hsp htr hx21 herr hn _hinv :=
    h.onErr hnone evs_tag s' err n_err hevs hpc hrun hsp htr hx21 herr hn
  onOk := h.onOk

/-- Uniform per-tag step hypothesis shape consumed by `V1StateLoopClPlacedBudget` for tag `k` at `entryOff`. -/
abbrev V1StateTagStepHypClPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (k : Nat) (entryOff : BitVec 64) : Prop :=
  ∀ {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat},
    V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s →
    s.pc = (blkPl_298).base + entryOff →
    V1StateTagContClPlaced A lim H s0 x st0 st R k m rest iwt limit →
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)

private theorem sepWP_mono_freeOnly {prog : Program} {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {Q : List AllocEvent → State → SepProp → Prop}
    (h : SepWP prog tgt s Pre (Q evs)) :
    SepWP prog tgt s Pre (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ Q evs' sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨evs, hevs, hq⟩

/-! ## 2. Tag 1 (`KeysUnsampled`, `+300..+332`, `+1472..+1564`, `+2632..+2700`) -/

theorem v1State_tag1_inplace_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {ku : V1State.Chunked.KeysUnsampled}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.keysUnsampled ku))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 300#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 1 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, _hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  rw [hm_is] at hx9
  change s.readReg64 (Reg.gpr 9#5) = 0x8000000000000000#64 at hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000000#64) = false := by rw [hx9]; decide
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hFit_sub : FitsEnv M lim st
      (ChunkedKeysUnsampledMergeEnv ⟨iwt, x.msgPtr + 8#64, ku, x.bufRef, x.slot, restPtr, rest⟩) :=
    tag_fitsEnv_sub hrest_le (Nat.zero_le _) hFit
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 305) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 305); wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, x.msgPtr + 8#64, ku, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 328#64) hKuCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by
      dsimp only [chunkedKeysUnsampledMergeSpec,
        ChunkedInlinedCommonBudget.chunkedKeysUnsampledMergeSpecOfEnv]
      simp only [arm64_norm, hsp, hx0]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧
        rest.length < 2 ^ 63 ∧
        FitsEnv M lim st
          (ChunkedKeysUnsampledMergeEnv ⟨iwt, x.msgPtr + 8#64, ku, x.bufRef, x.slot, restPtr, rest⟩))
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag1 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hku_res : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) ku rest 99).toOption with
  | none =>
    rw [hku_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec,
        ChunkedInlinedCommonBudget.chunkedKeysUnsampledMergeSpecOfEnv,
        ChunkedKeysUnsampledMergePostEnv, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro ku'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0, hn_err⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000000#64) ∗
        chunkedKeysUnsampledPBAt A.repAlloc (x.msgPtr + 8#64) ku' ∗ memRegion (x.msgPtr + 64#64) 160 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is' := by
      rw [chunkedKeysUnsampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr (some (.keysUnsampled ku'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs st) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; sep_ac_rfl))
    exact honErr hm_field evs _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (tag_err_env_inplace hrest_le (Nat.zero_le _) hevs)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨ku', rest'⟩
    rw [hku_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hku_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.keysUnsampled ku')) := by
      have h56 := optInnerStatePolyBound_lt_2_56 hpoly
      unfold OptInnerStatePolyBound InnerStatePolyBound; omega
    have hcap' : optInnerStatePolyCapBound (some (.keysUnsampled ku')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_keysUnsampled hku_res)
        (Nat.le_trans hrest_le (optInnerStatePolyCapBound_ge_len x.msg.innerState x.bs.length))
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec,
        ChunkedInlinedCommonBudget.chunkedKeysUnsampledMergeSpecOfEnv,
        ChunkedKeysUnsampledMergePostEnv, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs⟩, hsm0⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents evs st) s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.keysUnsampled ku') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; sep_ac_rfl))
    exact honOk evs { m with innerState := some (.keysUnsampled ku') } rest' _
      hm_field hpoly' hcap' hrest'_le
      (tag_ok_env_inplace hrest_le (Nat.zero_le _) hevs)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1State_tag1_dealloc_x24_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s : State} {st : M.σ} {fsp w0 w1 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1524#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1544#64) s
      (vecCapPtrDealloc A.repAlloc w0 w1 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5)) := by
  have hDealloc' := subroutine_ok_deallocFreeOnly hDealloc
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hDealloc'
  dsimp only [vecCapPtrDealloc]
  by_cases hw0 : (w0 == 0#64) = true <;>
    simp only [hw0, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 24#5) == 0#64) = true := by rw [hx24]; exact hw0
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ A.pool lim (M.stepEvents [] st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
      sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
      sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5)) ?_
      (fun _ _ _ _ h => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, h⟩)
    wp_steps_sync_pool ((blkPl_298).base + 1544#64); wp_done
  · have hbr : (s.readReg64 (Reg.gpr 24#5) == 0#64) = false := by
      rw [hx24]; exact Bool.eq_false_iff.mpr hw0
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ A.pool lim (M.stepEvents (rustDeallocEvents w0.toNat 1) st) sm ∗
        stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
      sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
      sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5)) ?_
      (fun _ _ _ _ h => ⟨rustDeallocEvents w0.toNat 1, freeOnlyEvs_rustDeallocEvents w0.toNat 1, h⟩)
    simp only [sepConj_assoc]
    change SepWP _ _ _ (A.live w1 w0.toNat 1 ∗ memRegion w1 w0.toNat ∗ A.pool lim st s ∗
      stackAt fsp allocHookStack ∗ Frame) _
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    wp_apply
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_dealloc_x22_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s : State} {st : M.σ} {fsp w3 w4 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1544#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      (vecCapPtrDealloc A.repAlloc w3 w4 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hDealloc' := subroutine_ok_deallocFreeOnly hDealloc
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hDealloc'
  dsimp only [vecCapPtrDealloc]
  by_cases hw3 : (w3 == 0#64) = true <;>
    simp only [hw3, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 22#5) == 0#64) = true := by rw [hx22]; exact hw3
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ A.pool lim (M.stepEvents [] st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, h⟩)
    wp_steps_sync_pool ((blkPl_298).base + 2680#64); wp_done
  · have hbr : (s.readReg64 (Reg.gpr 22#5) == 0#64) = false := by
      rw [hx22]; exact Bool.eq_false_iff.mpr hw3
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ A.pool lim (M.stepEvents (rustDeallocEvents w3.toNat 1) st) sm ∗
        stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨rustDeallocEvents w3.toNat 1, freeOnlyEvs_rustDeallocEvents w3.toNat 1, h⟩)
    simp only [sepConj_assoc]
    change SepWP _ _ _ (A.live w4 w3.toNat 1 ∗ memRegion w4 w3.toNat ∗ A.pool lim st s ∗
      stackAt fsp allocHookStack ∗ Frame) _
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    wp_apply
    wp_steps_sync_pool ((blkPl_298).base + 2680#64)
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_ok_copy_2632_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr w_sp8 w0 w1 w2 w3 w4 w5 w6 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2632#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((fsp + 8#64) ↦₆₄ w_sp8) ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ ((fsp + 8#64) ↦₆₄ w2) ∗
          (mPtr ↦₆₄ 0x8000000000000000#64) ∗ words7At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 ∗
          memRegion (mPtr + 64#64) 160 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  conv => arg 4; dsimp only [words7At]
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag1_ok mPtr]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0
  refine sepWP_mono_freeOnly (by assumption) ?_
  dsimp only [words7At]
  wp_steps_sync_pool ((blkPl_298).base + 2680#64)
  exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1State_tag1_err_1512_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s : State} {st : M.σ} {fsp w0 w1 w3 w4 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1512#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = w3) (hx23 : s.readReg64 (Reg.gpr 23#5) = w4)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = w0) (hx25 : s.readReg64 (Reg.gpr 25#5) = w1) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2680#64) s
      ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
        else vecCapPtrDealloc A.repAlloc w0 w1 ∗ vecCapPtrDealloc A.repAlloc w3 w4) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  by_cases hcc : ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) = true <;>
    simp only [hcc, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
  · have hbr : ConditionHolds .CC (subsPState64 (s.readReg64 (Reg.gpr 24#5) + 2#64) 2#64) = true := by
      rw [hx24]; exact hcc
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ A.pool lim (M.stepEvents [] st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, h⟩)
    wp_steps_sync_pool ((blkPl_298).base + 2680#64); wp_done
  · have hstep1 : SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 1524#64) s
        ((vecCapPtrDealloc A.repAlloc w0 w1 ∗ vecCapPtrDealloc A.repAlloc w3 w4) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun s1 P1 =>
          (P1 ⊢ vecCapPtrDealloc A.repAlloc w0 w1 ∗ A.pool lim st s1 ∗
            stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A.repAlloc w3 w4 ∗ Frame)) ∧
          s1.sp = s.sp ∧ s1.v1TraceEq s ∧
          s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          s1.readReg64 (Reg.gpr 22#5) = w3 ∧ s1.readReg64 (Reg.gpr 23#5) = w4 ∧
          s1.readReg64 (Reg.gpr 24#5) = w0 ∧ s1.readReg64 (Reg.gpr 25#5) = w1) := by
      have hbr : ConditionHolds .CC (subsPState64 (s.readReg64 (Reg.gpr 24#5) + 2#64) 2#64) = false := by
        rw [hx24]; exact Bool.eq_false_iff.mpr hcc
      wp_steps_sync_pool ((blkPl_298).base + 1524#64); wp_done
    refine SepWP.seq hstep1 ?_
    rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.seq (v1State_tag1_dealloc_x24_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx24_1 hx25_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨evs1, hevs1, hP2, hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
      A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗
        (vecCapPtrDealloc A.repAlloc w3 w4 ∗ Frame) =
      vecCapPtrDealloc A.repAlloc w3 w4 ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
        stackAt fsp allocHookStack ∗ Frame))) ?_
    refine SepWP.mono (v1State_tag1_dealloc_x22_placed hDealloc hsp_align hpc2 hrun2
      (hsp2.trans (hsp1.trans hsp)) (hx22_2.trans hx22_1) (hx23_2.trans hx23_1)) ?_
    rintro s3 P3 _ _ ⟨evs2, hevs2, hP3, hsp3, htr3, hx21_3⟩
    rw [← stepEvents_append_eq evs1 evs2 st] at hP3
    exact ⟨evs1 ++ evs2, hevs1.append hevs2, hP3,
      hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1), hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1State_tag1_load_ok_1496_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2632#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1 ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  wp_steps_sync_pool ((blkPl_298).base + 2632#64); wp_done

private theorem v1State_tag1_load_err_1496_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w0 w1 w2 w3 w4 w5 w6 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1496#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1512#64) s
      (words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = w3 ∧ sm.readReg64 (Reg.gpr 23#5) = w4 ∧
        sm.readReg64 (Reg.gpr 24#5) = w0 ∧ sm.readReg64 (Reg.gpr 25#5) = w1) := by
  dsimp only [words7At]
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  wp_steps_sync_pool ((blkPl_298).base + 1512#64); wp_done

private theorem v1State_tag1_setup_1472_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp240 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1472#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305) s
      (((fsp + 240#64) ↦₆₄ w_sp240) ∗ memRegion (fsp + 248#64) 48 ∗ A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedKeysUnsampledPBCapAt A.repAlloc (fsp + 240#64) restLen default ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 240#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1496#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef_ku : ((fsp + 240#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 248#64) 48 ⊢
      chunkedKeysUnsampledPBCapAt A.repAlloc (fsp + 240#64) restLen default := by
    dsimp only [chunkedKeysUnsampledPBCapAt, default, Inhabited.default, optKeysUnsampledPBCapAt, noneCap2]
    have h8 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
    rw [h8]; exact Entails.refl _
  wp_steps_sync_pool (lsmpl.base 305)
  apply SepWP.fold hdef_ku (by sep_focus)
  wp_done

theorem v1State_tag1_at_1472_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1472#64)
    (hcont : V1StateTagContClPlaced A lim H s0 x st0 st R 1 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩, _hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : ((s0.sp - 816#64) &&& 15#64 == 0#64) = true := by
    simpa only [arm64_norm] using hsp_align
  have hfsp240 : (s0.sp - 816#64) + 240#64 = s0.sp - 576#64 := by bv_lin
  have hfsp248 : (s0.sp - 816#64) + 248#64 = s0.sp - 568#64 := by bv_lin
  have hfsp8 : (s0.sp - 816#64) + 8#64 = s0.sp - 808#64 := by bv_lin
  have hFit_sub : FitsEnv M lim st
      (ChunkedKeysUnsampledMergeEnv ⟨iwt, s0.sp - 576#64, default, x.bufRef, x.slot, restPtr, rest⟩) :=
    tag_fitsEnv_sub hrest_le (Nat.zero_le _) hFit
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 305) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, memRegion_split_tag1_temp s0.sp, sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp240
  apply SepWP.exists_elim; intro w_sp8
  rw [← hfsp240, ← hfsp248]
  refine SepWP.weaken_pre (P' := (((s0.sp - 816#64) + 240#64) ↦₆₄ w_sp240) ∗
    memRegion ((s0.sp - 816#64) + 248#64) 48 ∗ A.pool lim st s ∗
    (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 8 ∗
      ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗ memRegion (s0.sp - 800#64) 224 ∗
      memRegion (s0.sp - 520#64) 424 ∗ v1StateJumpTablesPlacedAt ∗
      optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m.innerState ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
      (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; sep_ac_rfl)) ?_
  refine SepWP.mono (v1State_tag1_setup_1472_placed (A := A) (lim := lim) (st := st)
    (restLen := rest.length) hfsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hfsp240] at hP1 hx1_1
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1 hx27_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, s0.sp - 576#64, default, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 1496#64) hKuCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by
      dsimp only [chunkedKeysUnsampledMergeSpec,
        ChunkedInlinedCommonBudget.chunkedKeysUnsampledMergeSpecOfEnv]
      simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        s0.sp - 576#64 = s0.sp - 576#64 ∧ x.bufRef = x.bufRef ∧
        rest.length < 2 ^ 63 ∧
        FitsEnv M lim st
          (ChunkedKeysUnsampledMergeEnv ⟨iwt, s0.sp - 576#64, default, x.bufRef, x.slot, restPtr, rest⟩))
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest 99).toOption =
      (mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.keysUnsampled v') }, rest')) := by
    rw [v1State_mergeField_tag1]
    rcases h : m.innerState with _ | st_is
    · rfl
    · cases st_is with
      | keysUnsampled ku => exact absurd h (hm_not ku)
      | _ => rfl
  cases hku_res : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hku_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2680#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec,
        ChunkedInlinedCommonBudget.chunkedKeysUnsampledMergeSpecOfEnv,
        ChunkedKeysUnsampledMergePostEnv, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.exists_elim; intro ku'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_m⟩, hsm0, hn_err⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBAt_entails_err_dealloc A.repAlloc (s0.sp - 576#64) ku') (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_allocHook (s0.sp - 816#64), ← hfsp240]
    let Frame_err : SepProp :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        v1StateBelowRest (s0.sp - 816#64) allocHookStack ∗
        memRegion (s0.sp - 816#64) 8 ∗ ((s0.sp - 808#64) ↦₆₄ w_sp8) ∗
        memRegion (s0.sp - 800#64) 224 ∗ memRegion (s0.sp - 520#64) 424 ∗
        v1StateJumpTablesPlacedAt ∗
        (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
        (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        A.pool lim (M.stepEvents evs_m st) sm ∗
        ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
          else vecCapPtrDealloc A.repAlloc w0 w1 ∗ vecCapPtrDealloc A.repAlloc w3 w4) ∗
          stackAt (s0.sp - 816#64) allocHookStack ∗ Frame_err))
      (Entails.of_eq (by dsimp only [Frame_err]; sep_ac_rfl)) ?_
    refine SepWP.seq (v1State_tag1_load_err_1496_placed (A := A) (lim := lim)
      hfsp_align hpcm hrunm hspm hsm0) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        A.pool lim (M.stepEvents evs_m st) s2 ∗
        ((if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
          else vecCapPtrDealloc A.repAlloc w0 w1 ∗ vecCapPtrDealloc A.repAlloc w3 w4) ∗
          stackAt (s0.sp - 816#64) allocHookStack ∗ Frame_err) =
      (if ConditionHolds .CC (subsPState64 (w0 + 2#64) 2#64) then emp
       else vecCapPtrDealloc A.repAlloc w0 w1 ∗ vecCapPtrDealloc A.repAlloc w3 w4) ∗
        A.pool lim (M.stepEvents evs_m st) s2 ∗ stackAt (s0.sp - 816#64) allocHookStack ∗
        (words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗ Frame_err)))) ?_
    refine SepWP.seq (v1State_tag1_err_1512_placed hDealloc hfsp_align hpc2 hrun2
      (hsp2.trans hspm) hx22_2 hx23_2 hx24_2 hx25_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx21_3⟩
    rw [← stepEvents_append_eq evs_m evs_d st] at hP3
    apply SepWP.weaken_pre hP3
    rw [hfsp240]; dsimp only [Frame_err]
    apply SepWP.fold (v1StateBelow_allocHook_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w_sp8 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    refine v1State_tail_2680_placed hpc3 hrun3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hvm4 _ _ hx21_4 _ _ _ _ _ _ _ _ hinv4
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs_m ++ evs_d) st) s0 s4 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by
        dsimp only [v1StateErrFramePlaced]
        rw [pool_eq_of_vmPreserved A lim _ hvm4]; sep_ac_rfl))
    exact hcont.onErr hm_field (evs_m ++ evs_d) s4 (sm.readReg64 (Reg.gpr 0#5)) n_err
      (tag_err_env_of_free hrest_le (Nat.zero_le _) hevs_m hevs_d)
      hpc4 hrun4
      (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2)) hsm0 hn_err (hinv4 _ hinv3)
  | some p =>
    rcases p with ⟨ku', rest'⟩
    rw [hku_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hku_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.keysUnsampled ku')) := by
      have h56 := optInnerStatePolyBound_lt_2_56 hpoly
      unfold OptInnerStatePolyBound InnerStatePolyBound; omega
    have hcap' : optInnerStatePolyCapBound (some (.keysUnsampled ku')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_keysUnsampled hku_res)
        (Nat.le_trans hrest_le (optInnerStatePolyCapBound_ge_len x.msg.innerState x.bs.length))
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2680#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedKeysUnsampledMergeSpec,
        ChunkedInlinedCommonBudget.chunkedKeysUnsampledMergeSpecOfEnv,
        ChunkedKeysUnsampledMergePostEnv, hku_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_m⟩, hsm0⟩
    replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState) (by sep_focus)
    have hku_words : chunkedKeysUnsampledPBCapAt A.repAlloc (s0.sp - 576#64) rest'.length ku' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
          words7At (s0.sp - 576#64) w0 w1 w2 w3 w4 w5 w6 ∗
          optUnchunked2CapHeap A.repAlloc rest'.length (ku'.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 := by
      dsimp only [chunkedKeysUnsampledPBCapAt]
      rw [optKeysUnsampledPBCapAt_eq_optUnchunked2]
      exact optUnchunked2CapAt_extract_words A.repAlloc (s0.sp - 576#64) rest'.length (ku'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hku_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64), ← hfsp240, ← hfsp8]
    dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      optUnchunked2CapHeap A.repAlloc rest'.length (ku'.uc.map fun u => (u.epoch, u.auth)) w0 w1 w2 w3 w4 w5 w6 ∗
        v1StateBelowRest (s0.sp - 816#64) dropStack96 ∗
        memRegion (s0.sp - 816#64) 8 ∗ memRegion (s0.sp - 800#64) 224 ∗
        memRegion (s0.sp - 520#64) 424 ∗ v1StateMergeJumpTablePlacedExpanded ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
        v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        A.pool lim (M.stepEvents evs_m st) sm ∗
        (optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
          (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; sep_ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1State_tag1_load_ok_1496_placed (A := A) (lim := lim)
      hfsp_align hpcm hrunm hspm hsm0) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
      words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        A.pool lim (M.stepEvents evs_m st) s2 ∗
        (optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
          (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok) =
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗
        A.pool lim (M.stepEvents evs_m st) s2 ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt (s0.sp - 816#64) dropStack96 ∗
        words7At ((s0.sp - 816#64) + 240#64) w0 w1 w2 w3 w4 w5 w6 ∗
        (((s0.sp - 816#64) + 8#64) ↦₆₄ w_sp8) ∗ Frame_ok))) ?_
    refine SepWP.seq (v1State_tag1_ok_copy_2632_cl_placed hDropInner hcl2 hfsp_align hpc2 hrun2
      (hsp2.trans hspm) (hx20_2.trans hx20_m) hx22_2 hx23_2 hx24_2 hx25_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx19_3, hx20_3, hx21_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    rw [← stepEvents_append_eq evs_m evs_d st] at hP3
    apply SepWP.weaken_pre hP3
    rw [hfsp240, hfsp8]; dsimp only [Frame_ok]
    apply SepWP.fold (v1StateBelow_dropStack96_entails (s0.sp - 816#64)) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag1_temp s0.sp w2 w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    apply SepWP.fold (tag1_reconstruct_innerState A.repAlloc x.msgPtr rest'.length ku' w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    refine v1State_tail_2680_placed hpc3 hrun3 ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hvm4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hinv4
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.keysUnsampled ku') } x.bs rest')
      (Entails.of_eq (by
        dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt]
        rw [pool_eq_of_vmPreserved A lim _ hvm4]; sep_ac_rfl))
    have hsp4' : s4.sp = s0.sp - 816#64 := hsp4.trans (hsp3.trans (hsp2.trans hspm))
    exact hcont.onOk (evs_m ++ evs_d) { m with innerState := some (.keysUnsampled ku') } rest' s4
      hm_field hpoly' hcap' hrest'_le
      (tag_ok_env_of_free hrest_le (Nat.zero_le _) hevs_m hevs_d)
      hpc4 hrun4 hsp4'
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4.trans (hx20_3.trans (hx20_2.trans hx20_m)),
       hx22_4, hx23_4,
       hx24_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       by rw [hx25_4, hsp3.trans (hsp2.trans hspm), hfsp240],
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4,
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans (hx29_3.trans (hx29_2.trans hfp_m))⟩
      (hinv4 _ hinv3)

private theorem v1State_tag1_branch_1472_placed [LibsignalPlacement] {M : AllocCostModel}
    {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st : M.σ} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : State → SepProp} {post panic : State → SepProp → Prop}
    (hpool : ∀ s', VmPreserved s s' → P s = P s')
    (hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku))
    (hentry : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 300#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1472#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' (P s') post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s (P s) post panic := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1472#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (hpool _ ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
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
    have hne : ∀ ku, is ≠ .keysUnsampled ku := fun ku h => hm_not ku (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000000#64) = true :=
      discrFull_other_tag1 hne hx9_s
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre
      (hpool _ ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
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

theorem v1State_tag1_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hKuCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim)) :
    V1StateTagStepHypClPlaced A lim H 1 300#64 := by
  intro s0 s x st0 st R m rest iwt limit hentry hpc hcont
  by_cases hex : ∃ ku, m.innerState = some (.keysUnsampled ku)
  · rcases hex with ⟨ku, hm_is⟩
    exact v1State_tag1_inplace_cl_placed hKuCall hm_is hentry hpc hcont
  · have hm_not : ∀ ku, m.innerState ≠ some (.keysUnsampled ku) := fun ku h => hex ⟨ku, h⟩
    refine v1State_tag1_branch_1472_placed (lim := lim)
      (P := fun s_cur => v1StateLoopPrePlaced A lim st s0 s_cur x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (fun s' hvm => by dsimp only [v1StateLoopPrePlaced]; rw [pool_eq_of_vmPreserved A lim st hvm])
      hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag1_at_1472_cl_placed hKuCall hDropInner hDealloc hm_not hentry' hpc' hcont

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
