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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Outer Loop Exits and Latch Continuation for `V1State::merge` (Block `298`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` epilogue returns, `DecodeError::{from,push}`
exits, loop-bound exit, and shared latch continuation (`+2700 -> +216`) for `V1State::merge`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv FitsEnv.spqrMergeLoop_head FitsEnv.spqrMergeLoop_mono
   FitsEnv.spqrMergeLoop_split FitsEnv.spqrMergeLoop_tail SpqrMergeIterEnv SpqrMergeLoopEnv
   decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergePostEnv optInnerStatePolyCapBound v1StateErrFramePlaced
   v1StateLoopPrePlaced v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagContPlaced WppPanicFalse stepEvents_append_eq wppPanicFalse_of_false)
open CryptoVerification (LibsignalPlacement lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop
  (optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound SepWPp.of_sepWP_lscro V1StateLoopRegsPlaced V1StateMergeGhost WppPost
   bv64_add_zero bv64_sub_zero chunkedInlStack cmp_len_limit_of_eq cmp_len_limit_of_lt
   codecWireTypeToProto decodeErrorWith_le4_intro optProtoInnerStateAt_entails_exists
   optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb stackAt_v1StateMerge_epilogue
   v1Loop_err1_join_720 v1Loop_err48_join_720 v1Loop_memRegion_720_split_err1
   v1StateBelow_decodeError v1StateBelow_decodeError_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateMergeStack
   v1StateSavedRegsAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (blkLib_eq_298 blkPC_298 blkPC_298_pairStep_0xd30 blkPC_298_pairStep_0xd38 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  optProtoInnerStateJumpTablePlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## 1. Allocator Event Envelope Combinators for `DecodeError::{from,push}` & Epilogue -/

theorem spqrIter_of_decodeErrorFrom {maxLen polyCap : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    SpqrMergeIterEnv maxLen polyCap evs := by
  rw [show evs = _ from h]
  exact .fromErr

theorem spqrIter_of_decodeErrorPush {maxLen polyCap n : Nat} {evs : List AllocEvent}
    (hn : n ≤ 4) (h : DecodeErrorPushMergeEnv n evs) :
    SpqrMergeIterEnv maxLen polyCap evs :=
  .pushErr hn h

private theorem v1Loop_postEnv_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {x : V1StateMergeGhost} {st0 : M.σ} {sf : State} {evs : List AllocEvent}
    (hpost : V1StateMergePostEnv x evs) :
    A.pool lim (M.stepEvents evs st0) sf ⊢
      ∃∗ evs' : List AllocEvent, ⌜V1StateMergePostEnv x evs'⌝ ∗ A.pool lim (M.stepEvents evs' st0) sf := by
  refine Entails.sepExists_right evs ?_
  simp only [eq_true hpost, pure_true, emp_sepConj]
  exact Entails.refl _

private def v1StateMergePlacedFixedPost [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : V1StateMergeGhost) (st0 : M.σ)
    (evs : List AllocEvent) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
    A.pool lim (M.stepEvents evs st0) sf ∗
    stackAt s0.sp v1StateMergeStack ∗
    match (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
    | some (m', rest) =>
      ⌜sf.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m'.innerState ∗
        sliceCursorAfter x.slot x.ptr x.bs rest
    | none =>
      ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
        (∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
        (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
        memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

private theorem sepWP_wppPost_of_fixedPost [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {s0 s : State}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs : List AllocEvent} {R Pre : SepProp}
    (hpost_env : V1StateMergePostEnv x evs)
    (h : SepWP prog (s0.readReg64 Reg.lr) s Pre
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ v1StateMergePlacedFixedPost A lim x st0 evs s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog (s0.readReg64 Reg.lr) s Pre
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) := by
  refine SepWP.mono h fun sf Pf _ _ ⟨hm, hsp, hcs⟩ => ⟨fun hPf => ?_, hsp, hcs⟩
  refine Satisfies.mono (sepConj_mono_left ?_) (hm hPf)
  unfold v1StateMergePlacedFixedPost v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (v1Loop_postEnv_entails A lim hpost_env))))

/-! ## 2. Shared Epilogue Return (`+128..+160`) and `DecodeError::{from,push}` Exits -/

/-- Epilogue return at `+128` on error (`x1 = err ≠ 0#64`, `n_err ≤ 4`). -/
theorem v1Loop_err_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs : List AllocEvent} {R : SepProp}
    {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hevs : SpqrMergeLoopEnv (8 * x.bs.length + 16) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs)
    (hn : n_err ≤ 4) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs st0) s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases htr with ⟨htr, hvregs⟩
  apply SepWPp.of_sepWP_ret
  refine sepWP_wppPost_of_fixedPost (evs := evs)
    (by simpa only [V1StateMergePostEnv, hnone] using hevs) ?_
  dsimp only [v1StateMergePlacedFixedPost]
  conv => arg 5; simp only [hnone]
  conv =>
    arg 4
    simp only [v1StateErrFramePlaced, v1StateSavedRegsAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.exists_elim; intro is'
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  apply SepWP.fold (decodeErrorWith_le4_intro A.repAlloc err hn) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A.repAlloc x.msgPtr is'') is')
    (by sep_focus)
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Epilogue return at `+128` on success (`x1 = 0#64`). -/
theorem v1Loop_ok_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs : List AllocEvent} {R : SepProp}
    {s0 s : State} {m' : V1State} {rest : List (BitVec 8)}
    (hsome : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = some (m', rest))
    (hevs : SpqrMergeLoopEnv (8 * (x.bs.length - rest.length)) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs)
    (hbound : OptInnerStatePolyBound rest.length m'.innerState) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = 0#64) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases htr with ⟨htr, hvregs⟩
  apply SepWPp.of_sepWP_ret
  refine sepWP_wppPost_of_fixedPost (evs := evs)
    (by simpa only [V1StateMergePostEnv, hsome] using hevs) ?_
  dsimp only [v1StateMergePlacedFixedPost]
  conv => arg 5; simp only [hsome]
  conv =>
    arg 4
    simp only [v1StateLoopPrePlaced, v1StateSavedRegsAt, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Shared exit at `+112`: stores `X8 = w` (`KindNoHeap w`) at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::from`, and returns via `v1Loop_err_ret_exit_placed`. -/
theorem v1Loop_from_err_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_pre : List AllocEvent} {R : SepProp}
    {s0 s : State} {w : BitVec 64}
    (hnone : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hevs_pre : SpqrMergeLoopEnv (8 * x.bs.length + 15) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_pre)
    (hFit : FitsEnv M lim (M.stepEvents evs_pre st0) DecodeErrorFromEnv)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx8 : s.readReg64 (Reg.gpr 8#5) = w) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs_pre st0) s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  subst hx8
  have herr_ret := @v1Loop_err_ret_exit_placed _ M A lim H x st0
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  conv =>
    arg 4
    rw [v1StateErrFramePlaced, sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro is'
  conv =>
    arg 4
    rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v240
  wp_steps_sync_pool (lsmpl.base 261); wp_reach
  refine SepWPp.call_frame
    (x := (s0.sp - 576#64, s.readReg64 (Reg.gpr 8#5), M.stepEvents evs_pre st0))
    (ret_pc := (blkPl_298).base + 124#64) hFromCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by conv_lhs => dsimp only [decodeErrorFromBudgetSpec]; simp only [arm64_norm, hsp])
    (by exact ⟨hw, hFit⟩)
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcm hrunm hspm
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
  conv =>
    arg 4
    simp only [decodeErrorFromBudgetSpec,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
  apply SepWP.exists_elim; intro evs_f
  apply SepWP.pure_elim; rintro ⟨⟨hve_ne, htrm_eq⟩, hevs_f⟩
  have htrm : sm.v1TraceEq s := ⟨by simpa only [arm64_norm] using htrm_eq,
    by simpa only [arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2⟩
  apply SepWP.fold (v1StateBelow_decodeError_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (v1Loop_err48_join_720 s0.sp) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A.repAlloc x.msgPtr is'') is')
    (by sep_focus)
  wp_steps_sync_pool ((blkPl_298).base + 128#64); wp_reach
  apply SepWPp.weaken_pre
    (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗
      v1StateErrFramePlaced A lim (M.stepEvents (evs_pre ++ evs_f) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; rw [← stepEvents_append_eq]; sep_ac_rfl))
  exact herr_ret hnone
    (hevs_pre.append (SpqrMergeLoopEnv.single (fuel := 0) (spqrIter_of_decodeErrorFrom hevs_f)))
    (by decide : 0 ≤ 4) hve_ne hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])

/-- Shared exit at `+3376`: stores `X21 = err` at `[SP, #240]` (`s0.sp - 576#64`),
calls `DecodeError::push`, reloads `X1 = err`, and jumps to `+128`. -/
theorem v1Loop_push_err_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_pre : List AllocEvent} {R : SepProp}
    {s0 s : State} {err : BitVec 64} {n_err : Nat}
    (hnone : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hevs_pre : SpqrMergeLoopEnv (8 * x.bs.length + 15) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_pre)
    (hFit : FitsEnv M lim (M.stepEvents evs_pre st0)
      (SpqrMergeLoopEnv 1 x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hn : n_err ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx21 : s.readReg64 (Reg.gpr 21#5) = err) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs_pre st0) s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  subst hx21
  have herr_ret := @v1Loop_err_ret_exit_placed _ M A lim H x st0
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  conv =>
    arg 4
    rw [v1StateErrFramePlaced, sepExists_sepConj_left,
      sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro is'
  conv =>
    arg 4
    rw [v1StateBelow_decodeError (s0.sp - 816#64), v1Loop_memRegion_720_split_err1 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v240
  apply sepWP_seg_ls_vm
    (Q := (blkPC_298).rebase (blkPl_298).base (hooksException H))
    blkLib_eq_298 (mid := lsmpl.base 257)
  intro _m_strip
  refine blkPC_298_pairStep_0xd30 (blkPl_298).base _ rfl (by cases s; exact hpc) (by cases s; exact hrun) ?_
  refine blkPC_298_pairStep_0xd38 (blkPl_298).base _ rfl rfl (by cases s; exact hrun) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  wp_reach
  refine SepWPp.call_frame
    (x := (s0.sp - 576#64, s.readReg64 (Reg.gpr 21#5), n_err, M.stepEvents evs_pre st0))
    (ret_pc := (blkPl_298).base + 3412#64) hPushCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by conv_lhs => dsimp only [decodeErrorPushMergeBudgetSpec]; simp only [arm64_norm, hsp])
    (by exact ⟨by omega, FitsEnv.spqrMergeLoop_head (fuel := 0)
      (fun _ hp => spqrIter_of_decodeErrorPush (by omega) hp) hFit⟩)
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcm hrunm hspm
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
  conv =>
    arg 4
    simp only [decodeErrorPushMergeBudgetSpec,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
  apply SepWP.exists_elim; intro evs_p
  apply SepWP.pure_elim; rintro ⟨htrm_eq, hevs_p⟩
  have htrm : sm.v1TraceEq s := ⟨by simpa only [arm64_norm] using htrm_eq,
    by simpa only [arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2⟩
  apply SepWP.fold (v1StateBelow_decodeError_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (Entails.sepExists_intro (P := fun is'' => optProtoInnerStateAt A.repAlloc x.msgPtr is'') is')
    (by sep_focus)
  wp_steps_sync_pool ((blkPl_298).base + 128#64)
  apply SepWP.fold (v1Loop_err1_join_720 s0.sp (s.readReg64 (Reg.gpr 21#5))) (by sep_focus)
  wp_reach
  apply SepWPp.weaken_pre
    (P' := decodeErrorAtStackLen A.repAlloc (s.readReg64 (Reg.gpr 21#5)) (n_err + 1) ∗
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗
      v1StateErrFramePlaced A lim (M.stepEvents (evs_pre ++ evs_p) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; rw [← stepEvents_append_eq]; sep_ac_rfl))
  exact herr_ret hnone
    (hevs_pre.append (SpqrMergeLoopEnv.single (fuel := 0) (spqrIter_of_decodeErrorPush (by omega) hevs_p)))
    (by omega : n_err + 1 ≤ 4) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])

/-- Constructs `V1StateTagContPlaced` at the shared loop latch `+2700` from the
loop-header continuation at `+216`. -/
theorem v1Loop_latch_cont_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_acc : List AllocEvent} {R : SepProp}
    {s0 : State} {k : Nat} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_lt_bs : rest.length < x.bs.length)
    (hevs_acc : SpqrMergeLoopEnv (8 * (x.bs.length - (rest.length + 1))) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc)
    (hFit_rest : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
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
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)) :
    V1StateTagContPlaced A lim H s0 x st0 (M.stepEvents evs_acc st0) R k m rest iwt limit where
  onOk := by
    intro evs_tag m' rest' s' hfield hbound hcap' hrest'_le hevs_tag hpc hrun hsp htr hx21 hregs hinv
    rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    have hevs_acc' : SpqrMergeLoopEnv (8 * (x.bs.length - rest'.length)) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) (evs_acc ++ evs_tag) :=
      (hevs_acc.append hevs_tag).mono_fuel (by omega)
    have hFit_split : FitsEnv M lim (M.stepEvents evs_acc st0)
        (SpqrMergeLoopEnv ((8 * (rest.length - rest'.length) + 8) + (8 * rest'.length + 16)) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) :=
      FitsEnv.spqrMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit_rest
    have hFit' : FitsEnv M lim (M.stepEvents (evs_acc ++ evs_tag) st0)
        (SpqrMergeLoopEnv (8 * rest'.length + 16) x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) := by
      rw [stepEvents_append_eq]
      exact FitsEnv.spqrMergeLoop_split hevs_tag hFit_split
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinv ?_
    conv => arg 4; rw [v1StateLoopPrePlaced]
    wp_steps_sync_pool ((blkPl_298).base + 216#64); wp_reach; intro hinv'
    apply SepWPp.weaken_pre
      (P' := v1StateLoopPrePlaced A lim (M.stepEvents (evs_acc ++ evs_tag) st0) s0 _
        x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced]; rw [← stepEvents_append_eq]; sep_ac_rfl))
    exact hcont_loop (evs_acc ++ evs_tag) m' rest' _ hfield hbound hcap' hrest'_le hevs_acc' hFit'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩ hinv'
  onErr := by
    intro hfield evs_tag s' err n_err hevs_tag hpc hrun hsp htr hx21 herr hn
    have hnone := hnone_of_field_none hfield
    have hcbnz : (err == 0#64) = false := beq_eq_false_iff_ne.mpr herr
    have hevs_pre : SpqrMergeLoopEnv (8 * x.bs.length + 15) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) (evs_acc ++ evs_tag) :=
      (hevs_acc.append hevs_tag).mono_fuel (by omega)
    have hFit_rem : FitsEnv M lim (M.stepEvents (evs_acc ++ evs_tag) st0)
        (SpqrMergeLoopEnv 1 x.bs.length
          (optInnerStatePolyCapBound x.msg.innerState x.bs.length)) := by
      rw [stepEvents_append_eq]
      exact FitsEnv.spqrMergeLoop_split hevs_tag
        (FitsEnv.spqrMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit_rest)
    have hpush := @v1Loop_push_err_exit_placed _ M A lim H hPushCall x st0 (evs_acc ++ evs_tag) R s0
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 3376#64)
    conv => arg 4; rw [v1StateErrFramePlaced]
    wp_steps_sync_pool ((blkPl_298).base + 3376#64); wp_reach
    apply SepWPp.weaken_pre
      (P' := decodeErrorAtStackLen A.repAlloc err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs_acc ++ evs_tag) st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; rw [← stepEvents_append_eq]; sep_ac_rfl))
    exact hpush hnone hevs_pre hFit_rem hn herr hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx21])

/-- Loop exit at `+216` when `cur.length ≤ limit`. -/
theorem v1Loop_le_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_acc : List AllocEvent} {R : SepProp} {s0 s : State}
    {m : V1State} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63) (hbound : OptInnerStatePolyBound cur.length m.innerState)
    (hevs_acc : SpqrMergeLoopEnv (8 * (x.bs.length - cur.length)) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_acc)
    (hFit : FitsEnv M lim (M.stepEvents evs_acc st0)
      (SpqrMergeLoopEnv (8 * cur.length + 16) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length)))
    (hnone_of_lt : cur.length < limit →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = none)
    (hsome_of_eq : cur.length = limit →
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x limit s) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨_hx19, _hx20, _hx22, _hx23, _hx24, _hx25, hx26, _hx27, hx28, _hx29⟩
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    have hok_ret := fun {s' : State} => @v1Loop_ok_ret_exit_placed _ M A lim H x st0 evs_acc R s0 s' m cur
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
    conv =>
      arg 4
      rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
      simp only [sepConj_assoc]
    wp_steps_sync_pool ((blkPl_298).base + 128#64)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre
      (P' := v1StateLoopPrePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, sliceCursorAfter]; sep_ac_rfl))
    exact hok_ret hsome hevs_acc hbound hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hFit_from : FitsEnv M lim (M.stepEvents evs_acc st0) DecodeErrorFromEnv :=
      FitsEnv.spqrMergeLoop_head (fuel := 8 * cur.length + 15) (fun _ => spqrIter_of_decodeErrorFrom) hFit
    have hfrom_err := @v1Loop_from_err_exit_placed _ M A lim H hFromCall x st0 evs_acc R s0
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 112#64)
    conv =>
      arg 4
      rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
      simp only [sepConj_assoc]
    wp_steps_sync_pool ((blkPl_298).base + 112#64)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr cur.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre
      (P' := stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs_acc st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; sep_ac_rfl))
    exact hfrom_err hnone (hevs_acc.mono_fuel (by omega)) hFit_from
      (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
