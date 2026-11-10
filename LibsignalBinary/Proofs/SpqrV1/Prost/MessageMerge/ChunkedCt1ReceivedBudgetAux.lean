/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# SPQR V1: Budget-Threaded Exit, Skip & Key-Decode Helpers for `Chunked.Ct1Received::merge` (Block `303`)

Proves budget-threaded loop invariants, error exits (`ret_err`, `from_err`, `push_err`),
`skipField`, and `decodeVarint` key-decode step lemmas for `V1State.Chunked.Ct1Received::merge`
(Block `303`) with `withLsCodeRoLoaded lsmpl` callees.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix SkipFieldGhost bv32_zeroExtend_ofNat
   decodeVarint_suffix key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1ReceivedMergeGhost ChunkedHighCalleeSaved ChunkedLoopRegs SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedBelow chunkedBelow_err chunkedBelow_err_entails
   chunkedBelow_leaf chunkedBelow_leaf_entails chunkedBelow_skipField3_98
   chunkedBelow_skipField3_98_entails chunkedCt1ReceivedMerge_fnOff chunkedCt1ReceivedPBAt
   chunkedCt1ReceivedPBAt_entails_exists chunkedCt1ReceivedPBCapAt
   chunkedCt1ReceivedPBCapAt_entails_pb chunkedCt1ReceivedPBCapAt_mono chunkedMergeStack
   chunkedSavedRegs cmp_len_limit_of_gt codecWireTypeToProto
   memRegion8_memRegion40_entails_48_128 memRegion_48_split2_128 memRegion_48_split_128
   mergeLoopBin mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   pointsTo64_memRegion32_entails_40_128 pointsTo64_memRegion40_entails_48_128
   protoPrefixStep_chunked_ct1Received_mergeField stackAt_chunkedMerge)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_303 blkPl_303)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1ReceivedMergeEnv ChunkedCt1ReceivedMergePostEnv SpqrMergeLoopEnv
   chunkedCt1ReceivedMergeSpec chunkedCt1ReceivedMergeSpecOfEnv ct1ReceivedPolyCapBound
   decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeErrorFromEnv_to_spqr decodeErrorPushEnv_to_spqr
   decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeErrorFrom_of_spqr fitsEnv_decodeErrorPush_of_spqr
   fitsEnv_decodeVarint2_of_spqr fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc pool_spqr_mono
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm
   skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr spqrPoolAt spqrPoolAt_of_vmPreserved)
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

theorem subroutine_ok_withLsCodeRoLoaded_of_bare {α : Type} {prog : Program}
    {pl : Obj.MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ hpan => hpan)

/-! ## 1. Stack Epilogue, Loop Invariant, and Error Frame -/

theorem stackAt_chunkedMerge_epilogue (s0 : State) :
    chunkedBelow s0.sp ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedSavedRegs s0 ⊢
      stackAt s0.sp chunkedMergeStack := by
  rw [stackAt_chunkedMerge s0.sp, chunkedSavedRegs]
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x19))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x20))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x21))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x22))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x23))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x24))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x25))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x30))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x29))
  sep_entail

private theorem decodeErrorAtStackLen_entails_le3 (A : RustAlloc) (err : BitVec 64)
    {n : Nat} (hn : n ≤ 3) :
    decodeErrorAtStackLen A err n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A err k := by
  refine Entails.trans ?_ (Entails.sepExists_intro n)
  exact Entails.pure_right hn (Entails.refl _)

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-- Budget-threaded loop-header separation-logic bundle at `+192#64` (`(blkPl_303).base + 192#64`). -/
def ct1ReceivedLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct1Received) (bs cur : List (BitVec 8)) (polyBound : Nat) : SepProp :=
  spqrPoolAt A lim st (6 * (bs.length - cur.length)) bs.length polyBound s ∗
    chunkedCt1ReceivedPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0

/-- Budget-threaded error-exit separation-logic bundle at fuel `f` (`f ≤ 6 * bs.length + 12`). -/
def ct1ReceivedErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (f polyBound : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct1Received) (bs : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st f bs.length polyBound s ∗
    chunkedCt1ReceivedPBAt A.repAlloc msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ chunkedSavedRegs s0

private theorem ct1_err_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChunkedCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.Ct1Received) (err : BitVec 64)
    (n f : Nat) (evs : List AllocEvent)
    (hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hvm : VmPreserved s sf) (hf : f ≤ 6 * x.bs.length + 12) (hn : n ≤ 3) (herr : err ≠ 0#64)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = err)
    (hevs : SpqrMergeLoopEnv f x.bs.length (ct1ReceivedPolyCapBound x) evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (chunkedCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) ⊢
    (chunkedCt1ReceivedMergeSpec A lim).post (x, st) s0 sf := by
  dsimp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv,
    ChunkedCt1ReceivedMergePostEnv]
  rw [hnone, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (chunkedCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (decodeErrorAtStackLen A.repAlloc err n ∗
            (chunkedCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
              (memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)))))))) ?_
  exact sepConj_mono_right (sepConj_mono (pool_spqr_mono A lim st hvm hf hevs)
    (sepConj_mono_right (Entails.pure_right herr
      (sepConj_mono (decodeErrorAtStackLen_entails_le3 A.repAlloc err hn)
        (sepConj_mono_left (chunkedCt1ReceivedPBAt_entails_exists A.repAlloc x.msgPtr m))))))

/-! ## 2. Placed Error Exits, `skipField`, and `decodeVarint` Key-Decode (Block `303`) -/

section Placed

set_option quotPrecheck false in
local notation "blkBase" => (blkPl_303).base

theorem ct1Received_ret_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {err : BitVec 64} {n f : Nat}
    (hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_303).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedBelow s0.sp ∗
        ct1ReceivedErrFrame A lim st f (ct1ReceivedPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [ct1ReceivedErrFrame, spqrPoolAt, chunkedSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm,
      arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (ct1_err_exit_entails A lim st x s0 s _ m err n f evs hnone hvm hf hn herr
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx1]) hevs)

theorem ct1Received_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {w v_stk0 : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_303).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = w) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1ReceivedErrFrame A lim st f (ct1ReceivedPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  have hret := fun {s_err : State} =>
    @ct1Received_ret_err_exit_placed _ M A lim H x st R s0 s_err m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [chunkedBelow_err s0.sp, ct1ReceivedErrFrame, spqrPoolAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, w, M.stepEvents evs st))
      (ret_pc := blkBase + 120#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx8];
          try rfl)
      (And.intro hw (fitsEnv_decodeErrorFrom_of_spqr hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx26, hx27, hx28, hvregs]
      at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := blkBase + 124#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorFromBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_f
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, htrm⟩, hevs_f⟩
      apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold (memRegion8_memRegion40_entails_48_128 s0.sp) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
          hevs (decodeErrorFromEnv_to_spqr hevs_f))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
          ct1ReceivedErrFrame A lim st (f + 1) (ct1ReceivedPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
      exact hret hnone hf (by decide : 0 ≤ 3) hsm0 hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ct1Received_push_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_303).base + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1ReceivedErrFrame A lim st f (ct1ReceivedPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  have hret := fun {s_err : State} =>
    @ct1Received_ret_err_exit_placed _ M A lim H x st R s0 s_err m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 257)
  by_vm_steps
    (conv => arg 4; rw [chunkedBelow_err s0.sp, ct1ReceivedErrFrame, spqrPoolAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, err, n, M.stepEvents evs st))
      (ret_pc := blkBase + 512#64) hPushCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorPushMergeBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx0];
          try rfl)
      (And.intro (by omega) (fitsEnv_decodeErrorPush_of_spqr (by omega) hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx26, hx27, hx28, hvregs]
      at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := blkBase + 124#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorPushMergeBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_p
      apply SepWP.pure_elim; rintro ⟨htrm, hevs_p⟩
      apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
          hevs (decodeErrorPushEnv_to_spqr (by omega) hevs_p))
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsTo64_memRegion40_entails_48_128 s0.sp err) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc err (n + 1) ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
          ct1ReceivedErrFrame A lim st (f + 1) (ct1ReceivedPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
      exact hret hnone hf (by omega : n + 1 ≤ 3) herr hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ct1Received_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_303).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (ct1ReceivedLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
          (ct1ReceivedPolyCapBound x))
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 172#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩
  have hret_err := fun {s_err : State} =>
    @ct1Received_ret_err_exit_placed _ M A lim H x st R s0 s_err m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [ct1ReceivedLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_skipField3_98 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := blkBase + 184#64) hSkipCall
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
    cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
    | none =>
      have hnone := hnone_of_sf hsf
      apply sepWPpLscro_of_vm (mid := blkBase + 124#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr rest.length m) (by sep_focus)
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
            memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
            ct1ReceivedErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
        exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some rest' =>
      have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
      apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (chunkedCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest'_le) (by sep_focus)
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
          (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
            (ct1ReceivedPolyCapBound x))
          (by dsimp only [ct1ReceivedLoopPre]; sep_entail)
        exact hcont rest' _ hsf
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

theorem ct1Received_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.Ct1Received.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_303).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (ct1ReceivedLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (ct1ReceivedPolyCapBound x))
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  let x_dv : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, curPtr, cur⟩
  have hret_err := fun {s_err : State} =>
    @ct1Received_ret_err_exit_placed _ M A lim H x st R s0 s_err m
  have hfrom_exit := fun {s_err : State} =>
    @ct1Received_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0 s_err m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [ct1ReceivedLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_dv, M.stepEvents evs st))
      (ret_pc := blkBase + 212#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp,
              stackAt_decodeVarint2_raw_eq])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hcur_lt,
        fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hd : decodeVarint cur with
    | none =>
      have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hres_cur,
          mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_ct1Received_mergeField hgt_lim hd,
          Option.map_none]
      apply sepWPpLscro_of_vm (mid := blkBase + 124#64)
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
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - cur.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
            ct1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length) + 1)
              (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
        exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
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
      · have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hres_cur,
            mergeLoopBin_of_key_ge protoPrefixStep_chunked_ct1Received_mergeField hgt_lim hd hk_ge,
            Option.map_none]
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := blkBase + 108#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
            stackAt_decodeVarint2_raw_eq,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; intro hsm01
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          rcases hsm01 with ⟨hsm0, hsm1⟩
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m)
            (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (6 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
            memRegion_48_split2_128 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold
            (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
            (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢
              memRegion (s0.sp - 120#64) 40 := by
            rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp key
          apply SepWP.fold h40 (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
              chunkedBelow s0.sp ∗
              ct1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
          exact hfrom_exit hFit hnone (by omega)
            (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hres_cur,
              mergeLoopBin_of_wt_none protoPrefixStep_chunked_ct1Received_mergeField hgt_lim hd hk_ge hwt,
              Option.map_none]
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := blkBase + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
              stackAt_decodeVarint2_raw_eq,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_dv
            wp_focus_pure; intro hsm01
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_dv
            rcases hsm01 with ⟨hsm0, hsm1⟩
            (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
            apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m)
              (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
              memRegion_48_split2_128 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps
            apply SepWP.fold
              (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
              (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢
                memRegion (s0.sp - 120#64) 40 := by
              rw [bv_sub_add_lit s0.sp 128 8]
              exact pointsTo64_memRegion32_entails_40_128 s0.sp (key &&& 7#64)
            apply SepWP.fold h40 (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
                chunkedBelow s0.sp ∗
                ct1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                  (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
              (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
            exact hfrom_exit hFit hnone (by omega)
              (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr])
              (by simp only [arm64_norm, wp_norm])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone : (mergeMessage V1State.Chunked.Ct1Received.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              rw [hres_cur,
                mergeLoopBin_of_tag_zero protoPrefixStep_chunked_ct1Received_mergeField
                  hgt_lim hd hk_ge hwt hitag0,
                Option.map_none]
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := blkBase + 108#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
                stackAt_decodeVarint2_raw_eq,
                sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro evs_dv
              wp_focus_pure; intro hsm01
              wp_focus_pure; intro htrm
              wp_focus_pure; intro hevs_dv
              rcases hsm01 with ⟨hsm0, hsm1⟩
              (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
              apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (chunkedCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m)
                (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (6 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
                memRegion_48_split_128 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold
                (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
                (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ((s0.sp - 128#64) ↦₆₄ v_err0) ∗ memRegion (s0.sp - 120#64) 40 ∗
                  chunkedBelow s0.sp ∗
                  ct1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                    (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
                (by dsimp only [ct1ReceivedErrFrame]; sep_entail)
              exact hfrom_exit hFit hnone (by omega)
                (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                (by simp only [arm64_norm, wp_norm])
                ⟨by simp only [arm64_norm, wp_norm, hx26_m],
                 by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
              rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
              omega
            apply sepWPpLscro_of_vm (mid := blkBase + 244#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
                stackAt_decodeVarint2_raw_eq,
                sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro evs_dv
              wp_focus_pure; intro hsm01
              wp_focus_pure; intro htrm
              wp_focus_pure; intro hevs_dv
              rcases hsm01 with ⟨hsm0, hsm1⟩
              (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
              apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (chunkedCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur)
                (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (by omega : 6 * (x.bs.length - cur.length) ≤ 6 * (x.bs.length - rest.length))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                  (ct1ReceivedPolyCapBound x))
                (by dsimp only [ct1ReceivedLoopPre]; sep_entail)
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
                ⟨by simp only [arm64_norm, wp_norm, hx23_m],
                 by simp only [arm64_norm, wp_norm, hx24_m],
                 by simp only [arm64_norm, wp_norm, hx25_m],
                 ⟨by simp only [arm64_norm, wp_norm, hx26_m],
                  by simp only [arm64_norm, wp_norm, hx27_m],
                  by simp only [arm64_norm, wp_norm, hx28_m],
                  by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
