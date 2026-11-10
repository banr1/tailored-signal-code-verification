/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Step Helpers for `Chunked.EkSentCt1Received::merge` (Block `309`)

Provides budget-threaded error exits (`err0_ret`, `from_err`, `push_err`), `Option` field
initialization helpers (`tag1_init`, `tag2_init`), `loop_le_exit`, and `decode_key_step` on
Block `309` with `withLsCodeRoLoaded lsmpl` callees.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix
   key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.ProtoRepr
  (optPolynomialDecoderPBAt polynomialDecoderPBAt vecVecU8At
   vecVecU8At_eq_exists_pin vecVecU8Buf vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (cap_add_one_beq_zero_false cap_add_one_bne_zero_true
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedEkSentCt1ReceivedMergeGhost ChunkedHighCalleeSaved ChunkedLoopRegs SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedBelow chunkedBelow_err chunkedBelow_err_entails
   chunkedBelow_leaf chunkedBelow_leaf_entails chunkedEkSentCt1ReceivedMerge_fnOff
   chunkedEkSentCt1ReceivedPBAt chunkedEkSentCt1ReceivedPBAt_entails_exists
   chunkedEkSentCt1ReceivedPBCapAt chunkedEkSentCt1ReceivedPBCapAt_entails_pb
   chunkedEkSentCt1ReceivedPBCapAt_mono chunkedMergeStack chunkedSavedRegs
   cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt codecWireTypeToProto
   default_ekSentCt1Received_entails_cap default_polyDecoder_entails_pb
   memRegion8_memRegion40_entails_48_128 memRegion_48_split2_128 memRegion_48_split_128
   memRegion_ekSentCt1Received_none_split memRegion_polyDecoder_none_split mergeLoopBin
   mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_decodeVarint_none
   mergeLoopBin_of_key_ge mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   optUnchunkedEkSentCt1ReceivedPBCapAt pointsTo64_memRegion32_entails_40_128
   pointsTo64_memRegion40_entails_48_128 protoPrefixStep_chunked_ekSentCt1Received_mergeField
   stackAt_chunkedMerge unchunkedEkSentCt1ReceivedPBCapAt vecU8At_eq_header_sep_buf vecU8Buf
   vecU8Buf_entails_cap_lt vecVecU8Buf_entails_cap_lt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_309 blkPl_309)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedEkSentCt1ReceivedMergeEnv ChunkedEkSentCt1ReceivedMergePostEnv
   SpqrMergeLoopEnv chunkedEkSentCt1ReceivedMergeSpec
   chunkedEkSentCt1ReceivedMergeSpecOfEnv decodeErrorPushMergeBudgetSpec
   ekSentCt1ReceivedPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeErrorFromEnv_to_spqr
   decodeErrorPushEnv_to_spqr decodeVarint2Env_eq_nil_of_some
   decodeVarint2Env_to_spqr fitsEnv_decodeErrorFrom_of_spqr
   fitsEnv_decodeErrorPush_of_spqr fitsEnv_decodeVarint2_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc pool_spqr_mono
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedEkSentCt1ReceivedMerge_fnOff

/-- Budget-threaded error-exit separation-logic bundle at fuel `f` (`f ≤ 6 * bs.length + 12`). -/
def ekSentCt1ReceivedErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (f polyBound : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.EkSentCt1Received) (bs : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st f bs.length polyBound s ∗
    chunkedSavedRegs s0 ∗ chunkedEkSentCt1ReceivedPBAt A.repAlloc msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs)

/-- Budget-threaded loop-head (`+192#64`) separation-logic bundle for `Chunked.EkSentCt1Received::merge`. -/
def ekSentCt1ReceivedLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.EkSentCt1Received) (bs cur : List (BitVec 8))
    (polyBound : Nat) : SepProp :=
  spqrPoolAt A lim st (6 * (bs.length - cur.length)) bs.length polyBound s ∗
    chunkedEkSentCt1ReceivedPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0

theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

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
  exact Entails.of_eq (by sep_ac_rfl)

private theorem decodeErrorWith_le3_eks1r (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 3) :
    decodeErrorAtStackLen A e n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k :=
  Entails.trans (Entails.pure_right hn (Entails.refl _))
    (Entails.sepExists_right n (Entails.refl _))

private theorem eks1r_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChunkedEkSentCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.EkSentCt1Received) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrMergeLoopEnv (6 * (x.bs.length - cur.length)) x.bs.length
      (ekSentCt1ReceivedPolyCapBound x) evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (chunkedEkSentCt1ReceivedMergeSpec A lim).post (x, st) s0 sf := by
  dsimp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv,
    ChunkedEkSentCt1ReceivedMergePostEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (pool_spqr_mono A lim st hvm (Nat.le_refl _) hevs)
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem eks1r_err_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChunkedEkSentCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.EkSentCt1Received) (err : BitVec 64)
    (n f : Nat) (evs : List AllocEvent)
    (hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hvm : VmPreserved s sf) (hf : f ≤ 6 * x.bs.length + 12) (hn : n ≤ 3) (herr : err ≠ 0#64)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = err)
    (hevs : SpqrMergeLoopEnv f x.bs.length (ekSentCt1ReceivedPolyCapBound x) evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (chunkedEkSentCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) ⊢
    (chunkedEkSentCt1ReceivedMergeSpec A lim).post (x, st) s0 sf := by
  dsimp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv,
    ChunkedEkSentCt1ReceivedMergePostEnv]
  rw [hnone, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (chunkedEkSentCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (decodeErrorAtStackLen A.repAlloc err n ∗
            (chunkedEkSentCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
              (memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)))))))) ?_
  exact sepConj_mono_right (sepConj_mono (pool_spqr_mono A lim st hvm hf hevs)
    (sepConj_mono_right (Entails.pure_right herr
      (sepConj_mono (decodeErrorWith_le3_eks1r A.repAlloc err hn)
        (sepConj_mono_left (chunkedEkSentCt1ReceivedPBAt_entails_exists A.repAlloc x.msgPtr m))))))

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_309).base

theorem ekSentCt1Received_err0_ret_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.EkSentCt1Received} {s : State} {err : BitVec 64} {n f : Nat}
    (hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f ≤ 6 * x.bs.length + 12) (hn : n ≤ 3) (herr : err ≠ 0#64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_309).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedBelow s0.sp ∗
        ekSentCt1ReceivedErrFrame A lim st f (ekSentCt1ReceivedPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [ekSentCt1ReceivedErrFrame, spqrPoolAt, chunkedSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt s0.sp chunkedMergeStack ∗
        (decodeErrorAtStackLen A.repAlloc err n ∗
          (chunkedEkSentCt1ReceivedPBAt A.repAlloc x.msgPtr m ∗
            ((x.bufRef ↦₆₄ x.slot) ∗
              (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s)))))
      by sep_ac_rfl))
      (eks1r_err_exit_entails A lim st x s0 s _ m err n f evs hnone hvm hf hn herr
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx1]) hevs)

theorem ekSentCt1Received_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.EkSentCt1Received} {s : State} {w v_stk0 : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_309).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = w)
    (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗
        ekSentCt1ReceivedErrFrame A lim st f (ekSentCt1ReceivedPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  have herr0 := @ekSentCt1Received_err0_ret_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [chunkedBelow_err s0.sp, ekSentCt1ReceivedErrFrame, spqrPoolAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, w, M.stepEvents evs st))
      (ret_pc := entry + 120#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx8]; try rfl)
      (And.intro hw (fitsEnv_decodeErrorFrom_of_spqr hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx26, hx27, hx28, hvregs]
      at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 124#64)
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
          ekSentCt1ReceivedErrFrame A lim st (f + 1) (ekSentCt1ReceivedPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [ekSentCt1ReceivedErrFrame]; sep_entail)
      exact herr0 hnone hf (by decide : 0 ≤ 3) hsm0 hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ekSentCt1Received_push_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.EkSentCt1Received} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (herr : err ≠ 0#64) (hn : n ≤ 2) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_309).base + 504#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ekSentCt1ReceivedErrFrame A lim st f (ekSentCt1ReceivedPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  have herr0 := @ekSentCt1Received_err0_ret_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 257)
  by_vm_steps
    (conv => arg 4; rw [chunkedBelow_err s0.sp, ekSentCt1ReceivedErrFrame, spqrPoolAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, err, n, M.stepEvents evs st))
      (ret_pc := entry + 508#64) hPushCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorPushMergeBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx0]; try rfl)
      (And.intro (by omega : n < 2 ^ 32) (fitsEnv_decodeErrorPush_of_spqr (by omega) hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx26, hx27, hx28, hvregs]
      at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 124#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorPushMergeBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_p
      apply SepWP.pure_elim; rintro ⟨htrm, hevs_p⟩
      apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
          hevs (decodeErrorPushEnv_to_spqr (by omega : n ≤ 4) hevs_p))
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsTo64_memRegion40_entails_48_128 s0.sp err) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc err (n + 1) ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
          ekSentCt1ReceivedErrFrame A lim st (f + 1) (ekSentCt1ReceivedPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [ekSentCt1ReceivedErrFrame]; sep_entail)
      exact herr0 hnone hf (by omega : n + 1 ≤ 3) herr hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ekSentCt1Received_tag1_init_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {rest : List (BitVec 8)}
    {v0 : BitVec 64} {limit : Nat}
    (hpc : s.pc = (blkPl_309).base + 308#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_309).base + 340#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s'
        (unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length (m.uc.getD default) ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) m.receivingCt2 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ekSentCt1ReceivedPolyCapBound x) s' ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (ekSentCt1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ekSentCt1ReceivedPolyCapBound x))
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases huc : m.uc with _ | u
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 340#64)
    by_vm_steps
      (conv => arg 4; rw [ekSentCt1ReceivedLoopPre, chunkedEkSentCt1ReceivedPBCapAt, huc,
        optUnchunkedEkSentCt1ReceivedPBCapAt, memRegion_ekSentCt1Received_none_split x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w48
      apply SepWP.exists_elim; intro w40; apply SepWP.exists_elim; intro w32
      apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w16
      apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_ekSentCt1Received_entails_cap A.repAlloc x.msgPtr rest.length) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length default ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) m.receivingCt2 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ekSentCt1ReceivedPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.weaken_pre
      (P' := unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length u ∗
        optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) m.receivingCt2 ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
          (ekSentCt1ReceivedPolyCapBound x) s ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
      (by rw [ekSentCt1ReceivedLoopPre, chunkedEkSentCt1ReceivedPBCapAt, huc, optUnchunkedEkSentCt1ReceivedPBCapAt];
          exact Entails.of_eq (by sep_ac_rfl))
    apply sepWPpLscro_of_vm (mid := entry + 340#64)
    by_vm_steps
      (conv => arg 4; rw [unchunkedEkSentCt1ReceivedPBCapAt])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro cap_ct1; apply SepWP.exists_elim; intro ptr_ct1
      apply SepWP.exists_elim; intro cap_dk; apply SepWP.exists_elim; intro ptr_dk
      apply SepWP.pure_elim; intro hcap_dk
      (conv => arg 4; rw [vecU8At_eq_header_sep_buf A.repAlloc x.msgPtr cap_dk ptr_dk u.dk, vecHeader])
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.fold (vecU8Buf_entails_cap_lt A.repAlloc cap_dk ptr_dk u.dk) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_dk : (x.msgPtr ↦₆₄ cap_dk) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr_dk) ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
          vecU8Buf A.repAlloc cap_dk ptr_dk u.dk ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc x.msgPtr cap ptr u.dk) := by
        refine Entails.trans ?_ (Entails.sepExists_right cap_dk (Entails.sepExists_right ptr_dk (Entails.refl _)))
        refine Entails.pure_right hcap_dk ?_
        rw [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl)
      have hfold_ct1 : ⌜BytesMergeCapOk cap_ct1 rest.length⌝ ∗
          vecU8At A.repAlloc (x.msgPtr + 24#64) cap_ct1 ptr_ct1 u.ct1 ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc (x.msgPtr + 24#64) cap ptr u.ct1) :=
        Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 (Entails.refl _))
      apply SepWP.fold hfold_dk (by sep_focus)
      apply SepWP.fold hfold_ct1 (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length u ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) m.receivingCt2 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ekSentCt1ReceivedPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by dsimp only [unchunkedEkSentCt1ReceivedPBCapAt]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

theorem ekSentCt1Received_tag2_init_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {rest : List (BitVec 8)}
    {v0 : BitVec 64} {limit : Nat}
    (hpc : s.pc = (blkPl_309).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_309).base + 284#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s'
        (polynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) (m.receivingCt2.getD default) ∗
          optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ekSentCt1ReceivedPolyCapBound x) s' ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (ekSentCt1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ekSentCt1ReceivedPolyCapBound x))
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hpe : m.receivingCt2 with _ | pe
  · rw [hpe] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 284#64)
    by_vm_steps
      (conv => arg 4; rw [ekSentCt1ReceivedLoopPre, chunkedEkSentCt1ReceivedPBCapAt, hpe,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split (x.msgPtr + 104#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_polyDecoder_entails_pb A.repAlloc (x.msgPtr + 104#64)) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := polynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) default ∗
          optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ekSentCt1ReceivedPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [hpe] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.weaken_pre
      (P' := polynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) pe ∗
        optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
          (ekSentCt1ReceivedPolyCapBound x) s ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
      (by rw [ekSentCt1ReceivedLoopPre, chunkedEkSentCt1ReceivedPBCapAt, hpe, optPolynomialDecoderPBAt];
          exact Entails.of_eq (by sep_ac_rfl))
    apply sepWPpLscro_of_vm (mid := entry + 284#64)
    by_vm_steps
      (conv => arg 4; rw [polynomialDecoderPBAt,
        vecVecU8At_eq_exists_pin A.repAlloc (x.msgPtr + 104#64) pe.pts])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro pin
      (conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc])
      apply SepWP.fold (vecVecU8Buf_entails_cap_lt A.repAlloc pin.cap pin.ptr pe.pts) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_pts : ((x.msgPtr + 104#64) ↦₆₄ pin.cap) ∗
          ((x.msgPtr + 104#64 + 8#64) ↦₆₄ pin.ptr) ∗
          ((x.msgPtr + 104#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗
          vecVecU8Buf A.repAlloc pin.cap pin.ptr pe.pts ⊢
          vecVecU8At A.repAlloc (x.msgPtr + 104#64) pe.pts := by
        rw [vecVecU8At_eq_exists_pin]
        refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
        rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hfold_pts (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := polynomialDecoderPBAt A.repAlloc (x.msgPtr + 104#64) pe ∗
          optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ekSentCt1ReceivedPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by dsimp only [polynomialDecoderPBAt]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

theorem ekSentCt1Received_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedEkSentCt1ReceivedMergeEnv x))
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_309).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (ekSentCt1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (ekSentCt1ReceivedPolyCapBound x))
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply sepWPpLscro_of_ret_vm
    by_vm_steps
      (conv => arg 4; simp only [ekSentCt1ReceivedLoopPre, spqrPoolAt,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedSavedRegs,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        sepConj_pure_left_comm, arm64_norm, hsp])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
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
        by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
      refine Entails.trans (Entails.of_eq (show _ =
        stackAt s0.sp chunkedMergeStack ∗
          (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            ((x.bufRef ↦₆₄ x.slot) ∗
              (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s)))
        by sep_ac_rfl))
        (eks1r_ok_exit_entails A lim st x s0 s _ m cur evs hsome hvm
          (by simp only [arm64_norm, wp_norm, htr])
          (by simp only [arm64_norm, wp_norm]) hevs)
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ekSentCt1Received_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0 m
    apply sepWPpLscro_of_vm (mid := entry + 108#64)
    by_vm_steps
      (conv => arg 4; rw [ekSentCt1ReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, memRegion_48_split_128 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
          chunkedBelow s0.sp ∗
          ekSentCt1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
            (ekSentCt1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [ekSentCt1ReceivedErrFrame]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26],
         by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem ekSentCt1Received_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedEkSentCt1ReceivedMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_309).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s'
        (ekSentCt1ReceivedLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (ekSentCt1ReceivedPolyCapBound x))
        (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_309).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (ekSentCt1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (ekSentCt1ReceivedPolyCapBound x))
      (WppPost (chunkedEkSentCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @ekSentCt1Received_err0_ret_exit_placed _ M A lim H x st R s0 m
  have hfrom_exit := @ekSentCt1Received_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [ekSentCt1ReceivedLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 212#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp, hx19]; try rfl)
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
      have hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_ekSentCt1Received_mergeField hgt_lim hd, Option.map_none]
      apply sepWPpLscro_of_vm (mid := entry + 124#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
          stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
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
            ekSentCt1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length) + 1)
              (ekSentCt1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [ekSentCt1ReceivedErrFrame]; sep_entail)
        exact herr0_exit hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
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
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_chunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge, Option.map_none]
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := entry + 108#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (6 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_128 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
            rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp key
          apply SepWP.fold h40 (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
              chunkedBelow s0.sp ∗
              ekSentCt1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                (ekSentCt1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [ekSentCt1ReceivedErrFrame]; sep_entail)
          exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
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
          have hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_chunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := entry + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
              sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_128 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
              rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp (key &&& 7#64)
            apply SepWP.fold h40 (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
                chunkedBelow s0.sp ∗
                ekSentCt1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                  (ekSentCt1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
              (by dsimp only [ekSentCt1ReceivedErrFrame]; sep_entail)
            exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
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
          · have hnone : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_chunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := entry + 108#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
                stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
                sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_dv
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_entails_pb A.repAlloc x.msgPtr cur.length m) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (6 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
                (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_128 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ((s0.sp - 128#64) ↦₆₄ v_err0) ∗ memRegion (s0.sp - 120#64) 40 ∗
                  chunkedBelow s0.sp ∗
                  ekSentCt1ReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                    (ekSentCt1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
                (by dsimp only [ekSentCt1ReceivedErrFrame]; sep_entail)
              exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
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
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
            apply sepWPpLscro_of_vm (mid := entry + 244#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
                stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
                sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_dv
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
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
                (P' := ekSentCt1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                  (ekSentCt1ReceivedPolyCapBound x))
                (by dsimp only [ekSentCt1ReceivedLoopPre]; sep_entail)
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

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetAux
