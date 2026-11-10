/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStep
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
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
# Budget-Threaded Exit and Skip Step Lemmas for `unchunked::EkSentCt1Received::merge` (Block `311`)

`RustCliAllocBudget`-threaded loop-header and error-exit separation-logic bundles, shared
return/error exits, and `skip_field` and tag-1 wire-type error step lemmas for
`prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (Block `311`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_311 blkPl_311 lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix SkipFieldGhost pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (WppPost setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Drop
  (protoUnchunkedEkSentCt1ReceivedAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedEkSentCt1ReceivedMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro bv64_add_zero_u bv64_sub_zero_u codecWireTypeToProto
   iwt_cbnz_true_of_ne_varint_u memRegion8_memRegion40_entails_48_112 memRegion_48_split_112
   memRegion_48_wtErr112 pointsTo64_memRegion40_entails_48_112
   protoUnchunkedEkSentCt1ReceivedAt_entails_exists protoUnchunkedEkSentCt1ReceivedCapAt
   protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists protoUnchunkedEkSentCt1ReceivedCapAt_mono
   stackAt_unchunkedMerge unchunkedMergeBelow unchunkedMergeBelow_eq_authMergeStack
   unchunkedMergeBelow_err unchunkedMergeBelow_err_entails unchunkedOwnStack
   wtErr112_entails_memRegion40)
open CryptoVerification.SpqrV1.Varint (skipField3Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeLoopEnv UnchunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv
   decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeErrorFromEnv_to_spqr decodeErrorPushEnv_to_spqr
   fitsEnv_decodeErrorFrom_of_spqr fitsEnv_decodeErrorPush_of_spqr fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc pool_spqr_mono
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedEkSentCt1ReceivedMergeOwnSpec unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv)
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

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-- Weaken a bare `subroutine_ok` contract to `withLsCodeRoLoaded`. -/
theorem subroutine_ok_withLsCodeRoLoaded_of_bare {α : Type} {prog : Program}
    {pl : Obj.MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ hpan => hpan)

/-! ## 1. Saved-Register Bundle, Loop Invariant, and Error Frame -/

/-- Callee-saved register spill slots in the 112-byte stack frame of `EkSentCt1Received::merge`. -/
def ekSentSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    memRegion (sp - 40#64) 8 ∗
    ((sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem stackAt_unchunkedMerge_epilogue (sp : BitVec 64) (s0 : State) :
    unchunkedMergeBelow sp ∗ memRegion (sp - 112#64) 48 ∗ ekSentSavedRegs sp s0 ⊢
      stackAt sp unchunkedOwnStack := by
  rw [stackAt_unchunkedMerge sp, ekSentSavedRegs]
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 19#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 20#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 21#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 22#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 23#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 30#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 29#5)))
  sep_entail

/-- Budget-threaded loop-header separation-logic bundle at `+0x098` (`(blkPl_311).base + 152#64`). -/
def ekSentLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Unchunked.EkSentCt1Received) (bs cur : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st (4 * (bs.length - cur.length)) bs.length 0 s ∗
    protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 112#64) 48 ∗
    ekSentSavedRegs s0.sp s0 ∗
    unchunkedMergeBelow s0.sp

/-- Budget-threaded error-exit separation-logic bundle at fuel `f` (`f ≤ 4 * bs.length + 8`). -/
def ekSentErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (f : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st f bs.length 0 s ∗
    (∃∗ m' : V1State.Unchunked.EkSentCt1Received,
      protoUnchunkedEkSentCt1ReceivedAt A.repAlloc msgPtr m') ∗
    (bufRef ↦₆₄ slot) ∗
    memRegion slot 16 ∗
    (ptr ↦ₛ bs) ∗
    ekSentSavedRegs s0.sp s0

private theorem decodeErrorAtStackLen_entails_le2 (A : CryptoVerification.RustHeap.RustAlloc)
    (err : BitVec 64) {n : Nat} (hn : n ≤ 2) :
    decodeErrorAtStackLen A err n ⊢
      ∃∗ n' : Nat, ⌜n' ≤ 2⌝ ∗ decodeErrorAtStackLen A err n' :=
  Entails.trans (Entails.pure_right hn (Entails.refl _))
    (Entails.sepExists_intro (P := fun n' => ⌜n' ≤ 2⌝ ∗ decodeErrorAtStackLen A err n') n)

private theorem ekSent_err_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : UnchunkedEkSentCt1ReceivedMergeGhost)
    (s0 s sf : State) (m' : V1State.Unchunked.EkSentCt1Received) (err : BitVec 64)
    (n f : Nat) (evs : List AllocEvent)
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hvm : VmPreserved s sf) (hf : f ≤ 4 * x.bs.length + 8) (hn : n ≤ 2) (herr : err ≠ 0#64)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = err)
    (hevs : SpqrMergeLoopEnv f x.bs.length 0 evs) :
    stackAt s0.sp unchunkedOwnStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (protoUnchunkedEkSentCt1ReceivedAt A.repAlloc x.msgPtr m' ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) ⊢
    (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim).post (x, st) s0 sf := by
  dsimp only [unchunkedEkSentCt1ReceivedMergeOwnSpec, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv,
    UnchunkedEkSentCt1ReceivedMergePostEnv]
  rw [hnone, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp unchunkedOwnStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (protoUnchunkedEkSentCt1ReceivedAt A.repAlloc x.msgPtr m' ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp unchunkedOwnStack ∗
          (decodeErrorAtStackLen A.repAlloc err n ∗
            (protoUnchunkedEkSentCt1ReceivedAt A.repAlloc x.msgPtr m' ∗
              (memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)))))))) ?_
  exact sepConj_mono_right (sepConj_mono (pool_spqr_mono A lim st hvm hf hevs)
    (sepConj_mono_right (Entails.pure_right herr
      (sepConj_mono (decodeErrorAtStackLen_entails_le2 A.repAlloc err hn)
        (sepConj_mono_left
          (protoUnchunkedEkSentCt1ReceivedAt_entails_exists A.repAlloc x.msgPtr m'))))))

private theorem unchunkedMergeBelow_eq_skipField3_97 (sp : BitVec 64) :
    unchunkedMergeBelow sp = stackAt (sp - 112#64) (skipField3Stack 97) := rfl

/-! ## 2. Shared Placed Exit & Skip / Tag-1 Error Step Lemmas (Block `311`) -/

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_311).base

/-- Shared error return from `+0x078` (`(blkPl_311).base + 120#64`) when `x1 = err ≠ 0#64`
owns `decodeErrorAtStackLen A.repAlloc err n` with `n ≤ 2`. -/
theorem ekSent_ret_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f ≤ 4 * x.bs.length + 8)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [ekSentErrFrame, spqrPoolAt, ekSentSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm,
      arm64_norm, hsp])
    apply SepWP.exists_elim; intro m'
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_unchunkedMerge_epilogue s0.sp s0)
      (by unfold ekSentSavedRegs; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx24, hx25, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (ekSent_err_exit_entails A lim st x s0 s _ m' err n f evs hnone hvm hf hn herr
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx1]) hevs)

/-- Specialization of `ekSent_ret_err_exit_placed` at stack length `n = 0`. -/
theorem ekSent_err0_ret_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {f : Nat}
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f ≤ 4 * x.bs.length + 8)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_ret_err_exit_placed hnone hf (by decide : 0 ≤ 2) herr hsp_align hpc hrun hsp htr hx1 hcs

/-- Shared exit from `+0x06c` (`(blkPl_311).base + 108#64`): calls `DecodeError::from` (Block `261`)
and exits via `+0x078` (`+ 120#64`). -/
theorem ekSent_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ w) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hret := @ekSent_ret_err_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [ekSentErrFrame, spqrPoolAt, unchunkedMergeBelow_err s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro m'
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 112#64, w, M.stepEvents evs st))
      (ret_pc := entry + 116#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
      (And.intro hw (fitsEnv_decodeErrorFrom_of_spqr hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hspm hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 120#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorFromBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_f
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, htrm⟩, hevs_f⟩
      apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold (memRegion8_memRegion40_entails_48_112 s0.sp) (by sep_focus)
      apply SepWP.fold
        (protoUnchunkedEkSentCt1ReceivedAt_entails_exists A.repAlloc x.msgPtr m')
        (by sep_focus)
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
          memRegion (s0.sp - 112#64) 48 ∗
          unchunkedMergeBelow s0.sp ∗
          ekSentErrFrame A lim st (f + 1) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ekSentErrFrame]; sep_entail)
      exact hret hnone hf (by decide : 0 ≤ 2) hsm0 hsp_align
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
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ekSent_from_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ w) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_from_err_exit_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_bare hFromCall)
    hFit hnone hf hw hsp_align hpc hrun hsp htr hcs

/-- Shared exit from `+0x290` (`(blkPl_311).base + 656#64`): calls `DecodeError::push` (Block `257`)
on `(s0.sp - 112#64, err, n)` with `n ≤ 1`, then branches to `+0x078` (`+ 120#64`). -/
theorem ekSent_push_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hn : n ≤ 1) (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 656#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 112#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hret := @ekSent_ret_err_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 257)
  by_vm_steps
    (conv => arg 4; rw [ekSentErrFrame, spqrPoolAt, unchunkedMergeBelow_err s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro m'
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 112#64, err, n, M.stepEvents evs st))
      (ret_pc := entry + 660#64) hPushCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorPushMergeBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx0]; try rfl)
      (And.intro (by omega) (fitsEnv_decodeErrorPush_of_spqr (by omega) hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hspm hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 120#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorPushMergeBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_p
      apply SepWP.pure_elim; rintro ⟨htrm, hevs_p⟩
      apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold
        (protoUnchunkedEkSentCt1ReceivedAt_entails_exists A.repAlloc x.msgPtr m')
        (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
          hevs (decodeErrorPushEnv_to_spqr (by omega) hevs_p))
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsTo64_memRegion40_entails_48_112 s0.sp err) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc err (n + 1) ∗
          memRegion (s0.sp - 112#64) 48 ∗
          unchunkedMergeBelow s0.sp ∗
          ekSentErrFrame A lim st (f + 1) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ekSentErrFrame]; sep_entail)
      exact hret hnone hf (by omega : n + 1 ≤ 2) herr hsp_align
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
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ekSent_push_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hn : n ≤ 1) (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 656#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 112#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_push_err_exit_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    hFit hnone herr hn hf hsp_align hpc hrun hsp htr hx0 hcs

/-- Step lemma for unknown field tags (`tag ∉ {1, 2, 3, 4}`) at `+0x13c` (`(blkPl_311).base + 316#64`):
calls `skipField3Spec` (Block `263`) at depth `97`. -/
theorem ekSent_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
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
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩
  have herr0_exit := @ekSent_err0_ret_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [ekSentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_eq_skipField3_97 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 328#64) hSkipCall
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
      apply sepWPpLscro_of_vm (mid := entry + 120#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp, ← unchunkedMergeBelow_eq_skipField3_97])
        have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr rest.length m)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
            hevs (skipFieldEnv_to_spqr hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 112#64) 48 ∗
            unchunkedMergeBelow s0.sp ∗
            ekSentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ekSentErrFrame]; sep_entail)
        exact herr0_exit hnone (by omega) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          hsm0
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some rest' =>
      have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
      apply sepWPpLscro_of_vm (mid := entry + 152#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp, ← unchunkedMergeBelow_eq_skipField3_97])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold
          (protoUnchunkedEkSentCt1ReceivedCapAt_mono A.repAlloc x.msgPtr m hrest'_le)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 4 * (x.bs.length - rest.length) ≤ 4 * (x.bs.length - rest'.length))
            hevs (skipFieldEnv_eq_nil_of_some hsf hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ekSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
          (by dsimp only [ekSentLoopPre]; sep_entail)
        exact hcont rest' _ hsf
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

theorem ekSent_skip_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263)
      (skipField3Spec A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
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
        (ekSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
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
  ekSent_skip_step_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_bare hSkipCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_sf hcont
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hcs

/-- Tag-1 error exit from `+0x228` (`(blkPl_311).base + 552#64`): spills `X8 = err` to `[SP]`
and steps to `ekSent_push_err_exit_cl_placed` at `+ 656#64`. -/
theorem ekSent_tag1_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 552#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hpush_exit := @ekSent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := entry + 580#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
  rw [ekSentErrFrame, ← spqrPoolAt_of_vmPreserved hvm0, ← ekSentErrFrame]
  apply sepWPpLscro_of_vm (mid := entry + 656#64)
  by_vm_steps
    (conv => arg 4; rw [memRegion_48_split_112 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
    rw [ekSentErrFrame, ← spqrPoolAt_of_vmPreserved hvm1]
    refine SepWPpLscro.weaken_pre ?_
      (hpush_exit hFit hnone herr (Nat.zero_le 1) hf hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hsp])
        ⟨by simp only [arm64_norm, wp_norm, hx24],
         by simp only [arm64_norm, wp_norm, hx25],
         by simp only [arm64_norm, wp_norm, hx26],
         by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩)
    dsimp only [ekSentErrFrame]; sep_entail

theorem ekSent_tag1_push_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 552#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_tag1_push_exit_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    hFit hnone herr hf hsp_align hpc hrun hsp htr hx8 hcs

/-- Tag-1 wire-type error step from `+0x154` (`(blkPl_311).base + 340#64`) when `iwt ≠ .varint`:
calls `DecodeError::from` (`0x8000000000000006#64`) and `DecodeError::push`. -/
theorem ekSent_tag1_wt_err_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hiwt : iwt ≠ .varint)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_311).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @ekSent_tag1_push_exit_cl_placed _ M A lim H hPushCall x st R s0
  have hcbnz := iwt_cbnz_true_of_ne_varint_u hiwt
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [ekSentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr112 s0.sp, unchunkedMergeBelow_err s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (wtErr112_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 112#64, 0x8000000000000006#64, M.stepEvents evs st))
      (ret_pc := entry + 548#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
      (And.intro (by decide : KindNoHeap 0x8000000000000006#64)
        (fitsEnv_decodeErrorFrom_of_spqr (by omega) hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 552#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorFromBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_f
      apply SepWP.pure_elim; rintro ⟨⟨hve_ne, htrm⟩, hevs_f⟩
      apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold (memRegion8_memRegion40_entails_48_112 s0.sp) (by sep_focus)
      apply SepWP.fold
        (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length))
        (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold
        (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A.repAlloc x.msgPtr rest.length m)
        (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
          (Nat.le_refl (4 * (x.bs.length - rest.length) + 1))
          hevs (decodeErrorFromEnv_to_spqr hevs_f))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
          memRegion (s0.sp - 112#64) 48 ∗
          unchunkedMergeBelow s0.sp ∗
          ekSentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
            x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ekSentErrFrame]; sep_entail)
      exact htag1_push hFit hnone hve_ne (by omega) hsp_align
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
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ekSent_tag1_wt_err_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (UnchunkedEkSentCt1ReceivedMergeEnv x))
    (hiwt : iwt ≠ .varint)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_311).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ekSent_tag1_wt_err_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_bare hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    hFit hiwt hsp_align hrest_le hrest_suf hnone hpc hrun hsp htr hx0 hcs

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux
