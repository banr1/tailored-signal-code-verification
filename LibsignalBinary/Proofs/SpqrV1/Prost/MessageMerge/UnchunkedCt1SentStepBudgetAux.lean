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
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStep
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Shared Budget Combinators & Exit Lemmas for `Unchunked.Ct1Sent::merge` (Block `312`)

Provides the 112-byte saved-register epilogue fold, `BytesMergeEnv` ↔ `SpqrMergeLoopEnv` framing
helpers, budget-threaded loop/error frames (`ct1SentLoopPre`, `ct1SentErrFrame`), and Block `312`
error-exit lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl blkPC_312 blkPl_312)
open CryptoVerification.RustHeap
  (RustAlloc vecU8)
open CryptoVerification.LibsignalProtoCodec
  (WireType mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost IsDropSuffix SkipFieldGhost
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1
  (ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (WppPost setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Drop
  (optProtoAuthenticatorAt protoUnchunkedCt1SentAt)
open CryptoVerification.SpqrV1.Varint
  (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro
   bv64_add_zero_u bv64_sub_zero_u codecWireTypeToProto
   ct1Sent_fields_entails_exists ct1Sent_parts_entails_exists
   iwt_cbnz_true_of_ne_varint_u memRegion_48_split_112 memRegion_48_wtErr112
   pointsTo64_memRegion40_entails_48_112
   protoUnchunkedCt1SentCapAt protoUnchunkedCt1SentCapAt_entails_exists protoUnchunkedCt1SentCapAt_mono
   stackAt_unchunkedMerge
   unchunkedMergeBelow unchunkedMergeBelow_err unchunkedMergeBelow_err_entails
   unchunkedOwnStack wtErr112_entails_memRegion40)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (BytesMerge3EnvCore FitsEnv.spqrMergeLoop_bytesHead FitsEnv.spqrMergeLoop_split
   SpqrMergeIterEnv SpqrMergeLoopEnv UnchunkedCt1SentMergeEnv UnchunkedCt1SentMergePostEnv
   decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro
   decodeErrorFromEnv_to_spqr decodeErrorPushEnv_to_spqr
   fitsEnv_decodeErrorFrom_of_spqr fitsEnv_decodeErrorPush_of_spqr fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc pool_spqr_mono
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm
   skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved
   vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedCt1SentMergeOwnSpec unchunkedCt1SentMergeOwnSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
  (skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u

/-! ## 1. Reusable 112-Byte Frame, `withLsCodeRoLoaded`, and `BytesMergeEnv` Helpers -/

theorem subroutine_ok_withLsCodeRoLoaded_of_plain {α : Type} {prog : Program}
    {pl : Obj.MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded] at hpre
    refine Satisfies.of_entails hpre (sepConj_mono_left ?_)
    rw [sepConj_comm]
    exact Entails.pure_left fun _ => Entails.refl _
  exact h.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

theorem fitsEnv_bytesMerge3_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₀ f_tot maxLen polyCapBound : Nat} {x_bm : BytesMergeGhost} {evs₀ : List AllocEvent}
    (hf : f₀ + max 1 (2 * x_bm.bs.length) ≤ f_tot)
    (hbs : x_bm.bs.length ≤ maxLen)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (BytesMergeEnv x_bm) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st)
      (SpqrMergeLoopEnv (max 1 (2 * x_bm.bs.length)) maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  have hcore := FitsEnv.spqrMergeLoop_bytesHead (wt := x_bm.wt) (valCap := x_bm.valCap)
    hbs (Nat.le_refl _) hrem
  exact fun evs hb => hcore evs (by unfold BytesMergeEnv at hb; exact hb)

theorem bytesMergeEnv_to_spqr_err {maxLen polyCapBound : Nat} {x_bm : BytesMergeGhost}
    {evs : List AllocEvent}
    (hmb : mergeBytes x_bm.wt x_bm.bs = none)
    (hb : BytesMergeEnv x_bm evs) :
    SpqrMergeIterEnv maxLen polyCapBound evs :=
  .bytesMergeErr x_bm.wt x_bm.valCap x_bm.bs hmb (by unfold BytesMergeEnv at hb; exact hb)

theorem bytesMergeEnv_to_spqr_ok {maxLen polyCapBound : Nat} {x_bm : BytesMergeGhost}
    {v rest' : List (BitVec 8)} {evs : List AllocEvent}
    (hmb : mergeBytes x_bm.wt x_bm.bs = some (v, rest'))
    (hbs : x_bm.bs.length ≤ maxLen)
    (hb : BytesMergeEnv x_bm evs) :
    SpqrMergeLoopEnv (2 * v.length + 1) maxLen polyCapBound evs := by
  simpa using SpqrMergeLoopEnv.bytesSingle (fuel := 0) (maxLen := maxLen)
    (polyCapBound := polyCapBound) hmb hbs (by unfold BytesMergeEnv at hb; exact hb)

/-- Saved callee-saved register slots `X19..X23, X29, X30` (plus the 8-byte alignment hole at
`sp - 40`) in the 112-byte (`0x70`) stack frame of `Ct1Sent::merge` and `EkSentCt1Received::merge`. -/
def unchunkedSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    memRegion (sp - 40#64) 8 ∗
    ((sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem stackAt_unchunkedMerge_epilogue (sp : BitVec 64) (s0 : State) :
    unchunkedMergeBelow sp ∗ memRegion (sp - 112#64) 48 ∗ unchunkedSavedRegs sp s0 ⊢
      stackAt sp unchunkedOwnStack := by
  rw [stackAt_unchunkedMerge sp]
  unfold unchunkedSavedRegs
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 19#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 20#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 21#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 22#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 23#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 30#5)))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 (Reg.gpr 29#5)))
  exact Entails.of_eq (by sep_ac_rfl)

theorem decodeErrorAtStackLen_entails_le2 (A : RustAlloc) (err : BitVec 64) {n : Nat}
    (hn : n ≤ 2) :
    decodeErrorAtStackLen A err n ⊢ ∃∗ k : Nat, ⌜k ≤ 2⌝ ∗ decodeErrorAtStackLen A err k := by
  refine Entails.trans ?_ (Entails.sepExists_intro n)
  exact Entails.pure_right hn (Entails.refl _)

/-! ## 2. Budget Precondition, Error Frame, and Placed Exits for `Ct1Sent::merge` (Block `312`) -/

/-- Existentially-wrapped `protoUnchunkedCt1SentAt` (kept as a `def` so `simp` does not peel `m'`
during exit instruction stepping). -/
def anyProtoUnchunkedCt1SentAt (A : RustAlloc) (msgPtr : BitVec 64) : SepProp :=
  ∃∗ m' : V1State.Unchunked.Ct1Sent, protoUnchunkedCt1SentAt A msgPtr m'

theorem protoUnchunkedCt1SentCapAt_entails_any (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentCapAt A a n m ⊢ anyProtoUnchunkedCt1SentAt A a :=
  protoUnchunkedCt1SentCapAt_entails_exists A a n m

theorem ct1Sent_parts_entails_any (A : RustAlloc) (a : BitVec 64)
    (hdr es ct1 : List (BitVec 8)) (epoch : BitVec 64) :
    vecU8 A a hdr ∗ vecU8 A (a + 0x18#64) es ∗ vecU8 A (a + 0x30#64) ct1 ∗
      (∃∗ oauth : Option ProtoAuthenticator, optProtoAuthenticatorAt A (a + 0x48#64) oauth) ∗
      ((a + 0x78#64) ↦₆₄ epoch) ⊢ anyProtoUnchunkedCt1SentAt A a :=
  ct1Sent_parts_entails_exists A a hdr es ct1 epoch

theorem ct1Sent_fields_entails_any (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.Ct1Sent) :
    vecU8 A a m.hdr ∗ vecU8 A (a + 0x18#64) m.es ∗ vecU8 A (a + 0x30#64) m.ct1 ∗
      optProtoAuthenticatorAt A (a + 0x48#64) m.auth ∗
      ((a + 0x78#64) ↦₆₄ m.epoch) ⊢ anyProtoUnchunkedCt1SentAt A a :=
  ct1Sent_fields_entails_exists A a m

/-- Budget-threaded loop-header separation-logic bundle at `+0x098` (`entry + 152#64`) of Block `312`. -/
def ct1SentLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Unchunked.Ct1Sent) (bs cur : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st (4 * (bs.length - cur.length)) bs.length 0 s ∗
    protoUnchunkedCt1SentCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 112#64) 48 ∗
    unchunkedSavedRegs s0.sp s0 ∗
    unchunkedMergeBelow s0.sp

/-- Budget-threaded error-exit separation-logic bundle at fuel `f` (`f ≤ 4 * bs.length + 8`). -/
def ct1SentErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (f : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st f bs.length 0 s ∗
    anyProtoUnchunkedCt1SentAt A.repAlloc msgPtr ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
    unchunkedSavedRegs s0.sp s0

private theorem ct1Sent_err_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : UnchunkedCt1SentMergeGhost)
    (s0 s sf : State) (err : BitVec 64) (n f : Nat) (evs : List AllocEvent)
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hvm : VmPreserved s sf) (hf : f ≤ 4 * x.bs.length + 8) (hn : n ≤ 2) (herr : err ≠ 0#64)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = err)
    (hevs : SpqrMergeLoopEnv f x.bs.length 0 evs) :
    stackAt s0.sp unchunkedOwnStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (anyProtoUnchunkedCt1SentAt A.repAlloc x.msgPtr ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) ⊢
    (unchunkedCt1SentMergeOwnSpec A lim).post (x, st) s0 sf := by
  dsimp only [unchunkedCt1SentMergeOwnSpec, unchunkedCt1SentMergeOwnSpecOfEnv,
    UnchunkedCt1SentMergePostEnv, anyProtoUnchunkedCt1SentAt]
  rw [hnone, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (show
    stackAt s0.sp unchunkedOwnStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        ((∃∗ m' : V1State.Unchunked.Ct1Sent, protoUnchunkedCt1SentAt A.repAlloc x.msgPtr m') ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp unchunkedOwnStack ∗
          (decodeErrorAtStackLen A.repAlloc err n ∗
            ((∃∗ m' : V1State.Unchunked.Ct1Sent, protoUnchunkedCt1SentAt A.repAlloc x.msgPtr m') ∗
              (memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)))))) by sep_ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono (pool_spqr_mono A lim st hvm hf hevs)
    (sepConj_mono_right (Entails.pure_right herr
      (sepConj_mono_left (decodeErrorAtStackLen_entails_le2 A.repAlloc err hn)))))

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_312).base

theorem ct1Sent_err0_ret_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f ≤ 4 * x.bs.length + 8)
    (hn : n ≤ 2)
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 120#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [ct1SentErrFrame, spqrPoolAt, unchunkedSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm,
      arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_unchunkedMerge_epilogue s0.sp s0)
      (by unfold unchunkedSavedRegs; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx24, hx25, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (ct1Sent_err_exit_entails A lim st x s0 s _ err n f evs hnone hvm hf hn herr
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx1]) hevs)

theorem ct1Sent_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {kindTag : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hnoheap : KindNoHeap kindTag)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ kindTag) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hret := @ct1Sent_err0_ret_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [unchunkedMergeBelow_err s0.sp, ct1SentErrFrame, spqrPoolAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 112#64, kindTag, M.stepEvents evs st))
      (ret_pc := entry + 116#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
      (And.intro hnoheap (fitsEnv_decodeErrorFrom_of_spqr hf hevs hFit))
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
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_f
      wp_focus_pure; rintro ⟨hsm0, htrm⟩
      wp_focus_pure; intro hevs_f
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
      apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
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
          ct1SentErrFrame A lim st (f + 1) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ct1SentErrFrame]; sep_entail)
      exact hret hnone hf (by decide : 0 ≤ 2) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm]) hsm0
        ⟨by simp only [arm64_norm, wp_norm, hx24_m],
         by simp only [arm64_norm, wp_norm, hx25_m],
         by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ct1Sent_from_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {kindTag : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hnoheap : KindNoHeap kindTag)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ kindTag) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_from_err_exit_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    hFit hnone hf hnoheap hsp_align hpc hrun hsp htr hcs

theorem ct1Sent_push_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (herr : err ≠ 0#64)
    (hn : n ≤ 1)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 112#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hret := @ct1Sent_err0_ret_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 257)
  (conv => arg 4; rw [unchunkedMergeBelow_err s0.sp, ct1SentErrFrame, spqrPoolAt])
  (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
  apply SepWP.exists_elim; intro evs
  apply SepWP.pure_elim; intro hevs
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
  refine call_budget_lscro (x := (s0.sp - 112#64, err, n, M.stepEvents evs st))
    (ret_pc := entry + 716#64) hPushCall
    (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
    (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
    (by simp only [arm64_norm, wp_norm])
    (by dsimp only [decodeErrorPushMergeBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx0]; try rfl)
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
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_p
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_p
    (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
    apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
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
        ct1SentErrFrame A lim st (f + 1) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ct1SentErrFrame]; sep_entail)
    exact hret hnone hf (by omega : n + 1 ≤ 2) hsp_align
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hrunm])
      (by simp only [arm64_norm, wp_norm, hspm])
      (by simp only [arm64_norm, wp_norm, htrm, htr])
      (by simp only [arm64_norm, wp_norm]) herr
      ⟨by simp only [arm64_norm, wp_norm, hx24_m],
       by simp only [arm64_norm, wp_norm, hx25_m],
       by simp only [arm64_norm, wp_norm, hx26_m],
       by simp only [arm64_norm, wp_norm, hx27_m],
       by simp only [arm64_norm, wp_norm, hx28_m],
       by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem ct1Sent_push_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (herr : err ≠ 0#64)
    (hn : n ≤ 1)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 112#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_push_err_exit_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall)
    hFit hnone hf herr hn hsp_align hpc hrun hsp htr hx0 hcs

theorem ct1Sent_tag1_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (herr : err ≠ 0#64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hpush_exit := @ct1Sent_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := entry + 712#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
  apply SepWPpLscro.weaken_pre
    (P' := ((s0.sp - 112#64) ↦₆₄ err) ∗
      decodeErrorAtStackLen A.repAlloc err 0 ∗
      memRegion (s0.sp - 104#64) 40 ∗
      unchunkedMergeBelow s0.sp ∗
      ct1SentErrFrame A lim st f s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [ct1SentErrFrame]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
  exact hpush_exit hFit hnone hf herr (Nat.zero_le 1) hsp_align
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
     by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem ct1Sent_tag1_push_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (herr : err ≠ 0#64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_tag1_push_exit_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall)
    hFit hnone hf herr hsp_align hpc hrun hsp htr hcs

theorem ct1Sent_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 404#64)
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
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩
  have herr0_exit := @ct1Sent_err0_ret_exit_placed _ M A lim H x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [ct1SentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 416#64) hSkipCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [skipField3Spec, x_sf]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, unchunkedMergeBelow, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx1],
        htag_lt,
        by simp only [arm64_norm, wp_norm, hx19],
        by simp only [arm64_norm, wp_norm],
        by decide,
        hrest_lt,
        fitsEnv_skipField_of_spqr (by omega) hevs hFit⟩)
      (by dsimp only [unchunkedMergeBelow, x_sf]; sep_focus) ?_
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
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr rest.length m) (by sep_focus)
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
            ct1SentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
              x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ct1SentErrFrame, unchunkedMergeBelow]; sep_entail)
        exact herr0_exit hnone (by omega) (by decide : 0 ≤ 2) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm]) hsm0
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
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (protoUnchunkedCt1SentCapAt_mono A.repAlloc x.msgPtr m hrest'_le) (by sep_focus)
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
          (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
          (by dsimp only [ct1SentLoopPre, unchunkedMergeBelow]; sep_entail)
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

theorem ct1Sent_skip_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (skipField3Spec A lim))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
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
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 404#64)
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
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_skip_step_cl_placed (subroutine_ok_withLsCodeRoLoaded_of_plain hSkipCall)
    hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_sf hcont
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag1_wt_err_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hiwt : iwt ≠ .varint)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_312).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hcbnz := iwt_cbnz_true_of_ne_varint_u hiwt
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_exit := @ct1Sent_tag1_push_exit_cl_placed _ M A lim H hPushCall x st R s0
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [ct1SentLoopPre, spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr112 s0.sp, unchunkedMergeBelow_err s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (wtErr112_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 112#64, 0x8000000000000006#64, M.stepEvents evs st))
      (ret_pc := entry + 544#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
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
      (conv => arg 4; simp only [decodeErrorFromBudgetSpec, memRegion_48_split_112 s0.sp,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      apply SepWP.exists_elim; intro evs_f
      wp_focus_pure; rintro ⟨hsm0, htrm⟩
      wp_focus_pure; intro hevs_f
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
      apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
      apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr rest.length m) (by sep_focus)
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
        (P' := ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
          decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
          memRegion (s0.sp - 104#64) 40 ∗
          unchunkedMergeBelow s0.sp ∗
          ct1SentErrFrame A lim st (4 * (x.bs.length - rest.length) + 1) s0 _
            x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ct1SentErrFrame]; sep_entail)
      exact htag1_exit hFit hnone (by omega) hsm0 hsp_align
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

theorem ct1Sent_tag1_wt_err_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (decodeErrorPushMergeBudgetSpec M A lim))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hiwt : iwt ≠ .varint)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_312).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  ct1Sent_tag1_wt_err_step_cl_placed
    (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall)
    hFit hiwt hsp_align hrest_le hrest_suf hnone hpc hrun hsp htr hx0 hcs

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
