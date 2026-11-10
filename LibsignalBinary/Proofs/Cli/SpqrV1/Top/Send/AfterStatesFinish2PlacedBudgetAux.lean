/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPolyPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2Placed
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish2
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Auxiliary Drop Callees & Unchunked Field Drops (Block `427`)

Proves relocatable callee bridges for `PolynomialEncoder` and `UnchunkedCt1Sent` drops (Blocks `435`, `436`)
and budget-threaded unchunked field-drop steps (`+6472`, `+7568`, `+7644`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification
  (LibsignalPlacement libsignalSessionCode ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
  (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (V1State)
open CryptoVerification.LibsignalTripleRatchetRepr
  (noneCap)
open CryptoVerification.RustHeap
  (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (auth48HeadersAt auth48HeadersAt_entails_memRegion_48 auth64HeadersAt
   auth64HeadersAt_entails_memRegion_56 auth72HeadersAt cap_add_one_beq_zero_false
   cap_add_two_beq_zero_false none2Cap none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   optProtoAuthenticatorAt_48_none optProtoAuthenticatorAt_48_none_entails_memRegion_48
   optProtoAuthenticatorAt_64_none_entails_memRegion_56 optProtoAuthenticatorAt_72_none
   optProtoAuthenticatorAt_72_none_entails_memRegion_48 optProtoAuthenticatorAt_none
   optProtoAuthenticatorAt_some optProtoUnchunked2Vec_none_entails_memRegion_104
   optProtoUnchunkedCt1SentEkReceivedAt optProtoUnchunkedCt1SentEkReceivedAt_none
   optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
   optProtoUnchunkedCt1SentEkReceivedAt_some optProtoUnchunkedCt2SentAt
   optProtoUnchunkedEkSentCt1ReceivedAt optProtoUnchunkedEkSentCt1ReceivedAt_none
   optProtoUnchunkedEkSentCt1ReceivedAt_some optProtoUnchunkedNoHeaderReceivedAt
   optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56
   protoAuthenticatorAt_entails_dealloc protoUnchunked2VecHeadersAt
   protoUnchunked2VecHeadersAt_entails_memRegion_104' protoUnchunked3VecHeadersAt
   protoUnchunkedCt1SentEkReceivedAt_entails_dealloc protoUnchunkedCt2SentAt
   protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc twoVecHeadersAt
   twoVecHeadersAt_48_eq twoVecHeadersAt_64_eq twoVecHeadersAt_72_eq vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero)
open CryptoVerification.SpqrV1.ProtoRepr
  (v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Top.Send
  (auth72HeadersAt_entails_memRegion_48' extractLsb_hi_append64 extractLsb_lo_append64
   ite_zero32_self ite_zero64_self protoUnchunked3VecHeadersAt_entails_memRegion_128'
   send_stackAt_callee_eq_allocHook spqrSendCalleeStack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPolyPlacedBudget
  (drop_opt_proto_poly_encoder_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlacedBudget
  (drop_opt_proto_unchunked_ct1_sent_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
  (DeallocOkExtPlaced spqrSend_dealloc_sub_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
  (dropOptProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropOptProtoUnchunkedCt1SentSpec)

variable [LibsignalPlacement]

private theorem send_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
attribute [local simp, local arm64_norm, local wp_norm]
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  send_noneCap2_add_two_beq_zero send_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_lo_append64 extractLsb_hi_append64
  ite_zero32_self ite_zero64_self

private def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

omit [LibsignalPlacement] in
private theorem sepWP_seq_fo {M : AllocCostModel} {prog : Program}
    {mid tgt : BitVec 64} {s : State} {bst : M.σ} {P : SepProp}
    {Mid : M.σ → State → SepProp → Prop}
    {Post : M.σ → State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs₁ : List AllocEvent, FreeOnlyEvs evs₁ ∧ AllocCallPreserved s sm ∧
        Mid (M.stepEvents evs₁ bst) sm Pm))
    (h2 : ∀ (bst₁ : M.σ) (sm : State) (Pm : SepProp),
      sm.pc = mid → sm.status = .Running → AllocCallPreserved s sm →
      Mid bst₁ sm Pm →
      SepWP prog tgt sm Pm (fun sf Pf =>
        ∃ evs₂ : List AllocEvent, FreeOnlyEvs evs₂ ∧ AllocCallPreserved sm sf ∧
          Post (M.stepEvents evs₂ bst₁) sf Pf)) :
    SepWP prog tgt s P (fun sf Pf =>
      ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧
        Post (M.stepEvents evs bst) sf Pf) := by
  refine SepWP.seq h1 fun sm Pm hpc hrun ⟨evs₁, hevs₁, hacp₁, hmid⟩ => ?_
  refine SepWP.mono (h2 (M.stepEvents evs₁ bst) sm Pm hpc hrun hacp₁ hmid) ?_
  intro sf Pf _ _ ⟨evs₂, hevs₂, hacp₂, hpost⟩
  refine ⟨evs₁ ++ evs₂, hevs₁.append hevs₂, hacp₁.trans hacp₂, ?_⟩
  rw [M.stepEvents_append]
  exact hpost

/-! ## 1. Relocatable Budget Callee Lifts (`Block 435` & `Block 436`) -/

theorem spqrSend_dropOptProtoPolyEncoder_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 435)
      (withLsCodeLoaded lsmpl (dropOptProtoPolyEncoderSpec M A lim)) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_opt_proto_poly_encoder_placed hdealloc))
    (by decide) (by decide) (by decide)

theorem spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 436)
      (withLsCodeLoaded lsmpl (dropOptProtoUnchunkedCt1SentSpec M A lim)) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_opt_proto_unchunked_ct1_sent_placed hdealloc))
    (by decide) (by decide) (by decide)

/-! ## 2. Budget-Threaded Unchunked Field Drop Helpers (`+7568`, `+6472`, `+7644`) -/

/-- `spqrSendPlacedEntry + 7568#64 -> spqrSendPlacedEntry + 7632#64`: drops
    `uc : Option V1State.Unchunked.Ct2Sent` at `s.sp + 4896#64` (`sp + 0x1320`), setting
    `x19 = s.sp + 4704#64` (`sp + 0x1260`) and preserving `x23` with `FreeOnlyEvs`. -/
theorem step_send_drop_ct2Sent_7568_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (uc : Option V1State.Unchunked.Ct2Sent)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 7568#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 7632#64) s
      (optProtoUnchunkedCt2SentAt A.repAlloc (s.sp + 4896#64) uc ∗
        A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x19 = s.sp + 4704#64 ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4896#64) 56 ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
  cases uc with
  | none =>
    dsimp only [optProtoUnchunkedCt2SentAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (s.sp + 4896#64)
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
    refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  | some u =>
    dsimp only [optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt]
    cases hauth : u.auth with
    | none =>
      have hnone64 := optProtoAuthenticatorAt_64_none_entails_memRegion_56 A.repAlloc (s.sp + 4832#64) u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone64
      rw [optProtoAuthenticatorAt_none]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      refine SepWP.focus_weaken hnone64 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          Entails.of_eq (by
            simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
              RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
              RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
              RustCliAllocBudget.pool_writeReg]
            first | done | sep_ac_rfl)⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken
        (protoAuthenticatorAt_entails_dealloc A.repAlloc (s.sp + 4896#64) auth)
        (by sep_focus) ?_
      wp_pull_exists; rename_i ga
      rw [show s.sp + 4896#64 = (s.sp + 4832#64) + 64#64 from
        (BitVec.add_assoc s.sp 4832#64 64#64).symm, twoVecHeadersAt_64_eq]
      wp_focus_pure; intro hga_lt
      have hne_none2 := cap_add_two_beq_zero_false hga_lt
      have hne_none1 := cap_add_one_beq_zero_false hga_lt
      have hhdr56 := auth64HeadersAt_entails_memRegion_56 (s.sp + 4832#64) ga u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7612#64)
        (Mid := fun bst₁ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x19 = s.sp + 4704#64 ∧ sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ ((auth64HeadersAt (s.sp + 4832#64) ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
              ((s.sp + 4944#64) ↦₆₄ u.epoch)) ∗
            A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
        (Post := fun bst' sf Q =>
          sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
          sf.readReg64 .x19 = s.sp + 4704#64 ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4896#64) 56 ∗
            A.pool lim bst' sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
        ?_ ?_
      · dsimp only [auth64HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal,
              Entails.of_eq (by
                simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                  RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                  RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                  RustCliAllocBudget.pool_writeReg]
                first | done | sep_ac_rfl)⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
              by simp only [wp_norm, arm64_norm, *],
              by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
              by wp_norm_goal, by wp_norm_goal,
              Entails.of_eq (by sep_ac_rfl)⟩
      · intro bst₁ sa1 Pa1 hpca1 hruna1 _ ⟨hsp_a1, htr_a1, hvregs_a1, hx19_a1, hx23_a1, hPa1⟩
        refine SepWP.weaken_pre hPa1 ?_
        have hsp_a1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hsp_a1]
        dsimp only [auth64HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
              by wp_norm_goal,
              (by wp_norm_goal : _ = sa1.trace).trans htr_a1,
              (by wp_norm_goal : _ = sa1.sp).trans hsp_a1,
              (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
              (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1,
              (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregs_a1,
              Entails.of_eq (by
                simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                  RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                  RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                  RustCliAllocBudget.pool_writeReg]
                first | done | sep_ac_rfl)⟩
        · rw [← hsp_a1, send_stackAt_callee_eq_allocHook sa1.sp]
          wp_steps
          wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bst₁)
          rw [hsp_a1]
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
              by simp only [wp_norm, arm64_norm, *],
              by wp_norm_goal,
              (by wp_norm_goal : _ = sa1.trace).trans htr_a1,
              (by wp_norm_goal : _ = sa1.sp).trans hsp_a1,
              (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
              (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregs_a1,
              Entails.of_eq (by sep_ac_rfl)⟩

/-- `spqrSendPlacedEntry + 6472#64 -> spqrSendPlacedEntry + 6572#64`: drops
    `uc : Option V1State.Unchunked.EkSentCt1Received` at `s.sp + 4840#64` with `FreeOnlyEvs`. -/
theorem step_send_drop_ekSentCt1Received_6472_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (uc : Option V1State.Unchunked.EkSentCt1Received)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6472#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 6572#64) s
      (optProtoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s.sp + 4840#64) uc ∗
        A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4840#64) 104 ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
  let a := s.sp + 4840#64
  cases uc with
  | none =>
    rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
    have hnone104 := optProtoUnchunked2Vec_none_entails_memRegion_104 a
    simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone104 ⊢
    wp_steps
    refine SepWP.focus_weaken hnone104 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  | some u =>
    rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
    refine SepWP.focus_weaken
      (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A.repAlloc (s.sp + 4840#64) u)
      (by sep_focus) ?_
    wp_pull_exists; rename_i g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
    have hhdr104 := protoUnchunked2VecHeadersAt_entails_memRegion_104' a g
    let Post6472 : M.σ → State → SepProp → Prop := fun bst' sf Q =>
      sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
      sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (Q ⊢ memRegion (s.sp + 4840#64) 104 ∗
        A.pool lim bst' sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    let Mid1a : M.σ → State → SepProp → Prop := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ (protoUnchunked2VecHeadersAt a g ∗
          memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    refine sepWP_seq_fo (mid := (blkPl_427).base + 6532#64)
      (Mid := Mid1a) (Post := Post6472)
      ?_ ?_
    · cases hauth : u.auth with
      | none =>
        have hnone48 := optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc a
        rw [show s.sp + 4840#64 + 48#64 = a + 48#64 from rfl, optProtoAuthenticatorAt_48_none]
        dsimp only [Mid1a, protoUnchunked2VecHeadersAt, twoVecHeadersAt]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone48 ⊢
        wp_steps
        refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal,
            Entails.of_eq (by
              simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                RustCliAllocBudget.pool_writeReg]
              first | done | sep_ac_rfl)⟩
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken
          (protoAuthenticatorAt_entails_dealloc A.repAlloc ((s.sp + 4840#64) + 48#64) auth)
          (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [show (s.sp + 4840#64) + 48#64 = a + 48#64 from rfl, twoVecHeadersAt_48_eq]
        wp_focus_pure; intro hga_lt
        have hne_nonea := cap_add_one_beq_zero_false hga_lt
        have hhdr48 := auth48HeadersAt_entails_memRegion_48 a ga
        refine sepWP_seq_fo (mid := (blkPl_427).base + 6512#64)
          (Mid := fun bsta sa1 Pa1 =>
            sa1.sp = s.sp ∧ sa1.trace = s.trace ∧ calleeSavedVRegs sa1 = calleeSavedVRegs s ∧
            sa1.readReg64 .x19 = g.v1.cap ∧ sa1.readReg64 .x23 = x23 ∧
            (Pa1 ⊢ (protoUnchunked2VecHeadersAt a g ∗
                (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 96#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              A.pool lim bsta sa1 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
          (Post := Mid1a)
          ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
            vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal,
                Entails.of_eq (by
                  simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                    RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                    RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                    RustCliAllocBudget.pool_writeReg]
                  first | done | sep_ac_rfl)⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
                by simp only [wp_norm, arm64_norm, *],
                by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
                by wp_norm_goal, by wp_norm_goal,
                Entails.of_eq (by sep_ac_rfl)⟩
        · intro bsta sa1 Pa1 hpca1 hruna1 _ ⟨hsp_a1, htr_a1, hvregs_a1, hx19_a1, hx23_a1, hPa1⟩
          refine SepWP.weaken_pre hPa1 ?_
          have hsp_a1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hsp_a1]
          dsimp only [Mid1a, auth48HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
                (by wp_norm_goal : _ = sa1.sp).trans hsp_a1,
                (by wp_norm_goal : _ = sa1.trace).trans htr_a1,
                (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregs_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1,
                Entails.of_eq (by
                  simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                    RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                    RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                    RustCliAllocBudget.pool_writeReg]
                  first | done | sep_ac_rfl)⟩
          · rw [← hsp_a1, send_stackAt_callee_eq_allocHook sa1.sp]
            wp_steps
            wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bsta)
            rw [hsp_a1]
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
                by simp only [wp_norm, arm64_norm, *],
                (by wp_norm_goal : _ = sa1.sp).trans hsp_a1,
                (by wp_norm_goal : _ = sa1.trace).trans htr_a1,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregs_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1,
                Entails.of_eq (by sep_ac_rfl)⟩
    · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx19_1, hx23_1, hP1⟩
      refine SepWP.weaken_pre hP1 ?_
      have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
      refine sepWP_seq_fo (mid := (blkPl_427).base + 6552#64)
        (Mid := fun bst₂ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ (protoUnchunked2VecHeadersAt a g ∗
              memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
            A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
        (Post := Post6472)
        ?_ ?_
      · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
          RustCliAllocBudget.repAlloc_live]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
              (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.trace).trans htr1,
              (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
              (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
              Entails.of_eq (by
                simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                  RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                  RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                  RustCliAllocBudget.pool_writeReg]
                first | done | sep_ac_rfl)⟩
        · rw [← hsp1, send_stackAt_callee_eq_allocHook s1.sp]
          wp_steps
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, bst₁)
          rw [hsp1]
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents g.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v1.cap.toNat,
              by simp only [wp_norm, arm64_norm, *],
              (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.trace).trans htr1,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s1).trans hvregs1,
              (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
              Entails.of_eq (by sep_ac_rfl)⟩
      · intro bst₂ s2 P2 hpc2 hrun2 _ ⟨hsp2, htr2, hvregs2, hx23_2, hP2⟩
        refine SepWP.weaken_pre hP2 ?_
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
        dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
          RustCliAllocBudget.repAlloc_live]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr104 ⊢
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
              by wp_norm_goal,
              (by wp_norm_goal : _ = s2.trace).trans htr2,
              (by wp_norm_goal : _ = s2.sp).trans hsp2,
              (by wp_norm_goal : _ = s2.readReg64 .x23).trans hx23_2,
              (by wp_norm_goal : _ = calleeSavedVRegs s2).trans hvregs2,
              Entails.of_eq (by
                simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                  RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                  RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                  RustCliAllocBudget.pool_writeReg]
                first | done | sep_ac_rfl)⟩
        · rw [← hsp2, send_stackAt_callee_eq_allocHook s2.sp]
          wp_steps
          wp_call hdealloc_fo (g.v2.ptr, g.v2.cap.toNat, 1, bst₂)
          rw [hsp2]
          refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents g.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v2.cap.toNat,
              by simp only [wp_norm, arm64_norm, *],
              by wp_norm_goal,
              (by wp_norm_goal : _ = s2.trace).trans htr2,
              (by wp_norm_goal : _ = s2.sp).trans hsp2,
              (by wp_norm_goal : _ = s2.readReg64 .x23).trans hx23_2,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s2).trans hvregs2,
              Entails.of_eq (by sep_ac_rfl)⟩

/-- `spqrSendPlacedEntry + 7644#64 -> spqrSendPlacedEntry + 7764#64`: drops
    `uc : Option V1State.Unchunked.Ct1SentEkReceived` at `s.sp + 4840#64` with `FreeOnlyEvs`. -/
theorem step_send_drop_ct1SentEkReceived_7644_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (uc : Option V1State.Unchunked.Ct1SentEkReceived)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 7644#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 7764#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (s.sp + 4840#64) uc ∗
        A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4840#64) 128 ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
  let a := s.sp + 4840#64
  cases uc with
  | none =>
    have hnone128 := optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc a
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none] at hnone128 ⊢
    simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone128 ⊢
    wp_steps
    refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    refine SepWP.focus_weaken
      (protoUnchunkedCt1SentEkReceivedAt_entails_dealloc A.repAlloc (s.sp + 4840#64) u)
      (by sep_focus) ?_
    wp_pull_exists; rename_i g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
    have hhdr128 := protoUnchunked3VecHeadersAt_entails_memRegion_128' a g
    let Post7644 : M.σ → State → SepProp → Prop := fun bst' sf Q =>
      sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
      sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (Q ⊢ memRegion (s.sp + 4840#64) 128 ∗
        A.pool lim bst' sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    let Mid1a : M.σ → State → SepProp → Prop := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7704#64)
      (Mid := Mid1a) (Post := Post7644)
      ?_ ?_
    · cases hauth : u.auth with
      | none =>
        have hnone48 := optProtoAuthenticatorAt_72_none_entails_memRegion_48 A.repAlloc a
        rw [show s.sp + 4840#64 + 72#64 = a + 72#64 from rfl, optProtoAuthenticatorAt_72_none]
        dsimp only [Mid1a, protoUnchunked3VecHeadersAt]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone48 ⊢
        wp_steps
        refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal,
            Entails.of_eq (by
              simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                RustCliAllocBudget.pool_writeReg]
              first | done | sep_ac_rfl)⟩
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken
          (protoAuthenticatorAt_entails_dealloc A.repAlloc ((s.sp + 4840#64) + 72#64) auth)
          (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [show (s.sp + 4840#64) + 72#64 = a + 72#64 from rfl, twoVecHeadersAt_72_eq]
        wp_focus_pure; intro hga_lt
        have hne_nonea := cap_add_one_beq_zero_false hga_lt
        have hhdr48 := auth72HeadersAt_entails_memRegion_48' a ga
        refine sepWP_seq_fo (mid := (blkPl_427).base + 7684#64)
          (Mid := fun bsta sa1 Pa1 =>
            sa1.sp = s.sp ∧ sa1.trace = s.trace ∧ calleeSavedVRegs sa1 = calleeSavedVRegs s ∧
            sa1.readReg64 .x19 = g.v1.cap ∧ sa1.readReg64 .x23 = x23 ∧
            (Pa1 ⊢ (protoUnchunked3VecHeadersAt a g ∗
                (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
              A.pool lim bsta sa1 ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
          (Post := Mid1a)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt,
            vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal,
                Entails.of_eq (by
                  simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                    RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                    RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                    RustCliAllocBudget.pool_writeReg]
                  first | done | sep_ac_rfl)⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
                by simp only [wp_norm, arm64_norm, *],
                by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
                by wp_norm_goal, by wp_norm_goal,
                Entails.of_eq (by sep_ac_rfl)⟩
        · intro bsta sa1 Pa1 hpca1 hruna1 _ ⟨hsp_a1, htr_a1, hvregs_a1, hx19_a1, hx23_a1, hPa1⟩
          refine SepWP.weaken_pre hPa1 ?_
          have hsp_a1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hsp_a1]
          dsimp only [Mid1a, auth72HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
                (by wp_norm_goal : _ = sa1.sp).trans hsp_a1,
                (by wp_norm_goal : _ = sa1.trace).trans htr_a1,
                (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregs_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1,
                Entails.of_eq (by
                  simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                    RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                    RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                    RustCliAllocBudget.pool_writeReg]
                  first | done | sep_ac_rfl)⟩
          · rw [← hsp_a1, send_stackAt_callee_eq_allocHook sa1.sp]
            wp_steps
            wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bsta)
            rw [hsp_a1]
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
                by simp only [wp_norm, arm64_norm, *],
                (by wp_norm_goal : _ = sa1.sp).trans hsp_a1,
                (by wp_norm_goal : _ = sa1.trace).trans htr_a1,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregs_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1,
                Entails.of_eq (by sep_ac_rfl)⟩
    · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx19_1, hx23_1, hP1⟩
      refine SepWP.weaken_pre hP1 ?_
      have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7724#64)
        (Mid := fun bst₂ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
              memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
        (Post := Post7644)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
              (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.trace).trans htr1,
              (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
              (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
              Entails.of_eq (by
                simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                  RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                  RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                  RustCliAllocBudget.pool_writeReg]
                first | done | sep_ac_rfl)⟩
        · rw [← hsp1, send_stackAt_callee_eq_allocHook s1.sp]
          wp_steps
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, bst₁)
          rw [hsp1]
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents g.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v1.cap.toNat,
              by simp only [wp_norm, arm64_norm, *],
              (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.trace).trans htr1,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s1).trans hvregs1,
              (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
              Entails.of_eq (by sep_ac_rfl)⟩
      · intro bst₂ s2 P2 hpc2 hrun2 _ ⟨hsp2, htr2, hvregs2, hx23_2, hP2⟩
        refine SepWP.weaken_pre hP2 ?_
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
        refine sepWP_seq_fo (mid := (blkPl_427).base + 7744#64)
          (Mid := fun bst₃ sm Pm =>
            sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x23 = x23 ∧
            (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
              A.pool lim bst₃ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
          (Post := Post7644)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
                (by wp_norm_goal : _ = s2.sp).trans hsp2,
                (by wp_norm_goal : _ = s2.trace).trans htr2,
                (by wp_norm_goal : _ = calleeSavedVRegs s2).trans hvregs2,
                (by wp_norm_goal : _ = s2.readReg64 .x23).trans hx23_2,
                Entails.of_eq (by
                  simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                    RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                    RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                    RustCliAllocBudget.pool_writeReg]
                  first | done | sep_ac_rfl)⟩
          · rw [← hsp2, send_stackAt_callee_eq_allocHook s2.sp]
            wp_steps
            wp_call hdealloc_fo (g.v2.ptr, g.v2.cap.toNat, 1, bst₂)
            rw [hsp2]
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents g.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v2.cap.toNat,
                by simp only [wp_norm, arm64_norm, *],
                (by wp_norm_goal : _ = s2.sp).trans hsp2,
                (by wp_norm_goal : _ = s2.trace).trans htr2,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s2).trans hvregs2,
                (by wp_norm_goal : _ = s2.readReg64 .x23).trans hx23_2,
                Entails.of_eq (by sep_ac_rfl)⟩
        · intro bst₃ s3 P3 hpc3 hrun3 _ ⟨hsp3, htr3, hvregs3, hx23_3, hP3⟩
          refine SepWP.weaken_pre hP3 ?_
          have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rwa [hsp3]
          dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr128 ⊢
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
                by wp_norm_goal,
                (by wp_norm_goal : _ = s3.trace).trans htr3,
                (by wp_norm_goal : _ = s3.sp).trans hsp3,
                (by wp_norm_goal : _ = s3.readReg64 .x23).trans hx23_3,
                (by wp_norm_goal : _ = calleeSavedVRegs s3).trans hvregs3,
                Entails.of_eq (by
                  simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
                    RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
                    RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
                    RustCliAllocBudget.pool_writeReg]
                  first | done | sep_ac_rfl)⟩
          · rw [← hsp3, send_stackAt_callee_eq_allocHook s3.sp]
            wp_steps
            wp_call hdealloc_fo (g.v3.ptr, g.v3.cap.toNat, 1, bst₃)
            rw [hsp3]
            refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents g.v3.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v3.cap.toNat,
                by simp only [wp_norm, arm64_norm, *],
                by wp_norm_goal,
                (by wp_norm_goal : _ = s3.trace).trans htr3,
                (by wp_norm_goal : _ = s3.sp).trans hsp3,
                (by wp_norm_goal : _ = s3.readReg64 .x23).trans hx23_3,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s3).trans hvregs3,
                Entails.of_eq (by sep_ac_rfl)⟩

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudgetAux
