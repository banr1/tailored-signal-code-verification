/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish2
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `PolynomialDecoder` Share-Vector Drop Loops (Block `427`)

Proves budget-threaded combinators and the five `PolynomialDecoder` share-vector deallocation
loops (`+6844`, `+7092`, `+7184`, `+7360`, `+7508`) in `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetLoops

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withMemEq libsignalSessionCode
   lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded withMemEq)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendDropJumpTablePlacedAt spqrSendDropJumpTablePlacedAt_eq_expanded
   spqrSendDropJumpTablePlacedExpanded spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
  (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSessionRepr
  (VecPin)
open CryptoVerification.LibsignalSpqrV1
  (V1State pbToProtoPolyDecoder pbToProtoPolyEncoder)
open CryptoVerification.RustHeap
  (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 auth40HeadersAt auth40HeadersAt_entails_memRegion_56
   cap_add_one_beq_zero_false cap_add_two_beq_zero_false cons_len_mul
   header_cells_entails_memRegion_24 none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   ofNat_beq_zero_false_24 optProtoAuthenticatorAt_40_none_entails_memRegion_56
   optProtoAuthenticatorAt_none optProtoAuthenticatorAt_some optProtoInnerStateAt
   optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolynomialDecoderAt_none'
   optProtoPolynomialDecoderAt_some' optProtoUnchunkedCt1SentAt
   optProtoUnchunkedNoHeaderReceivedAt optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56
   protoAuthenticatorAt_entails_dealloc protoChunkedCt1AcknowledgedAt
   protoChunkedCt1SampledAt protoChunkedNoHeaderReceivedAt protoInnerStateAt
   protoPolyDecoderAt_entails_dealloc protoPolyDecoderHeaders_entails_memRegion_40
   protoUnchunkedCt1SentSize protoUnchunkedNoHeaderReceivedAt
   sep_pull_body sep_push_body sep_rejoin_loop tag_and_two_regions_entails_224
   tail_len_mul_lt twoVecHeadersAt_40_eq vecCapPtrDealloc vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialDecoderAt optProtoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero)
open CryptoVerification.SpqrV1.ProtoRepr
  (v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Top.Send
  (extractLsb_hi_append64 extractLsb_lo_append64 ite_zero32_self ite_zero64_self
   ofNat_add_one_sub_one ofNat_succ_beq_one_false_24 optProtoUnchunkedCt1SentAt_expose_tag
   optProtoUnchunkedCt1SentAt_unexpose_tag send_stackAt_callee_eq_allocHook
   send_stackAt_callee_eq_dropStack32 spqrSendCalleeStack stackAt_spqrSendCallee_eq_dropStack64)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
  (dropOptProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropOptProtoUnchunkedCt1SentSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
  (DeallocOkExtPlaced spqrSend_dealloc_sub_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
  (spqrSend_dropOptProtoPolyEncoder_ok_placed
   spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed
   step_send_poly_decoder_loop_6928_placed
   step_send_poly_decoder_pts_tail_325d4_placed)

variable [LibsignalPlacement]

private theorem send3_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send3_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt spqrSendDropJumpTablePlacedAt optProtoPolynomialEncoderAt optProtoUnchunkedCt1SentAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
attribute [local simp, local arm64_norm, local wp_norm]
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
  ofNat_add_one_sub_one
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  send3_noneCap2_add_two_beq_zero send3_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_lo_append64 extractLsb_hi_append64
  ite_zero32_self ite_zero64_self

local macro "entails_pool_rfl" : term =>
  `(Entails.of_eq (by
    simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
      RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_writeReg]
    try (first | rfl | sep_ac_rfl)))

/-! ## 1. Shared Budget-Threading Combinators -/

def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

omit [LibsignalPlacement] in
theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α} {m : Memory}
    (hcl : LibsignalCodeLoaded pl m)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hm, hpre⟩ := extract_withMemEq hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hm ▸ hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

omit [LibsignalPlacement] in
theorem sepWP_seq_mid_lscl {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Mid post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hM hcl' => h2 sm Pm hpc hrun hcl' hM)

omit [LibsignalPlacement] in
theorem sepWP_seq_fo {M : AllocCostModel} {prog : Program}
    {mid tgt : BitVec 64} {s : State} {bst : M.σ} {P : SepProp}
    {Mid Post : M.σ → State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs₁ : List AllocEvent, FreeOnlyEvs evs₁ ∧ AllocCallPreserved s sm ∧
        Mid (M.stepEvents evs₁ bst) sm Pm))
    (h2 : ∀ (bst₁ : M.σ) (sm : State) (Pm : SepProp),
      sm.pc = mid → sm.status = .Running → AllocCallPreserved s sm → Mid bst₁ sm Pm →
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
  rw [M.stepEvents_append]; exact hpost

omit [LibsignalPlacement] in
theorem sepWP_seq_fo_lscl {M : AllocCostModel} {prog : Program}
    {mid tgt : BitVec 64} {s : State} {bst : M.σ} {P : SepProp} {pl : MultiPlacement}
    {Mid Post : M.σ → State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs₁ : List AllocEvent, FreeOnlyEvs evs₁ ∧ AllocCallPreserved s sm ∧
        Mid (M.stepEvents evs₁ bst) sm Pm))
    (h2 : ∀ (bst₁ : M.σ) (sm : State) (Pm : SepProp),
      sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded pl sm.mem →
      AllocCallPreserved s sm → Mid bst₁ sm Pm →
      SepWP prog tgt sm Pm (fun sf Pf =>
        ∃ evs₂ : List AllocEvent, FreeOnlyEvs evs₂ ∧ AllocCallPreserved sm sf ∧
          Post (M.stepEvents evs₂ bst₁) sf Pf)) :
    SepWP prog tgt s P (fun sf Pf =>
      ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧
        Post (M.stepEvents evs bst) sf Pf) := by
  refine sepWP_seq_mid_lscl hcl h1 fun sm Pm hpc hrun hcl1 ⟨evs₁, hevs₁, hacp₁, hmid⟩ => ?_
  refine SepWP.mono (h2 (M.stepEvents evs₁ bst) sm Pm hpc hrun hcl1 hacp₁ hmid) ?_
  intro sf Pf _ _ ⟨evs₂, hevs₂, hacp₂, hpost⟩
  refine ⟨evs₁ ++ evs₂, hevs₁.append hevs₂, hacp₁.trans hacp₂, ?_⟩
  rw [M.stepEvents_append]; exact hpost

abbrev innerDropPostExp {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (bst' : M.σ) (sf : State) (Q : SepProp) : Prop :=
  sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
  sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
  (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
    spqrSendDropJumpTablePlacedExpanded ∗
    A.pool lim bst' sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)

omit [LibsignalPlacement] in
theorem poly_pts_loop_post_entails_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (pool : SepProp) (g : VecPin) (n : Nat) (sp : BitVec 64)
    (F : SepProp) (hle : n ≤ g.cap.toNat) (hcap_lt : g.cap.toNat * 24 < 2 ^ 63) :
    memRegion g.ptr (n * 24) ∗ pool ∗ stackAt sp allocHookStack ∗
      (A.live g.ptr (g.cap.toNat * 24) 8 ∗
        memRegion (g.ptr + BitVec.ofNat 64 (n * 24)) ((g.cap.toNat - n) * 24) ∗
        memRegion (sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ F) ⊢
    (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
      pool ∗ stackAt sp spqrSendCalleeStack ∗ F := by
  have hsplit : g.cap.toNat * 24 = n * 24 + (g.cap.toNat - n) * 24 := by
    rw [← Nat.add_mul]; congr 1; omega
  have hbound : n * 24 + (g.cap.toNat - n) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
  have hmr : memRegion g.ptr (n * 24) ∗
      memRegion (g.ptr + BitVec.ofNat 64 (n * 24)) ((g.cap.toNat - n) * 24) =
      memRegion g.ptr (g.cap.toNat * 24) := by
    rw [hsplit, ProofLib.memRegion_split g.ptr (n * 24) ((g.cap.toNat - n) * 24) hbound]
  rw [send_stackAt_callee_eq_allocHook sp, ← hmr]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_poly_decoder_pts_tail_325d4_sp_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s0 s2 : State) (bst : M.σ) (g : VecPin) (x23 : BitVec 64) (F2 : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = spqrSendPlacedEntry + 7544#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp) (htr2 : s2.trace = s0.trace)
    (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx19_2 : s2.readReg64 .x19 = g.ptr)
    (hx20_2 : s2.readReg64 .x20 = g.cap)
    (hx23_2 : s2.readReg64 .x23 = x23)
    (hcap_lt : g.cap.toNat * 24 < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s2
      ((if g.cap = 0 then emp
        else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool lim bst s2 ∗ stackAt s0.sp spqrSendCalleeStack ∗ F2)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s2 sf ∧ sf.status = .Running ∧
          sf.trace = s0.trace ∧ sf.sp = s0.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          (Q ⊢ A.pool lim (M.stepEvents evs bst) sf ∗
            stackAt s0.sp spqrSendCalleeStack ∗ F2)) := by
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
  have h := step_send_poly_decoder_pts_tail_325d4_placed
    hdealloc s2 bst g x23 F2 hpc2 hrun2 hsp2_align hx19_2 hx20_2 hx23_2 hcap_lt
  rwa [hsp2, htr2, hvregs2] at h

/-! ## 2. Remaining `PolynomialDecoder` Share-Vector Loops (`6844`, `7092`, `7184`, `7360`, `7508`) -/

theorem step_send_poly_decoder_body_6844_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (bst : M.σ) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 6856#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 6844#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  intro cur cnt bs s bst Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      ((blkPl_427).base + 6844#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr) ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps; wp_call hdealloc_fo (vptr, cap.toNat, 1, bst)
      have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
      have hsp_c : sf.sp = sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s.sp).trans hsp
      have htr_c : sf.trace = s0.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s.trace).trans htrace
      have hvr_c : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s).trans hvregs
      wp_steps; rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat,
          hacp_c.trans (by wp_norm_goal), entails_pool_rfl,
          (by wp_norm_goal : _ = sf.sp).trans hsp_c, (by wp_norm_goal : _ = sf.trace).trans htr_c,
          (by wp_norm_goal : _ = calleeSavedVRegs sf).trans hvr_c,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact SepWP.mono hstep fun sm Pm _ _ ⟨evs, hevs, hacp, hent, hrest⟩ =>
    ⟨evs, hevs, hacp, Entails.trans hent (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hrest⟩

theorem step_send_poly_decoder_loop_6844_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (bst : M.σ) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 6856#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr →
      s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_6844_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hbody ⊢
  intro rest; induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s bst Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine sepWP_seq_fo (mid := (blkPl_427).base + 6844#64)
      (Mid := fun bst₁ sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool lim bst₁ sm ∗ stackAt sp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23)
      (Post := fun bst' sm Pm =>
        (Pm ⊢ memRegion cur ((bs :: tl).length * 24) ∗
          A.pool lim bst' sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s bst _
        hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hP1, hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    refine SepWP.weaken_pre hP1 ?_; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      refine SepWP.seq (mid := (blkPl_427).base + 6856#64)
        (Mid := fun s2 P2 => AllocCallPreserved s1 s2 ∧
          (P2 ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim bst₁ s2 ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame)) ∧
          s2.sp = sp ∧ s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x22 = (cur + 24#64) + 8#64 ∧ s2.readReg64 .x23 = x23) ?_ ?_
      · wp_steps; rw [sep_push_body]
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, entails_pool_rfl, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, add_24_add_8, *], by wp_norm_goal⟩
      · intro s2 P2 hpc2 hrun2 ⟨hacp12, hP2, hsp2, htr2, hvregs2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        refine SepWP.weaken_pre hP2 (SepWP.mono
          (ih (cur + 24#64) s2 bst₁ (memRegion cur 24 ∗ Frame)
            (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_)
        intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2f, hent, hrest⟩
        refine ⟨evs₂, hevs₂, hacp12.trans hacp2f, Entails.trans hent ?_, hrest⟩
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem step_send_poly_decoder_body_7092_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (bst : M.σ) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7104#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7092#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  intro cur cnt bs s bst Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      ((blkPl_427).base + 7092#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr) ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps; wp_call hdealloc_fo (vptr, cap.toNat, 1, bst)
      have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
      have hsp_c : sf.sp = sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s.sp).trans hsp
      have htr_c : sf.trace = s0.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s.trace).trans htrace
      have hvr_c : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s).trans hvregs
      wp_steps; rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat,
          hacp_c.trans (by wp_norm_goal), entails_pool_rfl,
          (by wp_norm_goal : _ = sf.sp).trans hsp_c, (by wp_norm_goal : _ = sf.trace).trans htr_c,
          (by wp_norm_goal : _ = calleeSavedVRegs sf).trans hvr_c,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact SepWP.mono hstep fun sm Pm _ _ ⟨evs, hevs, hacp, hent, hrest⟩ =>
    ⟨evs, hevs, hacp, Entails.trans hent (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hrest⟩

theorem step_send_poly_decoder_loop_7092_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (bst : M.σ) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7104#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr →
      s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7092_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hbody ⊢
  intro rest; induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s bst Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7092#64)
      (Mid := fun bst₁ sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool lim bst₁ sm ∗ stackAt sp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23)
      (Post := fun bst' sm Pm =>
        (Pm ⊢ memRegion cur ((bs :: tl).length * 24) ∗
          A.pool lim bst' sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s bst _
        hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hP1, hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    refine SepWP.weaken_pre hP1 ?_; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      refine SepWP.seq (mid := (blkPl_427).base + 7104#64)
        (Mid := fun s2 P2 => AllocCallPreserved s1 s2 ∧
          (P2 ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim bst₁ s2 ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame)) ∧
          s2.sp = sp ∧ s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x22 = (cur + 24#64) + 8#64 ∧ s2.readReg64 .x23 = x23) ?_ ?_
      · wp_steps; rw [sep_push_body]
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, entails_pool_rfl, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, add_24_add_8, *], by wp_norm_goal⟩
      · intro s2 P2 hpc2 hrun2 ⟨hacp12, hP2, hsp2, htr2, hvregs2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        refine SepWP.weaken_pre hP2 (SepWP.mono
          (ih (cur + 24#64) s2 bst₁ (memRegion cur 24 ∗ Frame)
            (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_)
        intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2f, hent, hrest⟩
        refine ⟨evs₂, hevs₂, hacp12.trans hacp2f, Entails.trans hent ?_, hrest⟩
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem step_send_poly_decoder_body_7184_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (bst : M.σ) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7196#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7184#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  intro cur cnt bs s bst Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      ((blkPl_427).base + 7184#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr) ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps; wp_call hdealloc_fo (vptr, cap.toNat, 1, bst)
      have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
      have hsp_c : sf.sp = sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s.sp).trans hsp
      have htr_c : sf.trace = s0.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s.trace).trans htrace
      have hvr_c : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s).trans hvregs
      wp_steps; rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat,
          hacp_c.trans (by wp_norm_goal), entails_pool_rfl,
          (by wp_norm_goal : _ = sf.sp).trans hsp_c, (by wp_norm_goal : _ = sf.trace).trans htr_c,
          (by wp_norm_goal : _ = calleeSavedVRegs sf).trans hvr_c,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact SepWP.mono hstep fun sm Pm _ _ ⟨evs, hevs, hacp, hent, hrest⟩ =>
    ⟨evs, hevs, hacp, Entails.trans hent (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hrest⟩

theorem step_send_poly_decoder_loop_7184_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (bst : M.σ) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7196#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr →
      s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7184_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hbody ⊢
  intro rest; induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s bst Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7184#64)
      (Mid := fun bst₁ sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool lim bst₁ sm ∗ stackAt sp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23)
      (Post := fun bst' sm Pm =>
        (Pm ⊢ memRegion cur ((bs :: tl).length * 24) ∗
          A.pool lim bst' sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s bst _
        hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hP1, hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    refine SepWP.weaken_pre hP1 ?_; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      refine SepWP.seq (mid := (blkPl_427).base + 7196#64)
        (Mid := fun s2 P2 => AllocCallPreserved s1 s2 ∧
          (P2 ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim bst₁ s2 ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame)) ∧
          s2.sp = sp ∧ s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x22 = (cur + 24#64) + 8#64 ∧ s2.readReg64 .x23 = x23) ?_ ?_
      · wp_steps; rw [sep_push_body]
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, entails_pool_rfl, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, add_24_add_8, *], by wp_norm_goal⟩
      · intro s2 P2 hpc2 hrun2 ⟨hacp12, hP2, hsp2, htr2, hvregs2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        refine SepWP.weaken_pre hP2 (SepWP.mono
          (ih (cur + 24#64) s2 bst₁ (memRegion cur 24 ∗ Frame)
            (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_)
        intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2f, hent, hrest⟩
        refine ⟨evs₂, hevs₂, hacp12.trans hacp2f, Entails.trans hent ?_, hrest⟩
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem step_send_poly_decoder_body_7360_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (bst : M.σ) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7372#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7360#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  intro cur cnt bs s bst Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      ((blkPl_427).base + 7360#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr) ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps; wp_call hdealloc_fo (vptr, cap.toNat, 1, bst)
      have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
      have hsp_c : sf.sp = sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s.sp).trans hsp
      have htr_c : sf.trace = s0.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s.trace).trans htrace
      have hvr_c : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s).trans hvregs
      wp_steps; rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat,
          hacp_c.trans (by wp_norm_goal), entails_pool_rfl,
          (by wp_norm_goal : _ = sf.sp).trans hsp_c, (by wp_norm_goal : _ = sf.trace).trans htr_c,
          (by wp_norm_goal : _ = calleeSavedVRegs sf).trans hvr_c,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact SepWP.mono hstep fun sm Pm _ _ ⟨evs, hevs, hacp, hent, hrest⟩ =>
    ⟨evs, hevs, hacp, Entails.trans hent (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hrest⟩

theorem step_send_poly_decoder_loop_7360_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (bst : M.σ) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7372#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr →
      s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7360_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hbody ⊢
  intro rest; induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s bst Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7360#64)
      (Mid := fun bst₁ sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool lim bst₁ sm ∗ stackAt sp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23)
      (Post := fun bst' sm Pm =>
        (Pm ⊢ memRegion cur ((bs :: tl).length * 24) ∗
          A.pool lim bst' sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s bst _
        hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hP1, hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    refine SepWP.weaken_pre hP1 ?_; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      refine SepWP.seq (mid := (blkPl_427).base + 7372#64)
        (Mid := fun s2 P2 => AllocCallPreserved s1 s2 ∧
          (P2 ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim bst₁ s2 ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame)) ∧
          s2.sp = sp ∧ s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x22 = (cur + 24#64) + 8#64 ∧ s2.readReg64 .x23 = x23) ?_ ?_
      · wp_steps; rw [sep_push_body]
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, entails_pool_rfl, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, add_24_add_8, *], by wp_norm_goal⟩
      · intro s2 P2 hpc2 hrun2 ⟨hacp12, hP2, hsp2, htr2, hvregs2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        refine SepWP.weaken_pre hP2 (SepWP.mono
          (ih (cur + 24#64) s2 bst₁ (memRegion cur 24 ∗ Frame)
            (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_)
        intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2f, hent, hrest⟩
        refine ⟨evs₂, hevs₂, hacp12.trans hacp2f, Entails.trans hent ?_, hrest⟩
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem step_send_poly_decoder_body_7508_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (bst : M.σ) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7520#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7508#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  intro cur cnt bs s bst Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      ((blkPl_427).base + 7508#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr) ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps; wp_call hdealloc_fo (vptr, cap.toNat, 1, bst)
      have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
      have hsp_c : sf.sp = sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s.sp).trans hsp
      have htr_c : sf.trace = s0.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s.trace).trans htrace
      have hvr_c : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s).trans hvregs
      wp_steps; rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat,
          hacp_c.trans (by wp_norm_goal), entails_pool_rfl,
          (by wp_norm_goal : _ = sf.sp).trans hsp_c, (by wp_norm_goal : _ = sf.trace).trans htr_c,
          (by wp_norm_goal : _ = calleeSavedVRegs sf).trans hvr_c,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact SepWP.mono hstep fun sm Pm _ _ ⟨evs, hevs, hacp, hent, hrest⟩ =>
    ⟨evs, hevs, hacp, Entails.trans hent (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hrest⟩

theorem step_send_poly_decoder_loop_7508_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (bst : M.σ) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7520#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr →
      s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ AllocCallPreserved s sm ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7508_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hbody ⊢
  intro rest; induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s bst Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7508#64)
      (Mid := fun bst₁ sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool lim bst₁ sm ∗ stackAt sp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23)
      (Post := fun bst' sm Pm =>
        (Pm ⊢ memRegion cur ((bs :: tl).length * 24) ∗
          A.pool lim bst' sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s bst _
        hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hP1, hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    refine SepWP.weaken_pre hP1 ?_; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, entails_pool_rfl,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      refine SepWP.seq (mid := (blkPl_427).base + 7520#64)
        (Mid := fun s2 P2 => AllocCallPreserved s1 s2 ∧
          (P2 ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim bst₁ s2 ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame)) ∧
          s2.sp = sp ∧ s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x22 = (cur + 24#64) + 8#64 ∧ s2.readReg64 .x23 = x23) ?_ ?_
      · wp_steps; rw [sep_push_body]
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, entails_pool_rfl, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, add_24_add_8, *], by wp_norm_goal⟩
      · intro s2 P2 hpc2 hrun2 ⟨hacp12, hP2, hsp2, htr2, hvregs2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        refine SepWP.weaken_pre hP2 (SepWP.mono
          (ih (cur + 24#64) s2 bst₁ (memRegion cur 24 ∗ Frame)
            (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_)
        intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2f, hent, hrest⟩
        refine ⟨evs₂, hevs₂, hacp12.trans hacp2f, Entails.trans hent ?_, hrest⟩
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetLoops
