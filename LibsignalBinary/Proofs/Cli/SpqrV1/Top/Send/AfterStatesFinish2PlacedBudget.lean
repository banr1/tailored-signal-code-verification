/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
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
# Budget-Threaded Relocatable Phase 4 (Part 2) of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Threads `RustCliAllocBudget` through the non-looping `InnerState` drop arms (`ct2Sampled`,
`ct1Received`, `keysSampled`, `ekReceivedCt1Sampled`) and shared `PolynomialDecoder` drop helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget

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
  (V1State pbToProtoPolyEncoder)
open CryptoVerification.RustHeap
  (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_mul_24 cons_len_mul header_cells_entails_memRegion_24
   keysSampledToCt1Received none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   optProtoInnerStateAt optProtoUnchunkedCt1SentEkReceivedAt
   optProtoUnchunkedCt2SentAt optProtoUnchunkedEkSentCt1ReceivedAt
   protoChunkedCt1ReceivedAt protoChunkedCt2SampledAt
   protoChunkedEkReceivedCt1SampledAt protoChunkedKeysSampledAt_eq_ct1ReceivedAt
   protoInnerStateAt sep_pull_body sep_push_body sep_rejoin_loop
   tag_and_two_regions_entails_224 tail_len_mul_lt vecCapPtrDealloc
   vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero)
open CryptoVerification.SpqrV1.ProtoRepr
  (v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Top.Send
  (extractLsb_hi_append64 extractLsb_lo_append64 ite_zero32_self ite_zero64_self
   ofNat_add_one_sub_one ofNat_succ_beq_one_false_24 send_stackAt_callee_eq_allocHook
   spqrSendCalleeStack stackAt_spqrSendCallee_eq_dropStack64)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
  (DeallocOkExtPlaced spqrSend_dealloc_sub_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudgetAux
  (spqrSend_dropOptProtoPolyEncoder_ok_placed
   spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed
   step_send_drop_ct1SentEkReceived_7644_placed
   step_send_drop_ct2Sent_7568_placed
   step_send_drop_ekSentCt1Received_6472_placed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
  (dropOptProtoPolyEncoderSpec)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudgetAux
  (spqrSend_dropOptProtoPolyEncoder_ok_placed
   spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed
   step_send_drop_ct1SentEkReceived_7644_placed
   step_send_drop_ct2Sent_7568_placed
   step_send_drop_ekSentCt1Received_6472_placed)

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
  ofNat_add_one_sub_one
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
private theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program}
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
private theorem sepWP_seq_mid_lscl {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Mid post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hM hcl' => h2 sm Pm hpc hrun hcl' hM)

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

omit [LibsignalPlacement] in
private theorem sepWP_seq_fo_lscl {M : AllocCostModel} {prog : Program}
    {mid tgt : BitVec 64} {s : State} {bst : M.σ} {P : SepProp} {pl : MultiPlacement}
    {Mid : M.σ → State → SepProp → Prop}
    {Post : M.σ → State → SepProp → Prop}
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
  rw [M.stepEvents_append]
  exact hpost

private abbrev innerDropPost {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (bst' : M.σ) (sf : State) (Q : SepProp) : Prop :=
  sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
  sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
  (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
    spqrSendDropJumpTablePlacedAt ∗
    A.pool lim bst' sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)

/-! ## 1. Non-Looping `InnerState` Drop Branches (`ct2Sampled`, `ct1Received`, `keysSampled`, `ekReceivedCt1Sampled`) -/

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.ct2Sampled st)⟩)` (`idx = 10`, target `+7568`). -/
theorem step_send_drop_inner_ct2Sampled_32164_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.Ct2Sampled)
    (x23 : BitVec 64) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.ct2Sampled st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
            spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have huc : ∀ (s1 : State) (bst1 : M.σ),
      s1.pc = spqrSendPlacedEntry + 7568#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 7632#64) s1
        (optProtoUnchunkedCt2SentAt A.repAlloc (s1.sp + 4896#64) st.uc ∗
          A.pool lim bst1 s1 ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 4952#64) 104 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame))
        (fun sf Q =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            AllocCallPreserved s1 sf ∧
            sf.status = .Running ∧
            sf.trace = s1.trace ∧
            sf.sp = s1.sp ∧
            sf.readReg64 .x19 = s1.sp + 4704#64 ∧
            sf.readReg64 .x23 = x23 ∧
            calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
            (Q ⊢ memRegion (s1.sp + 4896#64) 56 ∗
              A.pool lim (M.stepEvents evs bst1) sf ∗ stackAt s1.sp spqrSendCalleeStack ∗
              (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
                optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
                memRegion (s.sp + 4952#64) 104 ∗
                spqrSendDropJumpTablePlacedAt ∗ Frame))) :=
    fun s1 bst1 hpc1 hrun1 hsp1_align hx23_1 =>
      step_send_drop_ct2Sent_7568_placed hdealloc s1 bst1 st.uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt2SampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc ⊢
  let a := s.sp + 4832#64
  have hjoin112 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 56 ⊢ memRegion (a + 8#64) 112 := by
    have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
    rw [← h64, ProofLib.memRegion_split (a + 8#64) 56 56 (by decide)]
    exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x800000000000000a#64) ∗
      memRegion (a + 8#64) 112 ∗ memRegion (a + 120#64) 104 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x800000000000000a#64 112 104 120#64
      (BitVec.add_assoc a 8#64 112#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin112 hjoin224 ⊢
  refine sepWP_seq_fo_lscl hcl (mid := (blkPl_427).base + 7568#64)
    (Mid := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ optProtoUnchunkedCt2SentAt A.repAlloc (s.sp + 4896#64) st.uc ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
        (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
          optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
          memRegion (s.sp + 4952#64) 104 ∗
          spqrSendDropJumpTablePlacedAt ∗ Frame)))
    (Post := innerDropPost A lim s x23 Frame)
    ?_ ?_
  · wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 hcl1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 bst₁ hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine sepWP_seq_fo_lscl hcl1 (mid := (blkPl_427).base + 7632#64)
      (Mid := fun bst₂ s2 Q2 =>
        s2.status = .Running ∧ s2.trace = s1.trace ∧ s2.sp = s.sp ∧
        s2.readReg64 .x19 = s.sp + 4704#64 ∧ s2.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s1 ∧
        (Q2 ⊢ memRegion (s.sp + 4896#64) 56 ∗
          A.pool lim bst₂ s2 ∗ stackAt s.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 4952#64) 104 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame)))
      (Post := innerDropPost A lim s x23 Frame)
      huc1 ?_
    intro bst₂ s2 Q2 hpc2 hrun2 hcl2 _ ⟨_, htr2, hsp2, hx19_2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2' : s2.sp = s.sp := hsp2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2']
    have hx19_2' : s2.readReg64 .x19 = s.sp + 4704#64 := hx19_2
    have hpoly_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl2 hpoly_enc
    simp only [withMemEq, dropOptProtoPolyEncoderSpec] at hpoly_mem
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpoly_mem
    dsimp only [innerDropPost]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_mem (⟨s.sp + 4840#64, st.sendingCt2.map pbToProtoPolyEncoder⟩, bst₂)
    have hacp_poly : AllocCallPreserved s2 sf := by simp only [wp_norm, arm64_norm, *]
    have hevs_poly : FreeOnlyEvs w := by assumption
    have htr_poly : sf.trace = s2.trace := by simp only [wp_norm, arm64_norm, *]
    have hsp_poly : sf.sp = s2.sp := by simp only [wp_norm, arm64_norm, *]
    have hx23_poly : sf.readReg64 .x23 = x23 := by simp only [wp_norm, arm64_norm, *]
    have hvregs_poly : calleeSavedVRegs sf = calleeSavedVRegs s2 := by simp only [wp_norm, arm64_norm, *]
    wp_steps
    refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨w, hevs_poly, hacp_poly.trans (by wp_norm_goal),
        by wp_norm_goal,
        (by wp_norm_goal : _ = sf.trace).trans (htr_poly.trans (htr2.trans htr1)),
        (by wp_norm_goal : _ = sf.sp).trans (hsp_poly.trans hsp2'),
        (by wp_norm_goal : _ = sf.readReg64 .x23).trans hx23_poly,
        (by wp_norm_goal : _ = calleeSavedVRegs sf).trans (hvregs_poly.trans (hvregs2.trans hvregs1)),
        Entails.of_eq (by
          simp only [hsp_poly, hsp2', RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.ct1Received st)⟩)` (`idx = 3`, target `+6472`). -/
theorem step_send_drop_inner_ct1Received_32164_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.Ct1Received)
    (x23 : BitVec 64) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.ct1Received st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
            spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have huc : ∀ (s1 : State) (bst1 : M.σ),
      s1.pc = spqrSendPlacedEntry + 6472#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 6572#64) s1
        (optProtoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s1.sp + 4840#64) st.uc ∗
          A.pool lim bst1 s1 ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5000#64) 56 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame))
        (fun sf Q =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            AllocCallPreserved s1 sf ∧
            sf.status = .Running ∧
            sf.trace = s1.trace ∧
            sf.sp = s1.sp ∧
            sf.readReg64 .x23 = x23 ∧
            calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
            (Q ⊢ memRegion (s1.sp + 4840#64) 104 ∗
              A.pool lim (M.stepEvents evs bst1) sf ∗ stackAt s1.sp spqrSendCalleeStack ∗
              (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
                optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
                memRegion (s.sp + 5000#64) 56 ∗
                spqrSendDropJumpTablePlacedAt ∗ Frame))) :=
    fun s1 bst1 hpc1 hrun1 hsp1_align hx23_1 =>
      step_send_drop_ekSentCt1Received_6472_placed hdealloc s1 bst1 st.uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt1ReceivedAt,
    BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc ⊢
  let a := s.sp + 4832#64
  have hjoin160 : memRegion (a + 8#64) 104 ∗ memRegion (a + 112#64) 56 ⊢ memRegion (a + 8#64) 160 := by
    have h112 : (a + 8#64) + 104#64 = a + 112#64 := BitVec.add_assoc a 8#64 104#64
    rw [← h112, ProofLib.memRegion_split (a + 8#64) 104 56 (by decide)]
    exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000003#64) ∗
      memRegion (a + 8#64) 160 ∗ memRegion (a + 168#64) 56 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000003#64 160 56 168#64
      (BitVec.add_assoc a 8#64 160#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin160 hjoin224 ⊢
  refine sepWP_seq_fo_lscl hcl (mid := (blkPl_427).base + 6472#64)
    (Mid := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ optProtoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s.sp + 4840#64) st.uc ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
        (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
          optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
          memRegion (s.sp + 5000#64) 56 ∗
          spqrSendDropJumpTablePlacedAt ∗ Frame)))
    (Post := innerDropPost A lim s x23 Frame)
    ?_ ?_
  · rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
    dsimp only [spqrSendDropJumpTablePlacedExpanded]
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 hcl1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 bst₁ hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine sepWP_seq_fo_lscl hcl1 (mid := (blkPl_427).base + 6572#64)
      (Mid := fun bst₂ s2 Q2 =>
        s2.status = .Running ∧ s2.trace = s1.trace ∧ s2.sp = s.sp ∧
        s2.readReg64 .x23 = x23 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s1 ∧
        (Q2 ⊢ memRegion (s.sp + 4840#64) 104 ∗
          A.pool lim bst₂ s2 ∗ stackAt s.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5000#64) 56 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame)))
      (Post := innerDropPost A lim s x23 Frame)
      huc1 ?_
    intro bst₂ s2 Q2 hpc2 hrun2 hcl2 _ ⟨_, htr2, hsp2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2' : s2.sp = s.sp := hsp2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2']
    have hpoly_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl2 hpoly_enc
    simp only [withMemEq, dropOptProtoPolyEncoderSpec] at hpoly_mem
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpoly_mem
    dsimp only [innerDropPost]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_mem (⟨s.sp + 4944#64, st.sendingEk.map pbToProtoPolyEncoder⟩, bst₂)
    have hacp_poly : AllocCallPreserved s2 sf := by simp only [wp_norm, arm64_norm, *]
    have hevs_poly : FreeOnlyEvs w := by assumption
    have htr_poly : sf.trace = s2.trace := by simp only [wp_norm, arm64_norm, *]
    have hsp_poly : sf.sp = s2.sp := by simp only [wp_norm, arm64_norm, *]
    have hx23_poly : sf.readReg64 .x23 = x23 := by simp only [wp_norm, arm64_norm, *]
    have hvregs_poly : calleeSavedVRegs sf = calleeSavedVRegs s2 := by simp only [wp_norm, arm64_norm, *]
    wp_steps
    refine SepWP.focus_weaken hjoin160 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨w, hevs_poly, hacp_poly.trans (by wp_norm_goal),
        by wp_norm_goal,
        (by wp_norm_goal : _ = sf.trace).trans (htr_poly.trans (htr2.trans htr1)),
        (by wp_norm_goal : _ = sf.sp).trans (hsp_poly.trans hsp2'),
        (by wp_norm_goal : _ = sf.readReg64 .x23).trans hx23_poly,
        (by wp_norm_goal : _ = calleeSavedVRegs sf).trans (hvregs_poly.trans (hvregs2.trans hvregs1)),
        Entails.of_eq (by
          simp only [hsp_poly, hsp2', RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.keysSampled st)⟩)` (`idx = 1`, target `+6472`). -/
theorem step_send_drop_inner_keysSampled_32164_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.KeysSampled)
    (x23 : BitVec 64) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.keysSampled st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
            spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have huc : ∀ (s1 : State) (bst1 : M.σ),
      s1.pc = spqrSendPlacedEntry + 6472#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 6572#64) s1
        (optProtoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s1.sp + 4840#64)
            (keysSampledToCt1Received st).uc ∗
          A.pool lim bst1 s1 ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64)
              ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5000#64) 56 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame))
        (fun sf Q =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            AllocCallPreserved s1 sf ∧
            sf.status = .Running ∧
            sf.trace = s1.trace ∧
            sf.sp = s1.sp ∧
            sf.readReg64 .x23 = x23 ∧
            calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
            (Q ⊢ memRegion (s1.sp + 4840#64) 104 ∗
              A.pool lim (M.stepEvents evs bst1) sf ∗ stackAt s1.sp spqrSendCalleeStack ∗
              (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
                optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64)
                  ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
                memRegion (s.sp + 5000#64) 56 ∗
                spqrSendDropJumpTablePlacedAt ∗ Frame))) :=
    fun s1 bst1 hpc1 hrun1 hsp1_align hx23_1 =>
      step_send_drop_ekSentCt1Received_6472_placed hdealloc s1 bst1
        (keysSampledToCt1Received st).uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    protoInnerStateAt, BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc ⊢
  rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]
  dsimp only [protoChunkedCt1ReceivedAt]
  let a := s.sp + 4832#64
  have hjoin160 : memRegion (a + 8#64) 104 ∗ memRegion (a + 112#64) 56 ⊢ memRegion (a + 8#64) 160 := by
    have h112 : (a + 8#64) + 104#64 = a + 112#64 := BitVec.add_assoc a 8#64 104#64
    rw [← h112, ProofLib.memRegion_split (a + 8#64) 104 56 (by decide)]
    exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000001#64) ∗
      memRegion (a + 8#64) 160 ∗ memRegion (a + 168#64) 56 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000001#64 160 56 168#64
      (BitVec.add_assoc a 8#64 160#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin160 hjoin224 ⊢
  refine sepWP_seq_fo_lscl hcl (mid := (blkPl_427).base + 6472#64)
    (Mid := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ optProtoUnchunkedEkSentCt1ReceivedAt A.repAlloc (s.sp + 4840#64)
          (keysSampledToCt1Received st).uc ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
        (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
          optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64)
            ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
          memRegion (s.sp + 5000#64) 56 ∗
          spqrSendDropJumpTablePlacedAt ∗ Frame)))
    (Post := innerDropPost A lim s x23 Frame)
    ?_ ?_
  · rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
    dsimp only [spqrSendDropJumpTablePlacedExpanded]
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 hcl1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 bst₁ hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine sepWP_seq_fo_lscl hcl1 (mid := (blkPl_427).base + 6572#64)
      (Mid := fun bst₂ s2 Q2 =>
        s2.status = .Running ∧ s2.trace = s1.trace ∧ s2.sp = s.sp ∧
        s2.readReg64 .x23 = x23 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s1 ∧
        (Q2 ⊢ memRegion (s.sp + 4840#64) 104 ∗
          A.pool lim bst₂ s2 ∗ stackAt s.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4944#64)
              ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5000#64) 56 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame)))
      (Post := innerDropPost A lim s x23 Frame)
      huc1 ?_
    intro bst₂ s2 Q2 hpc2 hrun2 hcl2 _ ⟨_, htr2, hsp2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2' : s2.sp = s.sp := hsp2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2']
    have hpoly_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl2 hpoly_enc
    simp only [withMemEq, dropOptProtoPolyEncoderSpec] at hpoly_mem
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpoly_mem
    dsimp only [innerDropPost]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_mem (⟨s.sp + 4944#64,
      (keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder⟩, bst₂)
    have hacp_poly : AllocCallPreserved s2 sf := by simp only [wp_norm, arm64_norm, *]
    have hevs_poly : FreeOnlyEvs w := by assumption
    have htr_poly : sf.trace = s2.trace := by simp only [wp_norm, arm64_norm, *]
    have hsp_poly : sf.sp = s2.sp := by simp only [wp_norm, arm64_norm, *]
    have hx23_poly : sf.readReg64 .x23 = x23 := by simp only [wp_norm, arm64_norm, *]
    have hvregs_poly : calleeSavedVRegs sf = calleeSavedVRegs s2 := by simp only [wp_norm, arm64_norm, *]
    wp_steps
    refine SepWP.focus_weaken hjoin160 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨w, hevs_poly, hacp_poly.trans (by wp_norm_goal),
        by wp_norm_goal,
        (by wp_norm_goal : _ = sf.trace).trans (htr_poly.trans (htr2.trans htr1)),
        (by wp_norm_goal : _ = sf.sp).trans (hsp_poly.trans hsp2'),
        (by wp_norm_goal : _ = sf.readReg64 .x23).trans hx23_poly,
        (by wp_norm_goal : _ = calleeSavedVRegs sf).trans (hvregs_poly.trans (hvregs2.trans hvregs1)),
        Entails.of_eq (by
          simp only [hsp_poly, hsp2', RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.ekReceivedCt1Sampled st)⟩)` (`idx = 8`, target `+7644`). -/
theorem step_send_drop_inner_ekReceivedCt1Sampled_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.EkReceivedCt1Sampled)
    (x23 : BitVec 64) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.ekReceivedCt1Sampled st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
            spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have huc : ∀ (s1 : State) (bst1 : M.σ),
      s1.pc = spqrSendPlacedEntry + 7644#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 7764#64) s1
        (optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (s1.sp + 4840#64) st.uc ∗
          A.pool lim bst1 s1 ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5024#64) 32 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame))
        (fun sf Q =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            AllocCallPreserved s1 sf ∧
            sf.status = .Running ∧
            sf.trace = s1.trace ∧
            sf.sp = s1.sp ∧
            sf.readReg64 .x23 = x23 ∧
            calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
            (Q ⊢ memRegion (s1.sp + 4840#64) 128 ∗
              A.pool lim (M.stepEvents evs bst1) sf ∗ stackAt s1.sp spqrSendCalleeStack ∗
              (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
                optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
                memRegion (s.sp + 5024#64) 32 ∗
                spqrSendDropJumpTablePlacedAt ∗ Frame))) :=
    fun s1 bst1 hpc1 hrun1 hsp1_align hx23_1 =>
      step_send_drop_ct1SentEkReceived_7644_placed hdealloc s1 bst1 st.uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc ⊢
  let a := s.sp + 4832#64
  have hjoin184 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 56 ⊢ memRegion (a + 8#64) 184 := by
    have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
    rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 56 (by decide)]
    exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000008#64) ∗
      memRegion (a + 8#64) 184 ∗ memRegion (a + 192#64) 32 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000008#64 184 32 192#64
      (BitVec.add_assoc a 8#64 184#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin184 hjoin224 ⊢
  refine sepWP_seq_fo_lscl hcl (mid := (blkPl_427).base + 7644#64)
    (Mid := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (s.sp + 4840#64) st.uc ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
        (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
          optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
          memRegion (s.sp + 5024#64) 32 ∗
          spqrSendDropJumpTablePlacedAt ∗ Frame)))
    (Post := innerDropPost A lim s x23 Frame)
    ?_ ?_
  · rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
    dsimp only [spqrSendDropJumpTablePlacedExpanded]
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 hcl1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 bst₁ hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine sepWP_seq_fo_lscl hcl1 (mid := (blkPl_427).base + 7764#64)
      (Mid := fun bst₂ s2 Q2 =>
        s2.status = .Running ∧ s2.trace = s1.trace ∧ s2.sp = s.sp ∧
        s2.readReg64 .x23 = x23 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s1 ∧
        (Q2 ⊢ memRegion (s.sp + 4840#64) 128 ∗
          A.pool lim bst₂ s2 ∗ stackAt s.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
            optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5024#64) 32 ∗
            spqrSendDropJumpTablePlacedAt ∗ Frame)))
      (Post := innerDropPost A lim s x23 Frame)
      huc1 ?_
    intro bst₂ s2 Q2 hpc2 hrun2 hcl2 _ ⟨_, htr2, hsp2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2' : s2.sp = s.sp := hsp2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2']
    have hpoly_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl2 hpoly_enc
    simp only [withMemEq, dropOptProtoPolyEncoderSpec] at hpoly_mem
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpoly_mem
    dsimp only [innerDropPost]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_mem (⟨s.sp + 4968#64, st.sendingCt1.map pbToProtoPolyEncoder⟩, bst₂)
    have hacp_poly : AllocCallPreserved s2 sf := by simp only [wp_norm, arm64_norm, *]
    have hevs_poly : FreeOnlyEvs w := by assumption
    have htr_poly : sf.trace = s2.trace := by simp only [wp_norm, arm64_norm, *]
    have hsp_poly : sf.sp = s2.sp := by simp only [wp_norm, arm64_norm, *]
    have hx23_poly : sf.readReg64 .x23 = x23 := by simp only [wp_norm, arm64_norm, *]
    have hvregs_poly : calleeSavedVRegs sf = calleeSavedVRegs s2 := by simp only [wp_norm, arm64_norm, *]
    wp_steps
    refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨w, hevs_poly, hacp_poly.trans (by wp_norm_goal),
        by wp_norm_goal,
        (by wp_norm_goal : _ = sf.trace).trans (htr_poly.trans (htr2.trans htr1)),
        (by wp_norm_goal : _ = sf.sp).trans (hsp_poly.trans hsp2'),
        (by wp_norm_goal : _ = sf.readReg64 .x23).trans hx23_poly,
        (by wp_norm_goal : _ = calleeSavedVRegs sf).trans (hvregs_poly.trans (hvregs2.trans hvregs1)),
        Entails.of_eq (by
          simp only [hsp_poly, hsp2', RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
            RustCliAllocBudget.pool_writeReg]
          first | done | sep_ac_rfl)⟩

/-! ## 2. Shared `PolynomialDecoder` Tail (`+7544..+7564 -> +4600`) & Loop (`+6928..+6960`) -/

theorem step_send_poly_decoder_pts_tail_325d4_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (g : VecPin) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 7544#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = g.ptr)
    (hx20 : s.readReg64 .x20 = g.cap)
    (hx23 : s.readReg64 .x23 = x23)
    (hpts_cap_lt : g.cap.toNat * 24 < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      ((if g.cap = 0 then emp
        else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
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
          (Q ⊢ A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
  by_cases hc : g.cap = 0#64
  · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj] at hx20 ⊢
    wp_steps
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
  · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    rw [send_stackAt_callee_eq_allocHook s.sp]
    wp_steps
    wp_call hdealloc_fo (g.ptr, g.cap.toNat * 24, 8, bst)
    dsimp only [wp_norm, arm64_norm]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨rustDeallocEvents (g.cap.toNat * 24) 8, FreeOnlyEvs.singleton 8 (g.cap.toNat * 24),
        by simp only [wp_norm, arm64_norm, *],
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by simp only [wp_norm, arm64_norm, *],
        Entails.of_eq (by sep_ac_rfl)⟩

theorem step_send_poly_decoder_body_6928_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (bst : M.σ) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 6940#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 6928#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            AllocCallPreserved s sm ∧
            (Pm ⊢ memRegion cur 24 ∗
              A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
            sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
            sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧
            sm.readReg64 .x23 = x23) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  intro cur cnt bs s bst Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      ((blkPl_427).base + 6928#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr) ∗ A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sm ∧
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧
          sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
          Entails.of_eq (by
            simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
              RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
              RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
              RustCliAllocBudget.pool_writeReg]
            first | done | sep_ac_rfl),
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps
      wp_call hdealloc_fo (vptr, cap.toNat, 1, bst)
      have hacp_call : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
      have hsp_call : sf.sp = sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s.sp).trans hsp
      have htr_call : sf.trace = s0.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s.trace).trans htrace
      have hvregs_call : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s).trans hvregs
      wp_steps
      rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat,
          hacp_call.trans (by wp_norm_goal),
          Entails.of_eq (by
            simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
              RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
              RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
            first | done | sep_ac_rfl),
          (by wp_norm_goal : _ = sf.sp).trans hsp_call,
          (by wp_norm_goal : _ = sf.trace).trans htr_call,
          (by wp_norm_goal : _ = calleeSavedVRegs sf).trans hvregs_call,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal⟩
  refine SepWP.mono hstep fun sm Pm _ _ ⟨evs, hevs, hacp, hent, hrest⟩ =>
    ⟨evs, hevs, hacp,
      Entails.trans hent (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)),
      hrest⟩

theorem step_send_poly_decoder_loop_6928_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (bst : M.σ) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = spqrSendPlacedEntry + 6940#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim bst s ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            AllocCallPreserved s sm ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗
              A.pool lim (M.stepEvents evs bst) sm ∗ stackAt sp allocHookStack ∗ Frame) ∧
            sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
            sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
            sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_6928_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hbody ⊢
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s bst Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine sepWP_seq_fo (mid := (blkPl_427).base + 6928#64)
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
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s bst _
        hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hP1, hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    refine SepWP.weaken_pre hP1 ?_
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal,
          Entails.of_eq (by
            simp only [AllocCostModel.stepEvents_nil, RustCliAllocBudget.pool_setPC,
              RustCliAllocBudget.pool_advancePC, RustCliAllocBudget.pool_setPState,
              RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
              RustCliAllocBudget.pool_writeReg]
            first | done | sep_ac_rfl),
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      refine SepWP.seq (mid := (blkPl_427).base + 6940#64)
        (Mid := fun s2 P2 =>
          AllocCallPreserved s1 s2 ∧
          (P2 ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim bst₁ s2 ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame)) ∧
          s2.sp = sp ∧ s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
          s2.readReg64 .x19 = ptsPtr ∧ s2.readReg64 .x20 = ptsCap ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x22 = (cur + 24#64) + 8#64 ∧
          s2.readReg64 .x23 = x23)
        ?_ ?_
      · wp_steps
        rw [sep_push_body]
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal,
            Entails.of_eq (by
              simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
                RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
                RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg]
              first | done | sep_ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal,
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, add_24_add_8, *],
            by wp_norm_goal⟩
      · intro s2 P2 hpc2 hrun2 ⟨hacp12, hP2, hsp2, htr2, hvregs2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        refine SepWP.weaken_pre hP2 ?_
        refine SepWP.mono
          (ih (cur + 24#64) s2 bst₁ (memRegion cur 24 ∗ Frame)
            (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2
            hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_
        intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2f, hent, hrest⟩
        refine ⟨evs₂, hevs₂, hacp12.trans hacp2f, Entails.trans hent ?_, hrest⟩
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
