/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetLoops
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish2
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Phase 4 (Part 3) of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Threads `RustCliAllocBudget` through the `headerReceived`, `headerSent`, and `ekSentCt1Received`
drop arms and assembles full `PqRatchetState` drop + return struct construction (`+6216 -> +4600`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsmpl lsρ withMemEq)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendDropJumpTablePlacedAt spqrSendDropJumpTablePlacedAt_eq_expanded
   spqrSendDropJumpTablePlacedExpanded spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
  (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PqRatchetState V1State pbToProtoPolyDecoder pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchet
  (spqrSendResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (noneCap)
open CryptoVerification.RustHeap
  (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (auth24HeadersAt auth24HeadersAt_entails_memRegion_48 auth48HeadersAt
   auth48HeadersAt_entails_memRegion_48 cap_add_one_beq_zero_false none2Cap
   none2Cap_add_two_beq_zero none3Cap' noneCap_add_two_beq_zero
   ofNat_beq_zero_false_24 optProtoAuthenticatorAt_24_none_entails_memRegion_48
   optProtoAuthenticatorAt_48_none_entails_memRegion_48 optProtoAuthenticatorAt_none
   optProtoAuthenticatorAt_some optProtoInnerStateAt optProtoInnerState_none_entails_224
   optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolynomialDecoderAt_none'
   optProtoPolynomialDecoderAt_some' optProtoPqRatchetInnerAt
   optProtoPqRatchetInnerAt_none_entails_memRegion_224 optProtoUnchunked1Vec_none_entails_memRegion_80
   optProtoUnchunked2Vec_none_entails_memRegion_104 optProtoUnchunkedEkSentAt_none
   optProtoUnchunkedEkSentAt_some optProtoUnchunkedEkSentCt1ReceivedAt_none
   optProtoUnchunkedEkSentCt1ReceivedAt_some optProtoUnchunkedHeaderReceivedAt_none
   optProtoUnchunkedHeaderReceivedAt_some protoAuthenticatorAt_entails_dealloc
   protoChunkedEkSentCt1ReceivedAt protoChunkedHeaderReceivedAt protoChunkedHeaderSentAt
   protoInnerStateAt protoPolyDecoderAt_entails_dealloc protoPolyDecoderHeaders_entails_memRegion_40
   protoPqRatchetStateAt protoUnchunked1VecHeadersAt protoUnchunked1VecHeadersAt_entails_memRegion_80'
   protoUnchunked2VecHeadersAt protoUnchunked2VecHeadersAt_entails_memRegion_104'
   protoUnchunkedEkSentAt_entails_dealloc protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc
   protoUnchunkedHeaderReceivedAt_entails_dealloc tag_and_two_regions_entails_224
   twoVecHeadersAt twoVecHeadersAt_24_eq twoVecHeadersAt_48_eq vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialDecoderAt optProtoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   pqRatchetStatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Top.Send
  (extractLsb_hi_append64 extractLsb_lo_append64 ite_zero32_self ite_zero64_self
   ofNat_add_one_sub_one optMsgKeySlotsAt pqRatchetStatePBPinnedAt_entails_proto
   send_stackAt_callee_eq_allocHook spqrSendCalleeStack stackAt_spqrSendCallee_eq_dropStack64)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
  (dropOptProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
  (DeallocOkExtPlaced spqrSend_dealloc_sub_ok_placed step_send_build_result_320a4_placed
   step_send_drop_inner_keysUnsampled_32164_placed step_send_drop_vn_chain_32134_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
  (spqrSend_dropOptProtoPolyEncoder_ok_placed
   step_send_drop_inner_ct1Received_32164_placed
   step_send_drop_inner_ct2Sampled_32164_placed
   step_send_drop_inner_ekReceivedCt1Sampled_32164_placed
   step_send_drop_inner_keysSampled_32164_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetAux
  (step_send_drop_inner_ct1Acknowledged_32164_placed
   step_send_drop_inner_ct1Sampled_32164_placed
   step_send_drop_inner_noHeaderReceived_32164_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetLoops
  (deallocFreeOnlySpec innerDropPostExp poly_pts_loop_post_entails_budget
   sepWP_seq_fo sepWP_seq_fo_lscl sepWP_seq_mid_lscl
   step_send_poly_decoder_body_6844_placed step_send_poly_decoder_body_7092_placed
   step_send_poly_decoder_body_7184_placed step_send_poly_decoder_body_7360_placed
   step_send_poly_decoder_body_7508_placed step_send_poly_decoder_loop_6844_placed
   step_send_poly_decoder_loop_7092_placed step_send_poly_decoder_loop_7184_placed
   step_send_poly_decoder_loop_7360_placed step_send_poly_decoder_loop_7508_placed
   step_send_poly_decoder_pts_tail_325d4_sp_placed subroutine_ok_deallocFreeOnly
   subroutine_ok_withMemEq_of_withLsCodeLoaded)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetAux
  (step_send_drop_inner_ct1Acknowledged_32164_placed
   step_send_drop_inner_ct1Sampled_32164_placed
   step_send_drop_inner_noHeaderReceived_32164_placed)

variable [LibsignalPlacement]

private theorem send3_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send3_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt spqrSendDropJumpTablePlacedAt optProtoPolynomialEncoderAt
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

/-! ## 1. `headerReceived` (`idx = 6`, `+7396..+7540`) -/

theorem step_send_drop_inner_headerReceived_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.HeaderReceived)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.headerReceived st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop := step_send_poly_decoder_loop_7508_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedHeaderReceivedAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin120 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) 40 ⊢ memRegion (a + 8#64) 120 := by
    rw [ProofLib.memRegion_split (a + 8#64) 80 40 (by decide), BitVec.add_assoc a 8#64 80#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000006#64) ∗ memRegion (a + 8#64) 120 ∗ memRegion (a + 128#64) 96 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000006#64 120 96 128#64 (BitVec.add_assoc a 8#64 120#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin120 hjoin224 ⊢
  let Mid7476 : M.σ → State → SepProp → Prop := fun bst₁ sm Pm =>
    sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
    sm.readReg64 .x23 = x23 ∧
    (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s.sp + 4840#64) 80 ∗
      optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4920#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗
      A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
  refine sepWP_seq_fo (mid := (blkPl_427).base + 7476#64)
    (Mid := Mid7476) (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedHeaderReceivedAt_none]; dsimp only [Mid7476, spqrSendDropJumpTablePlacedExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone80 := optProtoUnchunked1Vec_none_entails_memRegion_80 (s.sp + 4840#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone80
      refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
    | some u =>
      rw [optProtoUnchunkedHeaderReceivedAt_some]
      have huc_dealloc := protoUnchunkedHeaderReceivedAt_entails_dealloc A.repAlloc (s.sp + 4840#64) u
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc_dealloc
      refine SepWP.focus_weaken huc_dealloc (by sep_focus) ?_; wp_pull_exists; rename_i v1
      wp_focus_pure; intro hcap1_lt; have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      have hhdr80 := protoUnchunked1VecHeadersAt_entails_memRegion_80' (s.sp + 4840#64) v1
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr80 ⊢
      let Mid7456 : M.σ → State → SepProp → Prop := fun bst₀₁ sm Pm =>
        sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23 ∧
        (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗
          (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗ memRegion (s.sp + 4864#64) 48 ∗
            memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
          optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4920#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗
          A.pool lim bst₀₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7456#64) (Mid := Mid7456) (Post := Mid7476) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          have hnone48 := optProtoAuthenticatorAt_24_none_entails_memRegion_48 A.repAlloc (s.sp + 4840#64)
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
          rw [optProtoAuthenticatorAt_none]
          dsimp only [Mid7456, protoUnchunked1VecHeadersAt, spqrSendDropJumpTablePlacedExpanded]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
          refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (s.sp + 4864#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [show s.sp + 4864#64 = (s.sp + 4840#64) + 24#64 from (BitVec.add_assoc s.sp 4840#64 24#64).symm, twoVecHeadersAt_24_eq]
          wp_focus_pure; intro hga_lt; have hne_nonea := cap_add_one_beq_zero_false hga_lt
          have hhdr48 := auth24HeadersAt_entails_memRegion_48 (s.sp + 4840#64) ga
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          refine sepWP_seq_fo (mid := (blkPl_427).base + 7436#64)
            (Mid := fun bsta sm Pm =>
              sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
              sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23 ∧
              (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗
                (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗
                  (auth24HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                  memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
                optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4920#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
                memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗
                A.pool lim bsta sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
            (Post := Mid7456) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc,
              RustCliAllocBudget.repAlloc_live, spqrSendDropJumpTablePlacedExpanded]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                  by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
              wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
                  by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                  by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                  Entails.of_eq (by sep_ac_rfl)⟩
          · intro bsta sa1 Pa1 hpca1 hruna1 _ ⟨hspa1, htra1, hvregsa1, hx19_a1, hx23_a1, hPa1⟩
            refine SepWP.weaken_pre hPa1 ?_; dsimp only [Mid7456]
            have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
            dsimp only [auth24HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                  (by wp_norm_goal : _ = sa1.trace).trans htra1,
                  (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregsa1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, entails_pool_rfl⟩
            · rw [← hspa1, send_stackAt_callee_eq_allocHook sa1.sp]; wp_steps
              wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bsta); rw [hspa1]
              refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
                  by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                  (by wp_norm_goal : _ = sa1.trace).trans htra1,
                  (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregsa1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, Entails.of_eq (by sep_ac_rfl)⟩
      · intro bst₀₁ s01 P01 hpc01 hrun01 _ ⟨hsp01, htr01, hvregs01, hx19_01, hx23_01, hP01⟩
        refine SepWP.weaken_pre hP01 ?_; dsimp only [Mid7476]
        have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s01.sp).trans hsp01,
              (by wp_norm_goal : _ = s01.trace).trans htr01,
              (by wp_norm_goal : _ = calleeSavedVRegs s01).trans hvregs01,
              (by wp_norm_goal : _ = s01.readReg64 .x23).trans hx23_01, entails_pool_rfl⟩
        · rw [← hsp01, send_stackAt_callee_eq_allocHook s01.sp]; wp_steps
          wp_call hdealloc_fo (v1.ptr, v1.cap.toNat, 1, bst₀₁); rw [hsp01]
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents v1.cap.toNat 1, FreeOnlyEvs.singleton 1 v1.cap.toNat,
              by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = s01.sp).trans hsp01,
              (by wp_norm_goal : _ = s01.trace).trans htr01,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s01).trans hvregs01,
              (by wp_norm_goal : _ = s01.readReg64 .x23).trans hx23_01, Entails.of_eq (by sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_; dsimp only [innerDropPostExp]
    cases hct1 : st.receivingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4920#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus)
        (SepWP.focus_weaken hjoin120 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal,
          (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = s1.sp).trans hsp1,
          (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
          (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, entails_pool_rfl⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (s.sp + 4920#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40
        (s.sp + 4920#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      dsimp only [RustCliAllocBudget.repAlloc_live]
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7544#64)
        (Mid := fun bst₂ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s.sp + 4840#64) 80 ∗
              ((s.sp + 4920#64) ↦₆₄ g.cap) ∗ ((s.sp + 4928#64) ↦₆₄ g.ptr) ∗
              ((s.sp + 4936#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 4944#64) 16 ∗
              memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame)))
        (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
              by wp_norm_goal, by wp_norm_goal, (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1, entails_pool_rfl⟩
        | cons bs tl =>
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine SepWP.seq (mid := (blkPl_427).base + 7520#64)
            (Mid := fun s_loop P_loop => AllocCallPreserved s1 s_loop ∧
              s_loop.sp = s.sp ∧ s_loop.trace = s.trace ∧ calleeSavedVRegs s_loop = calleeSavedVRegs s ∧
              s_loop.readReg64 .x19 = g.ptr ∧ s_loop.readReg64 .x20 = g.cap ∧
              s_loop.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
              s_loop.readReg64 .x22 = g.ptr + 8#64 ∧ s_loop.readReg64 .x23 = x23 ∧
              (P_loop ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
                A.pool lim bst₁ s_loop ∗ stackAt s.sp allocHookStack ∗
                (A.live g.ptr (g.cap.toNat * 24) 8 ∗
                  memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                  memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
                  ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s.sp + 4840#64) 80 ∗
                  ((s.sp + 4920#64) ↦₆₄ g.cap) ∗ ((s.sp + 4928#64) ↦₆₄ g.ptr) ∗
                  ((s.sp + 4936#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 4944#64) 16 ∗
                  memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))) ?_ ?_
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨by wp_norm_goal, (by wp_norm_goal : _ = s1.sp).trans hsp1,
                (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1, entails_pool_rfl⟩
          · intro s_loop P_loop hpc_loop hrun_loop ⟨hacp_l, hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l, hP_loop⟩
            refine SepWP.weaken_pre hP_loop (SepWP.mono
              (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop bst₁ _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l) ?_)
            intro sm Pm _ _ ⟨evs_l, hevs_l, hacp_lm, hent_l, hsp_m, htr_m, hvregs_m, hx19_m, hx20_m, hx23_m⟩
            exact ⟨evs_l, hevs_l, hacp_l.trans hacp_lm, hsp_m, htr_m, hvregs_m, hx19_m, hx20_m, hx23_m,
              Entails.trans hent_l (poly_pts_loop_post_entails_budget A _ g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)⟩
      · intro bst₂ s2 P2 hpc2 hrun2 _ ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2, hP2⟩
        refine SepWP.weaken_pre hP2 (SepWP.seq
          (htail s2 bst₂ g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_)
        intro sf Qf hpcf _ ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus)
          (SepWP.focus_weaken hjoin120 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done hpcf hrunf
          ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 2. `headerSent` (`idx = 2`, `+6964..+7124`) -/

theorem step_send_drop_inner_headerSent_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.HeaderSent)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.headerSent st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_7092_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedHeaderSentAt, protoPolynomialEncoderSize,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo hpoly_enc hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin136 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) 56 ⊢ memRegion (a + 8#64) 136 := by
    rw [ProofLib.memRegion_split (a + 8#64) 80 56 (by decide), BitVec.add_assoc a 8#64 80#64]; exact Entails.refl _
  have hjoin176 : memRegion (a + 8#64) 136 ∗ memRegion (a + 144#64) 40 ⊢ memRegion (a + 8#64) 176 := by
    rw [ProofLib.memRegion_split (a + 8#64) 136 40 (by decide), BitVec.add_assoc a 8#64 136#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000002#64) ∗ memRegion (a + 8#64) 176 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000002#64 176 40 184#64 (BitVec.add_assoc a 8#64 176#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin136 hjoin176 hjoin224 ⊢
  let Mid7044 : M.σ → State → SepProp → Prop := fun bst₀₂ sm Pm =>
    sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
    sm.readReg64 .x23 = x23 ∧
    (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (s.sp + 4840#64) 80 ∗
      optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4920#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗
      A.pool lim bst₀₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
  refine sepWP_seq_fo_lscl hcl (mid := (blkPl_427).base + 7044#64)
    (Mid := Mid7044) (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentAt_none]; dsimp only [Mid7044, spqrSendDropJumpTablePlacedExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone80 := optProtoUnchunked1Vec_none_entails_memRegion_80 (s.sp + 4840#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone80
      refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
    | some u =>
      rw [optProtoUnchunkedEkSentAt_some]
      have huc_dealloc := protoUnchunkedEkSentAt_entails_dealloc A.repAlloc (s.sp + 4840#64) u
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc_dealloc
      refine SepWP.focus_weaken huc_dealloc (by sep_focus) ?_; wp_pull_exists; rename_i v1
      wp_focus_pure; intro hcap1_lt; have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      have hhdr80 := protoUnchunked1VecHeadersAt_entails_memRegion_80' (s.sp + 4840#64) v1
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr80 ⊢
      let Mid7024 : M.σ → State → SepProp → Prop := fun bst₀₁ sm Pm =>
        sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23 ∧
        (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗
          (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗ memRegion (s.sp + 4864#64) 48 ∗
            memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
          optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4920#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
          optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗
          A.pool lim bst₀₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7024#64) (Mid := Mid7024) (Post := Mid7044) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          have hnone48 := optProtoAuthenticatorAt_24_none_entails_memRegion_48 A.repAlloc (s.sp + 4840#64)
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
          rw [optProtoAuthenticatorAt_none]
          dsimp only [Mid7024, protoUnchunked1VecHeadersAt, spqrSendDropJumpTablePlacedExpanded]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
          refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (s.sp + 4864#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [show s.sp + 4864#64 = (s.sp + 4840#64) + 24#64 from (BitVec.add_assoc s.sp 4840#64 24#64).symm, twoVecHeadersAt_24_eq]
          wp_focus_pure; intro hga_lt; have hne_nonea := cap_add_one_beq_zero_false hga_lt
          have hhdr48 := auth24HeadersAt_entails_memRegion_48 (s.sp + 4840#64) ga
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          refine sepWP_seq_fo (mid := (blkPl_427).base + 7004#64)
            (Mid := fun bsta sm Pm =>
              sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
              sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23 ∧
              (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗
                (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗
                  (auth24HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                  memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
                optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4920#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
                optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
                memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗
                A.pool lim bsta sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
            (Post := Mid7024) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc,
              RustCliAllocBudget.repAlloc_live, spqrSendDropJumpTablePlacedExpanded]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                  by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
              wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
                  by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                  by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                  Entails.of_eq (by sep_ac_rfl)⟩
          · intro bsta sa1 Pa1 hpca1 hruna1 _ ⟨hspa1, htra1, hvregsa1, hx19_a1, hx23_a1, hPa1⟩
            refine SepWP.weaken_pre hPa1 ?_; dsimp only [Mid7024]
            have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
            dsimp only [auth24HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                  (by wp_norm_goal : _ = sa1.trace).trans htra1,
                  (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregsa1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, entails_pool_rfl⟩
            · rw [← hspa1, send_stackAt_callee_eq_allocHook sa1.sp]; wp_steps
              wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bsta); rw [hspa1]
              refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
                  by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                  (by wp_norm_goal : _ = sa1.trace).trans htra1,
                  (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregsa1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, Entails.of_eq (by sep_ac_rfl)⟩
      · intro bst₀₁ s01 P01 hpc01 hrun01 _ ⟨hsp01, htr01, hvregs01, hx19_01, hx23_01, hP01⟩
        refine SepWP.weaken_pre hP01 ?_; dsimp only [Mid7044]
        have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s01.sp).trans hsp01,
              (by wp_norm_goal : _ = s01.trace).trans htr01,
              (by wp_norm_goal : _ = calleeSavedVRegs s01).trans hvregs01,
              (by wp_norm_goal : _ = s01.readReg64 .x23).trans hx23_01, entails_pool_rfl⟩
        · rw [← hsp01, send_stackAt_callee_eq_allocHook s01.sp]; wp_steps
          wp_call hdealloc_fo (v1.ptr, v1.cap.toNat, 1, bst₀₁); rw [hsp01]
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents v1.cap.toNat 1, FreeOnlyEvs.singleton 1 v1.cap.toNat,
              by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = s01.sp).trans hsp01,
              (by wp_norm_goal : _ = s01.trace).trans htr01,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s01).trans hvregs01,
              (by wp_norm_goal : _ = s01.readReg64 .x23).trans hx23_01, Entails.of_eq (by sep_ac_rfl)⟩
  · intro bst₀₂ s02 P02 hpc02 hrun02 hcl02 _ ⟨hsp02, htr02, hvregs02, hx23_02, hP02⟩
    refine SepWP.weaken_pre hP02 ?_
    have hsp02_align : (s02.sp &&& 15#64 == 0#64) = true := by rwa [hsp02]
    have hpoly_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl02 hpoly_enc
    simp only [withMemEq, dropOptProtoPolyEncoderSpec] at hpoly_mem
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpoly_mem
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7060#64)
      (Mid := fun bst₁ sm Pm =>
        sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x23 = x23 ∧
        (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (s.sp + 4840#64) 136 ∗
          optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗
          A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
      (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
    · rw [← hsp02, stackAt_spqrSendCallee_eq_dropStack64 s02.sp]; wp_steps
      wp_call hpoly_mem (⟨s.sp + 4920#64, st.sendingEk.map pbToProtoPolyEncoder⟩, bst₀₂)
      have hacp_p : AllocCallPreserved s02 sf := by simp only [wp_norm, arm64_norm, *]
      have hevs_p : FreeOnlyEvs w := by assumption
      have hsp_p : sf.sp = s.sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s02.sp).trans hsp02
      have htr_p : sf.trace = s.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s02.trace).trans htr02
      have hvr_p : calleeSavedVRegs sf = calleeSavedVRegs s :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s02).trans hvregs02
      have hx23_p : sf.readReg64 .x23 = x23 :=
        (by simp only [wp_norm, arm64_norm, *] : sf.readReg64 .x23 = s02.readReg64 .x23).trans hx23_02
      rw [hsp02]; dsimp only [wp_norm, arm64_norm]
      refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨w, hevs_p, hacp_p, hsp_p, htr_p, hvr_p, hx23_p, Entails.of_eq (by sep_ac_rfl)⟩
    · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
      refine SepWP.weaken_pre hP1 ?_; dsimp only [innerDropPostExp]
      cases hct1 : st.receivingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
        have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4976#64)
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
        refine SepWP.focus_weaken hnone40 (by sep_focus)
          (SepWP.focus_weaken hjoin176 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal,
            (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = s1.sp).trans hsp1,
            (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
            (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, entails_pool_rfl⟩
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (s.sp + 4976#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40
          (s.sp + 4976#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        dsimp only [RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
        refine sepWP_seq_fo (mid := (blkPl_427).base + 7544#64)
          (Mid := fun bst₂ sm Pm =>
            sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23 ∧
            (Pm ⊢ (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
              A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
              (((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (s.sp + 4840#64) 136 ∗
                ((s.sp + 4976#64) ↦₆₄ g.cap) ∗ ((s.sp + 4984#64) ↦₆₄ g.ptr) ∗
                ((s.sp + 4992#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 5000#64) 16 ∗
                memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame)))
          (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s1.sp).trans hsp1,
                (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
                by wp_norm_goal, by wp_norm_goal, (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1, entails_pool_rfl⟩
          | cons bs tl =>
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
            have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine SepWP.seq (mid := (blkPl_427).base + 7104#64)
              (Mid := fun s_loop P_loop => AllocCallPreserved s1 s_loop ∧
                s_loop.sp = s.sp ∧ s_loop.trace = s.trace ∧ calleeSavedVRegs s_loop = calleeSavedVRegs s ∧
                s_loop.readReg64 .x19 = g.ptr ∧ s_loop.readReg64 .x20 = g.cap ∧
                s_loop.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
                s_loop.readReg64 .x22 = g.ptr + 8#64 ∧ s_loop.readReg64 .x23 = x23 ∧
                (P_loop ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
                  A.pool lim bst₁ s_loop ∗ stackAt s.sp allocHookStack ∗
                  (A.live g.ptr (g.cap.toNat * 24) 8 ∗
                    memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                    memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
                    ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (s.sp + 4840#64) 136 ∗
                    ((s.sp + 4976#64) ↦₆₄ g.cap) ∗ ((s.sp + 4984#64) ↦₆₄ g.ptr) ∗
                    ((s.sp + 4992#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 5000#64) 16 ∗
                    memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))) ?_ ?_
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨by wp_norm_goal, (by wp_norm_goal : _ = s1.sp).trans hsp1,
                  (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
                  by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                  (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1, entails_pool_rfl⟩
            · intro s_loop P_loop hpc_loop hrun_loop ⟨hacp_l, hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l, hP_loop⟩
              refine SepWP.weaken_pre hP_loop (SepWP.mono
                (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop bst₁ _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l) ?_)
              intro sm Pm _ _ ⟨evs_l, hevs_l, hacp_lm, hent_l, hsp_m, htr_m, hvregs_m, hx19_m, hx20_m, hx23_m⟩
              exact ⟨evs_l, hevs_l, hacp_l.trans hacp_lm, hsp_m, htr_m, hvregs_m, hx19_m, hx20_m, hx23_m,
                Entails.trans hent_l (poly_pts_loop_post_entails_budget A _ g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)⟩
        · intro bst₂ s2 P2 hpc2 hrun2 _ ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2, hP2⟩
          refine SepWP.weaken_pre hP2 (SepWP.seq
            (htail s2 bst₂ g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_)
          intro sf Qf hpcf _ ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
          refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus)
            (SepWP.focus_weaken hjoin176 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
          exact ProofLib.SepWP.done hpcf hrunf
            ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 3. `ekSentCt1Received` (`idx = 4`, `+6712..+6876`) -/

theorem step_send_drop_inner_ekSentCt1Received_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.EkSentCt1Received)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.ekSentCt1Received st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop := step_send_poly_decoder_loop_6844_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedEkSentCt1ReceivedAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin144 : memRegion (a + 8#64) 104 ∗ memRegion (a + 112#64) 40 ⊢ memRegion (a + 8#64) 144 := by
    rw [ProofLib.memRegion_split (a + 8#64) 104 40 (by decide), BitVec.add_assoc a 8#64 104#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000004#64) ∗ memRegion (a + 8#64) 144 ∗ memRegion (a + 152#64) 72 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000004#64 144 72 152#64 (BitVec.add_assoc a 8#64 144#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin144 hjoin224 ⊢
  let Mid6812 : M.σ → State → SepProp → Prop := fun bst₁ sm Pm =>
    sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
    sm.readReg64 .x23 = x23 ∧
    (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s.sp + 4840#64) 104 ∗
      optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗
      A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
  refine sepWP_seq_fo (mid := (blkPl_427).base + 6812#64)
    (Mid := Mid6812) (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]; dsimp only [Mid6812, spqrSendDropJumpTablePlacedExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone104 := optProtoUnchunked2Vec_none_entails_memRegion_104 (s.sp + 4840#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone104
      refine SepWP.focus_weaken hnone104 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      have huc_dealloc := protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A.repAlloc (s.sp + 4840#64) u
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc_dealloc
      refine SepWP.focus_weaken huc_dealloc (by sep_focus) ?_; wp_pull_exists; rename_i g
      wp_focus_pure; intro hcap1_lt; have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      have hhdr104 := protoUnchunked2VecHeadersAt_entails_memRegion_104' (s.sp + 4840#64) g
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr104 ⊢
      let Mid6772 : M.σ → State → SepProp → Prop := fun bst₀₁ sm Pm =>
        sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23 ∧
        (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗
          (protoUnchunked2VecHeadersAt (s.sp + 4840#64) g ∗ memRegion (s.sp + 4888#64) 48 ∗
            memRegion (s.sp + 4936#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
          optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗
          A.pool lim bst₀₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      refine sepWP_seq_fo (mid := (blkPl_427).base + 6772#64) (Mid := Mid6772) (Post := Mid6812) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          have hnone48 := optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc (s.sp + 4840#64)
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
          rw [optProtoAuthenticatorAt_none]
          dsimp only [Mid6772, protoUnchunked2VecHeadersAt, twoVecHeadersAt, spqrSendDropJumpTablePlacedExpanded]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
          refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (s.sp + 4888#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [show s.sp + 4888#64 = (s.sp + 4840#64) + 48#64 from (BitVec.add_assoc s.sp 4840#64 48#64).symm, twoVecHeadersAt_48_eq]
          wp_focus_pure; intro hga_lt; have hne_nonea := cap_add_one_beq_zero_false hga_lt
          have hhdr48 := auth48HeadersAt_entails_memRegion_48 (s.sp + 4840#64) ga
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          refine sepWP_seq_fo (mid := (blkPl_427).base + 6752#64)
            (Mid := fun bsta sm Pm =>
              sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
              sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23 ∧
              (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗
                (protoUnchunked2VecHeadersAt (s.sp + 4840#64) g ∗
                  (auth48HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                  memRegion (s.sp + 4936#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                  vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
                memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗
                A.pool lim bsta sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
            (Post := Mid6772) ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt,
              vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live, spqrSendDropJumpTablePlacedExpanded]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                  by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
              wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
                  by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                  by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                  Entails.of_eq (by sep_ac_rfl)⟩
          · intro bsta sa1 Pa1 hpca1 hruna1 _ ⟨hspa1, htra1, hvregsa1, hx19_a1, hx23_a1, hPa1⟩
            refine SepWP.weaken_pre hPa1 ?_; dsimp only [Mid6772]
            have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
            dsimp only [auth48HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                  (by wp_norm_goal : _ = sa1.trace).trans htra1,
                  (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregsa1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, entails_pool_rfl⟩
            · rw [← hspa1, send_stackAt_callee_eq_allocHook sa1.sp]; wp_steps
              wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bsta); rw [hspa1]
              refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
                  by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                  (by wp_norm_goal : _ = sa1.trace).trans htra1,
                  (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregsa1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x19).trans hx19_a1,
                  (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, Entails.of_eq (by sep_ac_rfl)⟩
      · intro bst₀₁ s01 P01 hpc01 hrun01 _ ⟨hsp01, htr01, hvregs01, hx19_01, hx23_01, hP01⟩
        refine SepWP.weaken_pre hP01 ?_
        have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
        refine sepWP_seq_fo (mid := (blkPl_427).base + 6792#64)
          (Mid := fun bst₀₂ sm Pm =>
            sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x23 = x23 ∧
            (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗
              (protoUnchunked2VecHeadersAt (s.sp + 4840#64) g ∗ memRegion (s.sp + 4888#64) 48 ∗
                memRegion (s.sp + 4936#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
              memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗
              A.pool lim bst₀₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
          (Post := Mid6812) ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s01.sp).trans hsp01,
                (by wp_norm_goal : _ = s01.trace).trans htr01,
                (by wp_norm_goal : _ = calleeSavedVRegs s01).trans hvregs01,
                (by wp_norm_goal : _ = s01.readReg64 .x23).trans hx23_01, entails_pool_rfl⟩
          · rw [← hsp01, send_stackAt_callee_eq_allocHook s01.sp]; wp_steps
            wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, bst₀₁); rw [hsp01]
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents g.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v1.cap.toNat,
                by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = s01.sp).trans hsp01,
                (by wp_norm_goal : _ = s01.trace).trans htr01,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s01).trans hvregs01,
                (by wp_norm_goal : _ = s01.readReg64 .x23).trans hx23_01, Entails.of_eq (by sep_ac_rfl)⟩
        · intro bst₀₂ s02 P02 hpc02 hrun02 _ ⟨hsp02, htr02, hvregs02, hx23_02, hP02⟩
          refine SepWP.weaken_pre hP02 ?_; dsimp only [Mid6812]
          have hsp02_align : (s02.sp &&& 15#64 == 0#64) = true := by rwa [hsp02]
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s02.sp).trans hsp02,
                (by wp_norm_goal : _ = s02.trace).trans htr02,
                (by wp_norm_goal : _ = calleeSavedVRegs s02).trans hvregs02,
                (by wp_norm_goal : _ = s02.readReg64 .x23).trans hx23_02, entails_pool_rfl⟩
          · rw [← hsp02, send_stackAt_callee_eq_allocHook s02.sp]; wp_steps
            wp_call hdealloc_fo (g.v2.ptr, g.v2.cap.toNat, 1, bst₀₂); rw [hsp02]
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents g.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 g.v2.cap.toNat,
                by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = s02.sp).trans hsp02,
                (by wp_norm_goal : _ = s02.trace).trans htr02,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s02).trans hvregs02,
                (by wp_norm_goal : _ = s02.readReg64 .x23).trans hx23_02, Entails.of_eq (by sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_; dsimp only [innerDropPostExp]
    cases hct2 : st.receivingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4944#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus)
        (SepWP.focus_weaken hjoin144 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal,
          (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = s1.sp).trans hsp1,
          (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
          (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, entails_pool_rfl⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (s.sp + 4944#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40
        (s.sp + 4944#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      dsimp only [RustCliAllocBudget.repAlloc_live]
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7544#64)
        (Mid := fun bst₂ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s.sp + 4840#64) 104 ∗
              ((s.sp + 4944#64) ↦₆₄ g.cap) ∗ ((s.sp + 4952#64) ↦₆₄ g.ptr) ∗
              ((s.sp + 4960#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 4968#64) 16 ∗
              memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame)))
        (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
              by wp_norm_goal, by wp_norm_goal, (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1, entails_pool_rfl⟩
        | cons bs tl =>
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine SepWP.seq (mid := (blkPl_427).base + 6856#64)
            (Mid := fun s_loop P_loop => AllocCallPreserved s1 s_loop ∧
              s_loop.sp = s.sp ∧ s_loop.trace = s.trace ∧ calleeSavedVRegs s_loop = calleeSavedVRegs s ∧
              s_loop.readReg64 .x19 = g.ptr ∧ s_loop.readReg64 .x20 = g.cap ∧
              s_loop.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
              s_loop.readReg64 .x22 = g.ptr + 8#64 ∧ s_loop.readReg64 .x23 = x23 ∧
              (P_loop ⊢ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
                A.pool lim bst₁ s_loop ∗ stackAt s.sp allocHookStack ∗
                (A.live g.ptr (g.cap.toNat * 24) 8 ∗
                  memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                  memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
                  ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s.sp + 4840#64) 104 ∗
                  ((s.sp + 4944#64) ↦₆₄ g.cap) ∗ ((s.sp + 4952#64) ↦₆₄ g.ptr) ∗
                  ((s.sp + 4960#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 4968#64) 16 ∗
                  memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))) ?_ ?_
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨by wp_norm_goal, (by wp_norm_goal : _ = s1.sp).trans hsp1,
                (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1, entails_pool_rfl⟩
          · intro s_loop P_loop hpc_loop hrun_loop ⟨hacp_l, hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l, hP_loop⟩
            refine SepWP.weaken_pre hP_loop (SepWP.mono
              (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop bst₁ _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l) ?_)
            intro sm Pm _ _ ⟨evs_l, hevs_l, hacp_lm, hent_l, hsp_m, htr_m, hvregs_m, hx19_m, hx20_m, hx23_m⟩
            exact ⟨evs_l, hevs_l, hacp_l.trans hacp_lm, hsp_m, htr_m, hvregs_m, hx19_m, hx20_m, hx23_m,
              Entails.trans hent_l (poly_pts_loop_post_entails_budget A _ g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)⟩
      · intro bst₂ s2 P2 hpc2 hrun2 _ ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2, hP2⟩
        refine SepWP.weaken_pre hP2 (SepWP.seq
          (htail s2 bst₂ g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_)
        intro sf Qf hpcf _ ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus)
          (SepWP.focus_weaken hjoin144 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done hpcf hrunf
          ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 4. Top-Level `step_send_drop_inner_32164_placed`, `step_send_drop_pq_state_32134_placed`, and `step_send_finish_320a4_placed` -/

private theorem step_send_drop_inner_none_32164_acp_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s : State) (bst : M.σ) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoPqRatchetInnerAt A.repAlloc (s.sp + 4832#64) none ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoPqRatchetInnerAt,
    none3Cap', BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
  have hnone224 := optProtoPqRatchetInnerAt_none_entails_memRegion_224 (s.sp + 4832#64)
  dsimp only [none3Cap'] at hnone224; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
  refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩

private theorem step_send_drop_inner_v1_none_32164_acp_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s : State) (bst : M.σ) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) none ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    none2Cap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
  have hnone224 := optProtoInnerState_none_entails_224 (s.sp + 4832#64)
  dsimp only [none2Cap] at hnone224; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
  refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩

private theorem step_send_epoch_dealloc_32114_acp_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s : State) (bst : M.σ) (x23 x25 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6328#64) (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23) (hx25 : s.readReg64 .x25 = x25)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x19 = 0#32) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 6360#64) s
      (A.pool lim bst s ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          sf.readReg64 .x25 = x25 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ A.pool lim (M.stepEvents evs bst) sf ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rcases hflag with hx21 | hx19
  · wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
  · have hgpr19 : BitVec.truncate 32 (s.readReg64 (Reg.gpr 19#5)) = 0#32 := hx19
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩

theorem step_send_drop_inner_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (inner : Option PqRatchetState.Inner)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = s.sp + 4704#64)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoPqRatchetInnerAt A.repAlloc (s.sp + 4832#64) inner ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  rcases inner with _ | ⟨⟨_ | st⟩⟩
  · exact step_send_drop_inner_none_32164_acp_placed s bst x23 Frame hpc hrun hsp_align hx23
  · exact step_send_drop_inner_v1_none_32164_acp_placed s bst x23 Frame hpc hrun hsp_align hx23
  · cases st with
    | keysUnsampled st => exact step_send_drop_inner_keysUnsampled_32164_placed hdealloc s bst st x23 Frame hpc hrun hsp_align hx23
    | keysSampled st => exact step_send_drop_inner_keysSampled_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx23
    | headerSent st => exact step_send_drop_inner_headerSent_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx23
    | ct1Received st => exact step_send_drop_inner_ct1Received_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx23
    | ekSentCt1Received st => exact step_send_drop_inner_ekSentCt1Received_32164_placed hdealloc s bst st x23 Frame hpc hrun hsp_align hx23
    | noHeaderReceived st => exact step_send_drop_inner_noHeaderReceived_32164_placed hdealloc s bst st x23 Frame hpc hrun hsp_align hx23
    | headerReceived st => exact step_send_drop_inner_headerReceived_32164_placed hdealloc s bst st x23 Frame hpc hrun hsp_align hx23
    | ct1Sampled st => exact step_send_drop_inner_ct1Sampled_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx19 hx23
    | ekReceivedCt1Sampled st => exact step_send_drop_inner_ekReceivedCt1Sampled_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx23
    | ct1Acknowledged st => exact step_send_drop_inner_ct1Acknowledged_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx23
    | ct2Sampled st => exact step_send_drop_inner_ct2Sampled_32164_placed hdealloc s bst st x23 Frame hcl hpc hrun hsp_align hx23

theorem step_send_drop_pq_state_32134_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : PqRatchetState)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6360#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : (s.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (protoPqRatchetStateAt A.repAlloc (s.sp + 4704#64) st ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4704#64) 352 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hjoin352 : memRegion (s.sp + 4704#64) 128 ∗ memRegion (s.sp + 4832#64) 224 ⊢ memRegion (s.sp + 4704#64) 352 := by
    have h4832 : (s.sp + 4704#64) + 128#64 = s.sp + 4832#64 := by bv_omega
    rw [← h4832, ProofLib.memRegion_split (s.sp + 4704#64) 128 224 (by decide)]; exact Entails.refl _
  dsimp only [protoPqRatchetStateAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.weaken_pre ?_
    (sepWP_seq_mid_lscl hcl
      (step_send_drop_vn_chain_32134_placed hdealloc s bst st.versionNegotiation st.chain x23
        (optProtoPqRatchetInnerAt A.repAlloc (s.sp + 4832#64) st.inner ∗ spqrSendDropJumpTablePlacedAt ∗ Frame)
        hcl hpc hrun hsp_align hx23 hx25) ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 Q1 hpc1 _ hcl1 ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx19_1, hx23_1, hvregs1, hQ1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have hx19_1' : s1.readReg64 .x19 = s1.sp + 4704#64 := by rw [hsp1]; exact hx19_1
    rw [← hsp1] at hQ1
    refine SepWP.weaken_pre ?_
      (SepWP.mono (step_send_drop_inner_32164_placed hdealloc s1 (M.stepEvents evs₁ bst) st.inner x23
        (memRegion (s1.sp + 4704#64) 128 ∗ Frame) hcl1 hpc1 hrun1 hsp1_align hx19_1' hx23_1) ?_)
    · exact Entails.trans hQ1 (Entails.of_eq (by sep_ac_rfl))
    · intro sf Qf _ _ ⟨evs₂, hevs₂, hacp₂, hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
      refine ⟨evs₁ ++ evs₂, hevs₁.append hevs₂, hacp₁.trans hacp₂, hrunf, htrf.trans htr1,
        hspf.trans hsp1, hx23_f, hvregsf.trans hvregs1, ?_⟩
      rw [hsp1] at hQf; rw [M.stepEvents_append]
      exact Entails.trans hQf (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hjoin352))

theorem step_send_finish_320a4_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = spqrSendPlacedEntry + 6216#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hflag : x21 = noneCap ∨ BitVec.truncate 32 v_20 = 0#32)
    (hx25_ch : (x25 + 1#64 == 0#64) = !st.chain.isSome)
    (hret_align : (ret &&& 7#64 == 0#64) = true) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (memRegion ret 72 ∗ vecU8 A.repAlloc (s.sp + 1424#64) stBytes ∗
        vecU8 A.repAlloc (s.sp + 4080#64) msgBytes ∗ optMsgKeySlotsAt A.repAlloc s.sp key ∗
        ((s.sp + 32#64) ↦₆₄ v_20) ∗ memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
        pqRatchetStatePBPinnedAt A.repAlloc g (s.sp + 4704#64) st ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗
            memRegion (s.sp + 1424#64) 24 ∗ memRegion (s.sp + 4080#64) 24 ∗
            memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 4704#64) 352 ∗
            memRegion (s.sp + 7136#64) 16 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  refine SepWP.focus_weaken (pqRatchetStatePBPinnedAt_entails_proto A.repAlloc g (s.sp + 4704#64) st) (by sep_focus) ?_
  refine SepWP.weaken_pre ?_
    (sepWP_seq_mid_lscl hcl
      (step_send_build_result_320a4_placed hdealloc s bst ret v_20 x21 x23 x25 x27 stBytes msgBytes key
        (protoPqRatchetStateAt A.repAlloc (s.sp + 4704#64) st ∗ spqrSendDropJumpTablePlacedAt ∗ Frame)
        hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 hx28 hret_align hsp_align) ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 Q1 hpc1 _ hcl1 ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx25_1, _, hvregs1, hQ1⟩
    have hflag1 : s1.readReg64 .x21 = noneCap ∨ s1.readReg32 .x19 = 0#32 := by
      rcases hflag with h21 | h20
      · left; rw [hx21_1, h21]
      · right; simp only [State.readReg32, hx19_1, h20]
    refine SepWP.weaken_pre ?_
      (sepWP_seq_mid_lscl hcl1
        (step_send_epoch_dealloc_32114_acp_placed (A := A) (lim := lim) s1 (M.stepEvents evs₁ bst) x23 x25
          (spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗
            memRegion (s.sp + 1424#64) 24 ∗ memRegion (s.sp + 4080#64) 24 ∗
            memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
            stackAt s.sp spqrSendCalleeStack ∗
            protoPqRatchetStateAt A.repAlloc (s.sp + 4704#64) st ∗ spqrSendDropJumpTablePlacedAt ∗ Frame)
          hpc1 hrun1 hx23_1 hx25_1 hflag1) ?_)
    · exact Entails.trans hQ1 (Entails.of_eq (by sep_ac_rfl))
    · intro s2 Q2 hpc2 _ hcl2 ⟨evs₂, hevs₂, hacp₂, hrun2, htr2, hsp2, hx23_2, hx25_2, hvregs2, hQ2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2, hsp1]
      have hx25_2' : (s2.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome := by rw [hx25_2, hx25_ch]
      rw [← hsp1, ← hsp2] at hQ2
      refine SepWP.weaken_pre ?_
        (SepWP.mono (step_send_drop_pq_state_32134_placed hdealloc s2 (M.stepEvents evs₂ (M.stepEvents evs₁ bst)) st x23
          (spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s2.sp + 8#64) 8 ∗ memRegion (s2.sp + 24#64) 24 ∗
            memRegion (s2.sp + 1424#64) 24 ∗ memRegion (s2.sp + 4080#64) 24 ∗
            memRegion (s2.sp + 4192#64) 48 ∗ memRegion (s2.sp + 7136#64) 16 ∗ Frame)
          hcl2 hpc2 hrun2 hsp2_align hx23_2 hx25_2') ?_)
      · exact Entails.trans hQ2 (Entails.of_eq (by sep_ac_rfl))
      · intro sf Qf _ _ ⟨evs₃, hevs₃, hacp₃, hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine ⟨evs₁ ++ evs₂ ++ evs₃, (hevs₁.append hevs₂).append hevs₃, (hacp₁.trans hacp₂).trans hacp₃,
          hrunf, htrf.trans (htr2.trans htr1), hspf.trans (hsp2.trans hsp1),
          hx23_f, hvregsf.trans (hvregs2.trans hvregs1), ?_⟩
        rw [hsp2, hsp1] at hQf; rw [M.stepEvents_append, M.stepEvents_append]
        exact Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudget
