/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetLoops
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
# Budget-Threaded Looping `InnerState` Drop Arms (`ct1Acknowledged`, `ct1Sampled`, `noHeaderReceived`)

Threads `RustCliAllocBudget` through the looping `InnerState` drop arms `idx = 9, 7, 5`
inside Block `427` (`spqr::send::<signal_session_ratchet::Coins>`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetAux

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

open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetLoops
  (deallocFreeOnlySpec innerDropPostExp poly_pts_loop_post_entails_budget
   sepWP_seq_fo sepWP_seq_fo_lscl
   step_send_poly_decoder_body_6844_placed step_send_poly_decoder_body_7092_placed
   step_send_poly_decoder_body_7184_placed step_send_poly_decoder_body_7360_placed
   step_send_poly_decoder_body_7508_placed step_send_poly_decoder_loop_6844_placed
   step_send_poly_decoder_loop_7092_placed step_send_poly_decoder_loop_7184_placed
   step_send_poly_decoder_loop_7360_placed step_send_poly_decoder_loop_7508_placed
   step_send_poly_decoder_pts_tail_325d4_sp_placed subroutine_ok_deallocFreeOnly
   subroutine_ok_withMemEq_of_withLsCodeLoaded)

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

/-! ## 1. `ct1Acknowledged` (`idx = 9`, `+6880..+6960`) -/

theorem step_send_drop_inner_ct1Acknowledged_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.Ct1Acknowledged)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.ct1Acknowledged st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hct1_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl
    (spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed hdealloc)
  simp only [withMemEq, dropOptProtoUnchunkedCt1SentSpec] at hct1_mem
  have hloop := step_send_poly_decoder_loop_6928_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedCt1AcknowledgedAt, protoUnchunkedCt1SentSize,
    BitVec.ofNat_eq_ofNat] at hpc hct1_mem hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin168 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 40 ⊢ memRegion (a + 8#64) 168 := by
    rw [ProofLib.memRegion_split (a + 8#64) 128 40 (by decide), BitVec.add_assoc a 8#64 128#64]
    exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000009#64) ∗
      memRegion (a + 8#64) 168 ∗ memRegion (a + 176#64) 48 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000009#64 168 48 176#64
      (BitVec.add_assoc a 8#64 168#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin168 hjoin224 ⊢
  refine sepWP_seq_fo (mid := (blkPl_427).base + 6896#64)
    (Mid := fun bst₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗ memRegion (s.sp + 4840#64) 128 ∗
        optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4968#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
        memRegion (s.sp + 5008#64) 48 ∗ spqrSendDropJumpTablePlacedExpanded ∗
        A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
    (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
  · dsimp only [spqrSendDropJumpTablePlacedExpanded]
    rw [send_stackAt_callee_eq_dropStack32 s.sp]; wp_steps
    wp_call hct1_mem (⟨s.sp + 4840#64, st.uc⟩, bst)
    have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
    have hevs_c : FreeOnlyEvs w := by assumption
    dsimp only [wp_norm, arm64_norm]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨w, hevs_c, hacp_c, by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_; dsimp only [innerDropPostExp]
    cases hek : st.receivingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4968#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus)
        (SepWP.focus_weaken hjoin168 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal,
          (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = s1.sp).trans hsp1,
          (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
          (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, entails_pool_rfl⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (s.sp + 4968#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40
        (s.sp + 4968#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      dsimp only [RustCliAllocBudget.repAlloc_live]
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7544#64)
        (Mid := fun bst₂ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗ memRegion (s.sp + 4840#64) 128 ∗
              ((s.sp + 4968#64) ↦₆₄ g.cap) ∗ ((s.sp + 4976#64) ↦₆₄ g.ptr) ∗
              ((s.sp + 4984#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              memRegion (s.sp + 4992#64) 16 ∗ memRegion (s.sp + 5008#64) 48 ∗
              spqrSendDropJumpTablePlacedExpanded ∗ Frame)))
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
          refine SepWP.seq (mid := (blkPl_427).base + 6940#64)
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
                  ((s.sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗ memRegion (s.sp + 4840#64) 128 ∗
                  ((s.sp + 4968#64) ↦₆₄ g.cap) ∗ ((s.sp + 4976#64) ↦₆₄ g.ptr) ∗
                  ((s.sp + 4984#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
                  memRegion (s.sp + 4992#64) 16 ∗ memRegion (s.sp + 5008#64) 48 ∗
                  spqrSendDropJumpTablePlacedExpanded ∗ Frame))) ?_ ?_
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
          (SepWP.focus_weaken hjoin168 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done hpcf hrunf
          ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 2. `ct1Sampled` (`idx = 7`, `+7128..+7216`) -/

theorem step_send_drop_inner_ct1Sampled_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.Ct1Sampled)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = s.sp + 4704#64)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.ct1Sampled st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hct1_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl
    (spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed hdealloc)
  simp only [withMemEq, dropOptProtoUnchunkedCt1SentSpec] at hct1_mem
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_7184_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedCt1SampledAt, protoUnchunkedCt1SentSize, protoPolynomialEncoderSize,
    BitVec.ofNat_eq_ofNat] at hpc hct1_mem hpoly_enc hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin184 : memRegion a 128 ∗ memRegion (a + 128#64) 56 ⊢ memRegion a 184 := by
    rw [ProofLib.memRegion_split a 128 56 (by decide)]; exact Entails.refl _
  have hjoin224 : memRegion a 184 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 := by
    rw [ProofLib.memRegion_split a 184 40 (by decide)]; exact Entails.refl _
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin184 hjoin224 ⊢
  refine sepWP_seq_fo_lscl hcl (mid := (blkPl_427).base + 7136#64)
    (Mid := fun bst₀₁ sm Pm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .x23 = x23 ∧
      (Pm ⊢ memRegion (s.sp + 4832#64) 128 ∗
        optProtoPolynomialEncoderAt A.repAlloc (s.sp + 4960#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
        optProtoPolynomialDecoderAt A.repAlloc (s.sp + 5016#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
        spqrSendDropJumpTablePlacedExpanded ∗ A.pool lim bst₀₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
    (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
  · dsimp only [spqrSendDropJumpTablePlacedExpanded]
    refine SepWP.focus_weaken (optProtoUnchunkedCt1SentAt_expose_tag A.repAlloc (s.sp + 4832#64) st.uc) (by sep_focus) ?_
    wp_pull_exists; rename_i tagW; wp_focus_pure; rintro ⟨hw_ult, hw_cc⟩
    have hw_ult' : ¬((tagW + 3#64).ult 2#64 = true) := by rw [hw_ult]; decide
    have hw_cc' : ¬(ConditionHolds .CC (subsPState64 (tagW ^^^ 0x8000000000000000#64) 11#64) = true) := by rw [hw_cc]; decide
    wp_steps
    refine SepWP.focus_weaken (optProtoUnchunkedCt1SentAt_unexpose_tag A.repAlloc (s.sp + 4832#64) tagW st.uc) (by sep_focus) ?_
    rw [send_stackAt_callee_eq_dropStack32 s.sp]
    wp_call hct1_mem (⟨s.sp + 4832#64, st.uc⟩, bst)
    have hacp_c : AllocCallPreserved s sf := by simp only [wp_norm, arm64_norm, *]
    have hevs_c : FreeOnlyEvs w := by assumption
    dsimp only [wp_norm, arm64_norm]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨w, hevs_c, hacp_c, by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl)⟩
  · intro bst₀₁ s01 P01 hpc01 hrun01 hcl01 _ ⟨hsp01, htr01, hvregs01, hx23_01, hP01⟩
    refine SepWP.weaken_pre hP01 ?_
    have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
    have hpoly_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl01 hpoly_enc
    simp only [withMemEq, dropOptProtoPolyEncoderSpec] at hpoly_mem
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpoly_mem
    refine sepWP_seq_fo (mid := (blkPl_427).base + 7152#64)
      (Mid := fun bst₁ sm Pm =>
        sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x23 = x23 ∧
        (Pm ⊢ memRegion (s.sp + 4832#64) 184 ∗
          optProtoPolynomialDecoderAt A.repAlloc (s.sp + 5016#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
          spqrSendDropJumpTablePlacedExpanded ∗ A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
      (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
    · rw [← hsp01, stackAt_spqrSendCallee_eq_dropStack64 s01.sp]; wp_steps
      wp_call hpoly_mem (⟨s.sp + 4960#64, st.sendingCt1.map pbToProtoPolyEncoder⟩, bst₀₁)
      have hacp_p : AllocCallPreserved s01 sf := by simp only [wp_norm, arm64_norm, *]
      have hevs_p : FreeOnlyEvs w := by assumption
      have hsp_p : sf.sp = s.sp := (by simp only [wp_norm, arm64_norm, *] : sf.sp = s01.sp).trans hsp01
      have htr_p : sf.trace = s.trace := (by simp only [wp_norm, arm64_norm, *] : sf.trace = s01.trace).trans htr01
      have hvr_p : calleeSavedVRegs sf = calleeSavedVRegs s :=
        (by simp only [wp_norm, arm64_norm, *] : calleeSavedVRegs sf = calleeSavedVRegs s01).trans hvregs01
      have hx23_p : sf.readReg64 .x23 = x23 :=
        (by simp only [wp_norm, arm64_norm, *] : sf.readReg64 .x23 = s01.readReg64 .x23).trans hx23_01
      rw [hsp01]; dsimp only [wp_norm, arm64_norm]
      refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨w, hevs_p, hacp_p, hsp_p, htr_p, hvr_p, hx23_p, Entails.of_eq (by sep_ac_rfl)⟩
    · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
      refine SepWP.weaken_pre hP1 ?_; dsimp only [innerDropPostExp]
      cases hek : st.receivingEk with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
        have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 5016#64)
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
        refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal,
            (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = s1.sp).trans hsp1,
            (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
            (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, entails_pool_rfl⟩
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (s.sp + 5016#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40
          (s.sp + 5016#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        dsimp only [RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
        refine sepWP_seq_fo (mid := (blkPl_427).base + 7544#64)
          (Mid := fun bst₂ sm Pm =>
            sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23 ∧
            (Pm ⊢ (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
              A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
              (memRegion (s.sp + 4832#64) 184 ∗ ((s.sp + 5016#64) ↦₆₄ g.cap) ∗ ((s.sp + 5024#64) ↦₆₄ g.ptr) ∗
                ((s.sp + 5032#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 5040#64) 16 ∗
                spqrSendDropJumpTablePlacedExpanded ∗ Frame)))
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
            refine SepWP.seq (mid := (blkPl_427).base + 7196#64)
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
                    memRegion (s.sp + 4832#64) 184 ∗ ((s.sp + 5016#64) ↦₆₄ g.cap) ∗ ((s.sp + 5024#64) ↦₆₄ g.ptr) ∗
                    ((s.sp + 5032#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 5040#64) 16 ∗
                    spqrSendDropJumpTablePlacedExpanded ∗ Frame))) ?_ ?_
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
            (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
          exact ProofLib.SepWP.done hpcf hrunf
            ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 3. `noHeaderReceived` (`idx = 5`, `+7272..+7392`) -/

theorem step_send_drop_inner_noHeaderReceived_32164_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (st : V1State.Chunked.NoHeaderReceived)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.noHeaderReceived st)) ∗
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
  have hloop := step_send_poly_decoder_loop_7360_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedNoHeaderReceivedAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin96 : memRegion (a + 8#64) 40 ∗ memRegion (a + 48#64) 56 ⊢ memRegion (a + 8#64) 96 := by
    rw [ProofLib.memRegion_split (a + 8#64) 40 56 (by decide), BitVec.add_assoc a 8#64 40#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000005#64) ∗ memRegion (a + 8#64) 96 ∗ memRegion (a + 104#64) 120 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000005#64 96 120 104#64 (BitVec.add_assoc a 8#64 96#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin96 hjoin224 ⊢
  let Mid7328 : M.σ → State → SepProp → Prop := fun bst₁ sm Pm =>
    sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
    sm.readReg64 .x23 = x23 ∧
    (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗
      optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4840#64) (st.receivingHdr.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 4880#64) 56 ∗ memRegion (s.sp + 4936#64) 120 ∗
      spqrSendDropJumpTablePlacedExpanded ∗ A.pool lim bst₁ sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
  refine sepWP_seq_fo (mid := (blkPl_427).base + 7328#64)
    (Mid := Mid7328) (Post := innerDropPostExp A lim s x23 Frame) ?_ ?_
  · cases huc : st.uc with
    | none =>
      dsimp only [Mid7328, optProtoUnchunkedNoHeaderReceivedAt, spqrSendDropJumpTablePlacedExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (s.sp + 4880#64)
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
    | some u =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, protoUnchunkedNoHeaderReceivedAt]
      cases hauth : u.auth with
      | none =>
        have hnone40 := optProtoAuthenticatorAt_40_none_entails_memRegion_56 A.repAlloc (s.sp + 4840#64) u.epoch
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
        rw [optProtoAuthenticatorAt_none]; dsimp only [Mid7328, spqrSendDropJumpTablePlacedExpanded]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (s.sp + 4880#64) auth) (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [show s.sp + 4880#64 = (s.sp + 4840#64) + 40#64 from (BitVec.add_assoc s.sp 4840#64 40#64).symm, twoVecHeadersAt_40_eq]
        wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        have hhdr56 := auth40HeadersAt_entails_memRegion_56 (s.sp + 4840#64) ga u.epoch
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
        refine sepWP_seq_fo (mid := (blkPl_427).base + 7308#64)
          (Mid := fun bsta sm Pm =>
            sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x23 = x23 ∧
            (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗
              optProtoPolynomialDecoderAt A.repAlloc (s.sp + 4840#64) (st.receivingHdr.map pbToProtoPolyDecoder) ∗
              ((auth40HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗ ((s.sp + 4928#64) ↦₆₄ u.epoch)) ∗
              memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗
              A.pool lim bsta sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
          (Post := Mid7328) ?_ ?_
        · dsimp only [auth40HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live, spqrSendDropJumpTablePlacedExpanded]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, entails_pool_rfl⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents ga.v1.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
                by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, by wp_norm_goal,
                by simp only [wp_norm, arm64_norm, *], by wp_norm_goal, Entails.of_eq (by sep_ac_rfl)⟩
        · intro bsta sa1 Pa1 hpca1 hruna1 _ ⟨hspa1, htra1, hvregsa1, hx23_a1, hPa1⟩
          refine SepWP.weaken_pre hPa1 ?_; dsimp only [Mid7328]
          have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
          dsimp only [auth40HeadersAt, vecCapPtrDealloc, RustCliAllocBudget.repAlloc_live]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                (by wp_norm_goal : _ = sa1.trace).trans htra1,
                (by wp_norm_goal : _ = calleeSavedVRegs sa1).trans hvregsa1,
                (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, entails_pool_rfl⟩
          · rw [← hspa1, send_stackAt_callee_eq_allocHook sa1.sp]; wp_steps
            wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, bsta); rw [hspa1]
            refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨rustDeallocEvents ga.v2.cap.toNat 1, FreeOnlyEvs.singleton 1 ga.v2.cap.toNat,
                by simp only [wp_norm, arm64_norm, *], (by wp_norm_goal : _ = sa1.sp).trans hspa1,
                (by wp_norm_goal : _ = sa1.trace).trans htra1,
                (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sa1).trans hvregsa1,
                (by wp_norm_goal : _ = sa1.readReg64 .x23).trans hx23_a1, Entails.of_eq (by sep_ac_rfl)⟩
  · intro bst₁ s1 P1 hpc1 hrun1 _ ⟨hsp1, htr1, hvregs1, hx23_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_; dsimp only [innerDropPostExp]
    cases hhdr : st.receivingHdr with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4840#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus)
        (SepWP.focus_weaken hjoin96 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal,
          (by wp_norm_goal : _ = s1.trace).trans htr1, (by wp_norm_goal : _ = s1.sp).trans hsp1,
          (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
          (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1, entails_pool_rfl⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (s.sp + 4840#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40
        (s.sp + 4840#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      dsimp only [RustCliAllocBudget.repAlloc_live]
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine sepWP_seq_fo (mid := (blkPl_427).base + 7544#64)
        (Mid := fun bst₂ sm Pm =>
          sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23 ∧
          (Pm ⊢ (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            A.pool lim bst₂ sm ∗ stackAt s.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗ ((s.sp + 4840#64) ↦₆₄ g.cap) ∗
              ((s.sp + 4848#64) ↦₆₄ g.ptr) ∗ ((s.sp + 4856#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              memRegion (s.sp + 4864#64) 16 ∗ memRegion (s.sp + 4880#64) 56 ∗
              memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame)))
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
          refine SepWP.seq (mid := (blkPl_427).base + 7372#64)
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
                  ((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗ ((s.sp + 4840#64) ↦₆₄ g.cap) ∗
                  ((s.sp + 4848#64) ↦₆₄ g.ptr) ∗ ((s.sp + 4856#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
                  memRegion (s.sp + 4864#64) 16 ∗ memRegion (s.sp + 4880#64) 56 ∗
                  memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))) ?_ ?_
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
          (SepWP.focus_weaken hjoin96 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done hpcf hrunf
          ⟨evs_t, hevs_t, hacp_t, hrunf, htrf, hspf, hx23_f, hvregsf, Entails.of_eq (by sep_ac_rfl)⟩

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudgetAux
