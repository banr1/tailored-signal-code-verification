/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2Placed
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish2
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Relocatable Phase 4 (Part 3) of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Proves the remaining `PolynomialDecoder` share-vector drop loops, looping `InnerState` drop arms,
and full `PqRatchetState` drop dispatch under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession CryptoVerification
open CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.SpqrV1.Layout.L22
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding SepWP.done
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt spqrSendDropJumpTablePlacedAt optProtoPolynomialEncoderAt optProtoUnchunkedCt1SentAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_add_one_sub_one spqrSendPlacedEntry

@[local simp, local arm64_norm]
private theorem send3_noneCap2_add_two_beq_zero : (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl
@[local simp, local arm64_norm]
private theorem send3_noneCap2_add_two_bne_zero : (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.Top.Send.extractLsb_lo_append64
  CryptoVerification.SpqrV1.Top.Send.extractLsb_hi_append64
  ite_zero32_self ite_zero64_self

theorem step_send_poly_decoder_pts_tail_325d4_sp_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s0 s2 : State) (g : VecPin) (x23 : BitVec 64) (F2 : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc2 : s2.pc = spqrSendPlacedEntry + 7544#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp) (htr2 : s2.trace = s0.trace) (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx19_2 : s2.readReg64 .x19 = g.ptr) (hx20_2 : s2.readReg64 .x20 = g.cap) (hx23_2 : s2.readReg64 .x23 = x23)
    (hcap_lt : g.cap.toNat * 24 < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s2
      ((if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool ∗ stackAt s0.sp spqrSendCalleeStack ∗ F2)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        (Q ⊢ A.pool ∗ stackAt s0.sp spqrSendCalleeStack ∗ F2)) := by
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
  have h := step_send_poly_decoder_pts_tail_325d4_placed hdealloc s2 g x23 F2 hpc2 hrun2 hsp2_align hx19_2 hx20_2 hx23_2 hcap_lt
  rwa [hsp2, htr2, hvregs2] at h

/-! ## 1. `ct1Acknowledged` (`idx = 9`, `+6880..+6960`) -/

theorem step_send_drop_inner_ct1Acknowledged_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : V1State.Chunked.Ct1Acknowledged)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.ct1Acknowledged st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hct1_sent := spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_6928_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedCt1AcknowledgedAt, protoUnchunkedCt1SentSize, BitVec.ofNat_eq_ofNat] at hpc hct1_sent hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin168 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 40 ⊢ memRegion (a + 8#64) 168 := by
    rw [ProofLib.memRegion_split (a + 8#64) 128 40 (by decide), BitVec.add_assoc a 8#64 128#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 168 ∗ memRegion (a + 176#64) 48 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000009#64 168 48 176#64 (BitVec.add_assoc a 8#64 168#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin168 hjoin224 ⊢
  refine seq_clean (mid := (blkPl_427).base + 6896#64)
    (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗ memRegion (s.sp + 4840#64) 128 ∗
      optProtoPolynomialDecoderAt A (s.sp + 4968#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 5008#64) 48 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
  · dsimp only [spqrSendDropJumpTablePlacedExpanded]; rw [send_stackAt_callee_eq_dropStack32 s.sp]; wp_steps
    wp_call hct1_sent ⟨s.sp + 4840#64, st.uc⟩; dsimp only [protoUnchunkedCt1SentSize, wp_norm, arm64_norm]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
    cases hek : st.receivingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4968#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin168 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']; let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (s.sp + 4968#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := Drop.cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40 (s.sp + 4968#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7544#64)
        (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ (((s.sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗
            memRegion (s.sp + 4840#64) 128 ∗ ((s.sp + 4968#64) ↦₆₄ g.cap) ∗ ((s.sp + 4976#64) ↦₆₄ g.ptr) ∗
            ((s.sp + 4984#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 4992#64) 16 ∗
            memRegion (s.sp + 5008#64) 48 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]; wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        | cons bs tl =>
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := (blkPl_427).base + 6940#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
              (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗
               memRegion (s.sp + 4840#64) 128 ∗ ((s.sp + 4968#64) ↦₆₄ g.cap) ∗ ((s.sp + 4976#64) ↦₆₄ g.ptr) ∗
               ((s.sp + 4984#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 4992#64) 16 ∗ memRegion (s.sp + 5008#64) 48 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64 ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro s_loop hpc_loop hrun_loop ⟨hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l⟩
            exact SepWP.strengthen_entails_const (poly_pts_loop_post_entails A g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)
              (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop _ (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l)
      · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2⟩
        refine SepWP.seq (htail s2 g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_
        intro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus) (SepWP.focus_weaken hjoin168 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 2. Remaining `PolynomialDecoder` Share-Vector Loops (`6844`, `7092`, `7184`, `7360`, `7508`) -/

theorem step_send_poly_decoder_body_6844_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 6856#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 6844#64) s (vecU8 A cur bs ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro cur cnt bs s Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  refine SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) ?_
  dsimp only [vecCapPtrDealloc]; by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · wp_steps; wp_call hdealloc (vptr, cap.toNat, 1); wp_steps; rw [hsp]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

theorem step_send_poly_decoder_loop_6844_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 6856#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_6844_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23; simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_427).base + 6844#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢; wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1; wp_steps; rw [sep_push_body]
      exact SepWP.mono (ih (cur + 24#64) _ (memRegion cur 24 ∗ Frame) (List.cons_ne_nil _ _) hlen_tl rfl (by assumption)
          hsp1 htr1 hvregs1 hx19_1 hx20_1 (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, add_24_add_8]) hx23_1)
        (fun _ _ _ _ h => ⟨Entails.trans h.1 (cons_len_rejoin_loop bs (bs2 :: tl2) cur hlen), h.2⟩)

theorem step_send_poly_decoder_body_7092_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7104#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7092#64) s (vecU8 A cur bs ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro cur cnt bs s Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  refine SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) ?_
  dsimp only [vecCapPtrDealloc]; by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · wp_steps; wp_call hdealloc (vptr, cap.toNat, 1); wp_steps; rw [hsp]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

theorem step_send_poly_decoder_loop_7092_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7104#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7092_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23; simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_427).base + 7092#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢; wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1; wp_steps; rw [sep_push_body]
      exact SepWP.mono (ih (cur + 24#64) _ (memRegion cur 24 ∗ Frame) (List.cons_ne_nil _ _) hlen_tl rfl (by assumption)
          hsp1 htr1 hvregs1 hx19_1 hx20_1 (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, add_24_add_8]) hx23_1)
        (fun _ _ _ _ h => ⟨Entails.trans h.1 (cons_len_rejoin_loop bs (bs2 :: tl2) cur hlen), h.2⟩)

theorem step_send_poly_decoder_body_7184_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7196#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7184#64) s (vecU8 A cur bs ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro cur cnt bs s Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  refine SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) ?_
  dsimp only [vecCapPtrDealloc]; by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · wp_steps; wp_call hdealloc (vptr, cap.toNat, 1); wp_steps; rw [hsp]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

theorem step_send_poly_decoder_loop_7184_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7196#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7184_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23; simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_427).base + 7184#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢; wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1; wp_steps; rw [sep_push_body]
      exact SepWP.mono (ih (cur + 24#64) _ (memRegion cur 24 ∗ Frame) (List.cons_ne_nil _ _) hlen_tl rfl (by assumption)
          hsp1 htr1 hvregs1 hx19_1 hx20_1 (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, add_24_add_8]) hx23_1)
        (fun _ _ _ _ h => ⟨Entails.trans h.1 (cons_len_rejoin_loop bs (bs2 :: tl2) cur hlen), h.2⟩)

theorem step_send_poly_decoder_body_7360_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7372#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7360#64) s (vecU8 A cur bs ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro cur cnt bs s Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  refine SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) ?_
  dsimp only [vecCapPtrDealloc]; by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · wp_steps; wp_call hdealloc (vptr, cap.toNat, 1); wp_steps; rw [hsp]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

theorem step_send_poly_decoder_loop_7360_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7372#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7360_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23; simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_427).base + 7360#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢; wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1; wp_steps; rw [sep_push_body]
      exact SepWP.mono (ih (cur + 24#64) _ (memRegion cur 24 ∗ Frame) (List.cons_ne_nil _ _) hlen_tl rfl (by assumption)
          hsp1 htr1 hvregs1 hx19_1 hx20_1 (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, add_24_add_8]) hx23_1)
        (fun _ _ _ _ h => ⟨Entails.trans h.1 (cons_len_rejoin_loop bs (bs2 :: tl2) cur hlen), h.2⟩)

theorem step_send_poly_decoder_body_7508_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = spqrSendPlacedEntry + 7520#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7508#64) s (vecU8 A cur bs ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro cur cnt bs s Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  refine SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) ?_
  dsimp only [vecCapPtrDealloc]; by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · wp_steps; wp_call hdealloc (vptr, cap.toNat, 1); wp_steps; rw [hsp]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

theorem step_send_poly_decoder_loop_7508_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64) (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 → s.pc = spqrSendPlacedEntry + 7520#64 → s.status = .Running → s.sp = sp →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 → s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 → s.readReg64 .x23 = x23 →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧ sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x23 = x23) := by
  have hbody := step_send_poly_decoder_body_7508_placed (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at *
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23; simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_427).base + 7508#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧ sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩; rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢; wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1; wp_steps; rw [sep_push_body]
      exact SepWP.mono (ih (cur + 24#64) _ (memRegion cur 24 ∗ Frame) (List.cons_ne_nil _ _) hlen_tl rfl (by assumption)
          hsp1 htr1 hvregs1 hx19_1 hx20_1 (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, add_24_add_8]) hx23_1)
        (fun _ _ _ _ h => ⟨Entails.trans h.1 (cons_len_rejoin_loop bs (bs2 :: tl2) cur hlen), h.2⟩)

/-! ## 3. `ct1Sampled` (`idx = 7`, `+7128..+7216`) -/

theorem step_send_drop_inner_ct1Sampled_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : V1State.Chunked.Ct1Sampled)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = s.sp + 4704#64)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.ct1Sampled st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hct1_sent := spqrSend_dropOptProtoUnchunkedCt1Sent_ok_placed hdealloc
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_7184_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt,
    protoUnchunkedCt1SentSize, protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpc hct1_sent hpoly_enc hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin184 : memRegion a 128 ∗ memRegion (a + 128#64) 56 ⊢ memRegion a 184 := by
    rw [ProofLib.memRegion_split a 128 56 (by decide)]; exact Entails.refl _
  have hjoin224 : memRegion a 184 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 := by
    rw [ProofLib.memRegion_split a 184 40 (by decide)]; exact Entails.refl _
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin184 hjoin224 ⊢
  refine seq_clean_lscl hcl (mid := (blkPl_427).base + 7136#64)
    (P_mid := memRegion (s.sp + 4832#64) 128 ∗ optProtoPolynomialEncoderAt A (s.sp + 4960#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A (s.sp + 5016#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
      spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
  · dsimp only [spqrSendDropJumpTablePlacedExpanded]
    refine SepWP.focus_weaken (optProtoUnchunkedCt1SentAt_expose_tag A (s.sp + 4832#64) st.uc) (by sep_focus) ?_
    wp_pull_exists; rename_i w; wp_focus_pure; rintro ⟨hw_ult, hw_cc⟩
    have hw_ult' : ¬((w + 3#64).ult 2#64 = true) := by rw [hw_ult]; decide
    have hw_cc' : ¬(ConditionHolds .CC (subsPState64 (w ^^^ 0x8000000000000000#64) 11#64) = true) := by rw [hw_cc]; decide
    wp_steps
    refine SepWP.focus_weaken (optProtoUnchunkedCt1SentAt_unexpose_tag A (s.sp + 4832#64) w st.uc) (by sep_focus) ?_
    rw [send_stackAt_callee_eq_dropStack32 s.sp]; wp_call hct1_sent ⟨s.sp + 4832#64, st.uc⟩
    dsimp only [protoUnchunkedCt1SentSize, wp_norm, arm64_norm]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s01 hpc01 hrun01 hcl01 ⟨hsp01, htr01, hvregs01, hx23_01⟩
    have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
    refine seq_clean (mid := (blkPl_427).base + 7152#64)
      (P_mid := memRegion (s.sp + 4832#64) 184 ∗
        optProtoPolynomialDecoderAt A (s.sp + 5016#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
        spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
    · rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]; wp_steps
      wp_call hpoly_enc ⟨s.sp + 4960#64, st.sendingCt1.map pbToProtoPolyEncoder⟩; rw [hsp01]
      dsimp only [protoPolynomialEncoderSize, wp_norm, arm64_norm]
      refine SepWP.focus_weaken hjoin184 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
      cases hek : st.receivingEk with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
        have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 5016#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
        refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']; let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (s.sp + 5016#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := Drop.cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40 (s.sp + 5016#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
        refine seq_clean (mid := (blkPl_427).base + 7544#64)
          (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ (memRegion (s.sp + 4832#64) 184 ∗
              ((s.sp + 5016#64) ↦₆₄ g.cap) ∗ ((s.sp + 5024#64) ↦₆₄ g.ptr) ∗ ((s.sp + 5032#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              memRegion (s.sp + 5040#64) 16 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          | cons bs tl =>
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
            have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := (blkPl_427).base + 7196#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
                (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ memRegion (s.sp + 4832#64) 184 ∗
                 ((s.sp + 5016#64) ↦₆₄ g.cap) ∗ ((s.sp + 5024#64) ↦₆₄ g.ptr) ∗ ((s.sp + 5032#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 5040#64) 16 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
              (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64 ∧ sm.readReg64 .x23 = x23) ?_ ?_
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
            · intro s_loop hpc_loop hrun_loop ⟨hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l⟩
              exact SepWP.strengthen_entails_const (poly_pts_loop_post_entails A g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)
                (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop _ (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l)
        · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2⟩
          refine SepWP.seq (htail s2 g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_
          intro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
          refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 4. `noHeaderReceived` (`idx = 5`, `+7272..+7392`) -/

theorem step_send_drop_inner_noHeaderReceived_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : V1State.Chunked.NoHeaderReceived)
    (x23 : BitVec 64) (Frame : SepProp) (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.noHeaderReceived st)) ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_7360_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt, protoChunkedNoHeaderReceivedAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin96 : memRegion (a + 8#64) 40 ∗ memRegion (a + 48#64) 56 ⊢ memRegion (a + 8#64) 96 := by
    rw [ProofLib.memRegion_split (a + 8#64) 40 56 (by decide), BitVec.add_assoc a 8#64 40#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000005#64) ∗ memRegion (a + 8#64) 96 ∗ memRegion (a + 104#64) 120 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000005#64 96 120 104#64 (BitVec.add_assoc a 8#64 96#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin96 hjoin224 ⊢
  refine seq_clean (mid := (blkPl_427).base + 7328#64)
    (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗ optProtoPolynomialDecoderAt A (s.sp + 4840#64) (st.receivingHdr.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 4880#64) 56 ∗ memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
  · cases huc : st.uc with
    | none =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (s.sp + 4880#64)
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
      refine SepWP.focus_weaken hnone56 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    | some u =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, protoUnchunkedNoHeaderReceivedAt]; cases hauth : u.auth with
      | none =>
        have hnone40 := optProtoAuthenticatorAt_40_none_entails_memRegion_56 A (s.sp + 4840#64) u.epoch; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
        rw [optProtoAuthenticatorAt_none]; dsimp only [spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
        refine SepWP.focus_weaken hnone40 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
      | some auth =>
        rw [optProtoAuthenticatorAt_some]; refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (s.sp + 4880#64) auth) (by sep_focus) ?_
        wp_pull_exists; rename_i ga; rw [show s.sp + 4880#64 = (s.sp + 4840#64) + 40#64 from (BitVec.add_assoc s.sp 4840#64 40#64).symm, twoVecHeadersAt_40_eq]
        wp_focus_pure; intro hga_lt; have hne_none2 := Drop.cap_add_two_beq_zero_false hga_lt; have hne_none1 := Drop.cap_add_one_beq_zero_false hga_lt
        have hhdr56 := auth40HeadersAt_entails_memRegion_56 (s.sp + 4840#64) ga u.epoch; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
        refine seq_clean (mid := (blkPl_427).base + 7308#64)
          (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗ optProtoPolynomialDecoderAt A (s.sp + 4840#64) (st.receivingHdr.map pbToProtoPolyDecoder) ∗
            ((auth40HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ ((s.sp + 4928#64) ↦₆₄ u.epoch)) ∗
            memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
        · dsimp only [auth40HeadersAt, vecCapPtrDealloc, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · intro sa1 hpca1 hruna1 ⟨hspa1, htra1, hvregsa1, hx23_a1⟩
          have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
          dsimp only [auth40HeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine SepWP.focus_weaken hhdr56 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1); rw [hspa1]
            refine SepWP.focus_weaken hhdr56 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩; cases hhdr : st.receivingHdr with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin96 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']; let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (s.sp + 4840#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := Drop.cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40 (s.sp + 4840#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7544#64)
        (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ (((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗
            ((s.sp + 4840#64) ↦₆₄ g.cap) ∗ ((s.sp + 4848#64) ↦₆₄ g.ptr) ∗ ((s.sp + 4856#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            memRegion (s.sp + 4864#64) 16 ∗ memRegion (s.sp + 4880#64) 56 ∗ memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]; wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        | cons bs tl =>
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt; have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := (blkPl_427).base + 7372#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
              (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗
               ((s.sp + 4840#64) ↦₆₄ g.cap) ∗ ((s.sp + 4848#64) ↦₆₄ g.ptr) ∗ ((s.sp + 4856#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               memRegion (s.sp + 4864#64) 16 ∗ memRegion (s.sp + 4880#64) 56 ∗ memRegion (s.sp + 4936#64) 120 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64 ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro s_loop hpc_loop hrun_loop ⟨hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l⟩
            exact SepWP.strengthen_entails_const (poly_pts_loop_post_entails A g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)
              (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop _ (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l)
      · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2⟩
        refine SepWP.seq (htail s2 g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_
        intro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus) (SepWP.focus_weaken hjoin96 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 5. `headerReceived` (`idx = 6`, `+7396..+7540`) -/

theorem step_send_drop_inner_headerReceived_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : V1State.Chunked.HeaderReceived)
    (x23 : BitVec 64) (Frame : SepProp) (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.headerReceived st)) ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_7508_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderReceivedAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin120 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) 40 ⊢ memRegion (a + 8#64) 120 := by
    rw [ProofLib.memRegion_split (a + 8#64) 80 40 (by decide), BitVec.add_assoc a 8#64 80#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000006#64) ∗ memRegion (a + 8#64) 120 ∗ memRegion (a + 128#64) 96 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000006#64 120 96 128#64 (BitVec.add_assoc a 8#64 120#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin120 hjoin224 ⊢
  refine seq_clean (mid := (blkPl_427).base + 7476#64)
    (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s.sp + 4840#64) 80 ∗
      optProtoPolynomialDecoderAt A (s.sp + 4920#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedHeaderReceivedAt_none]; dsimp only [spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone80 := optProtoUnchunked1Vec_none_entails_memRegion_80 (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone80
      refine SepWP.focus_weaken hnone80 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    | some u =>
      rw [optProtoUnchunkedHeaderReceivedAt_some]
      have huc_dealloc := protoUnchunkedHeaderReceivedAt_entails_dealloc A (s.sp + 4840#64) u; simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc_dealloc
      refine SepWP.focus_weaken huc_dealloc (by sep_focus) ?_; wp_pull_exists; rename_i v1; wp_focus_pure; intro hcap1_lt
      have hne_none1 := Drop.cap_add_one_beq_zero_false hcap1_lt
      have hhdr80 := protoUnchunked1VecHeadersAt_entails_memRegion_80' (s.sp + 4840#64) v1; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr80 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7456#64)
        (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗ memRegion (s.sp + 4864#64) 48 ∗
            memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗ optProtoPolynomialDecoderAt A (s.sp + 4920#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          have hnone48 := optProtoAuthenticatorAt_24_none_entails_memRegion_48 A (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
          rw [optProtoAuthenticatorAt_none]; dsimp only [protoUnchunked1VecHeadersAt, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
          refine SepWP.focus_weaken hnone48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]; refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (s.sp + 4864#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [show s.sp + 4864#64 = (s.sp + 4840#64) + 24#64 from (BitVec.add_assoc s.sp 4840#64 24#64).symm, twoVecHeadersAt_24_eq]
          wp_focus_pure; intro hga_lt; have hne_nonea := Drop.cap_add_one_beq_zero_false hga_lt
          have hhdr48 := auth24HeadersAt_entails_memRegion_48 (s.sp + 4840#64) ga; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          refine seq_clean (mid := (blkPl_427).base + 7436#64)
            (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗
                (auth24HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗
              optProtoPolynomialDecoderAt A (s.sp + 4920#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
              memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro sa1 hpca1 hruna1 ⟨hspa1, htra1, hvregsa1, hx19_a1, hx23_a1⟩
            have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
            dsimp only [auth24HeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken hhdr48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1); rw [hspa1]
              refine SepWP.focus_weaken hhdr48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
      · intro s01 hpc01 hrun01 ⟨hsp01, htr01, hvregs01, hx19_01, hx23_01⟩
        have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken hhdr80 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
        · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (v1.ptr, v1.cap.toNat, 1); rw [hsp01]
          refine SepWP.focus_weaken hhdr80 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩; cases hek : st.receivingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4920#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin120 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']; let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (s.sp + 4920#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := Drop.cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40 (s.sp + 4920#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7544#64)
        (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ (((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 4840#64) 80 ∗ ((s.sp + 4920#64) ↦₆₄ g.cap) ∗ ((s.sp + 4928#64) ↦₆₄ g.ptr) ∗
            ((s.sp + 4936#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 4944#64) 16 ∗ memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]; wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        | cons bs tl =>
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt; have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := (blkPl_427).base + 7520#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
              (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗
               memRegion (s.sp + 4840#64) 80 ∗ ((s.sp + 4920#64) ↦₆₄ g.cap) ∗ ((s.sp + 4928#64) ↦₆₄ g.ptr) ∗
               ((s.sp + 4936#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 4944#64) 16 ∗ memRegion (s.sp + 4960#64) 96 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64 ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro s_loop hpc_loop hrun_loop ⟨hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l⟩
            exact SepWP.strengthen_entails_const (poly_pts_loop_post_entails A g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)
              (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop _ (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l)
      · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2⟩
        refine SepWP.seq (htail s2 g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_
        intro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus) (SepWP.focus_weaken hjoin120 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 6. `headerSent` (`idx = 2`, `+6964..+7124`) -/

theorem step_send_drop_inner_headerSent_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : V1State.Chunked.HeaderSent)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.headerSent st)) ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hpoly_enc := spqrSend_dropOptProtoPolyEncoder_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_7092_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderSentAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hpoly_enc hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin136 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) 56 ⊢ memRegion (a + 8#64) 136 := by
    rw [ProofLib.memRegion_split (a + 8#64) 80 56 (by decide), BitVec.add_assoc a 8#64 80#64]; exact Entails.refl _
  have hjoin176 : memRegion (a + 8#64) 136 ∗ memRegion (a + 144#64) 40 ⊢ memRegion (a + 8#64) 176 := by
    rw [ProofLib.memRegion_split (a + 8#64) 136 40 (by decide), BitVec.add_assoc a 8#64 136#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000002#64) ∗ memRegion (a + 8#64) 176 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000002#64 176 40 184#64 (BitVec.add_assoc a 8#64 176#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin136 hjoin176 hjoin224 ⊢
  refine seq_clean_lscl hcl (mid := (blkPl_427).base + 7044#64)
    (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (s.sp + 4840#64) 80 ∗
      optProtoPolynomialEncoderAt A (s.sp + 4920#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentAt_none]; dsimp only [spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone80 := optProtoUnchunked1Vec_none_entails_memRegion_80 (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone80
      refine SepWP.focus_weaken hnone80 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    | some u =>
      rw [optProtoUnchunkedEkSentAt_some]
      have huc_dealloc := protoUnchunkedEkSentAt_entails_dealloc A (s.sp + 4840#64) u; simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc_dealloc
      refine SepWP.focus_weaken huc_dealloc (by sep_focus) ?_; wp_pull_exists; rename_i v1; wp_focus_pure; intro hcap1_lt
      have hne_none1 := Drop.cap_add_one_beq_zero_false hcap1_lt
      have hhdr80 := protoUnchunked1VecHeadersAt_entails_memRegion_80' (s.sp + 4840#64) v1; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr80 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7024#64)
        (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗ memRegion (s.sp + 4864#64) 48 ∗
            memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗ optProtoPolynomialEncoderAt A (s.sp + 4920#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
          optProtoPolynomialDecoderAt A (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          have hnone48 := optProtoAuthenticatorAt_24_none_entails_memRegion_48 A (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
          rw [optProtoAuthenticatorAt_none]; dsimp only [protoUnchunked1VecHeadersAt, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
          refine SepWP.focus_weaken hnone48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]; refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (s.sp + 4864#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [show s.sp + 4864#64 = (s.sp + 4840#64) + 24#64 from (BitVec.add_assoc s.sp 4840#64 24#64).symm, twoVecHeadersAt_24_eq]
          wp_focus_pure; intro hga_lt; have hne_nonea := Drop.cap_add_one_beq_zero_false hga_lt
          have hhdr48 := auth24HeadersAt_entails_memRegion_48 (s.sp + 4840#64) ga; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          refine seq_clean (mid := (blkPl_427).base + 7004#64)
            (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ (protoUnchunked1VecHeadersAt (s.sp + 4840#64) v1 ∗
                (auth24HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (s.sp + 4912#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗
              optProtoPolynomialEncoderAt A (s.sp + 4920#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
              optProtoPolynomialDecoderAt A (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
              memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = v1.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro sa1 hpca1 hruna1 ⟨hspa1, htra1, hvregsa1, hx19_a1, hx23_a1⟩
            have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
            dsimp only [auth24HeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken hhdr48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1); rw [hspa1]
              refine SepWP.focus_weaken hhdr48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
      · intro s01 hpc01 hrun01 ⟨hsp01, htr01, hvregs01, hx19_01, hx23_01⟩
        have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken hhdr80 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
        · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (v1.ptr, v1.cap.toNat, 1); rw [hsp01]
          refine SepWP.focus_weaken hhdr80 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
  · intro s02 hpc02 hrun02 hcl02 ⟨hsp02, htr02, hvregs02, hx23_02⟩
    have hsp02_align : (s02.sp &&& 15#64 == 0#64) = true := by rwa [hsp02]
    refine seq_clean (mid := (blkPl_427).base + 7060#64)
      (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (s.sp + 4840#64) 136 ∗
        optProtoPolynomialDecoderAt A (s.sp + 4976#64) (st.receivingCt1.map pbToProtoPolyDecoder) ∗
        memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
    · rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]; wp_steps
      wp_call hpoly_enc ⟨s.sp + 4920#64, st.sendingEk.map pbToProtoPolyEncoder⟩; rw [hsp02]
      dsimp only [protoPolynomialEncoderSize, wp_norm, arm64_norm]
      refine SepWP.focus_weaken hjoin136 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩; cases hct1 : st.receivingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
        have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4976#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
        refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin176 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']; let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (s.sp + 4976#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := Drop.cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40 (s.sp + 4976#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
        refine seq_clean (mid := (blkPl_427).base + 7544#64)
          (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ (((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗
              memRegion (s.sp + 4840#64) 136 ∗ ((s.sp + 4976#64) ↦₆₄ g.cap) ∗ ((s.sp + 4984#64) ↦₆₄ g.ptr) ∗
              ((s.sp + 4992#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 5000#64) 16 ∗ memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          | cons bs tl =>
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
            have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt; have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := (blkPl_427).base + 7104#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
                (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗
                 memRegion (s.sp + 4840#64) 136 ∗ ((s.sp + 4976#64) ↦₆₄ g.cap) ∗ ((s.sp + 4984#64) ↦₆₄ g.ptr) ∗
                 ((s.sp + 4992#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 5000#64) 16 ∗ memRegion (s.sp + 5016#64) 40 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
              (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64 ∧ sm.readReg64 .x23 = x23) ?_ ?_
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
            · intro s_loop hpc_loop hrun_loop ⟨hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l⟩
              exact SepWP.strengthen_entails_const (poly_pts_loop_post_entails A g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)
                (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop _ (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l)
        · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2⟩
          refine SepWP.seq (htail s2 g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_
          intro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
          refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus) (SepWP.focus_weaken hjoin176 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 7. `ekSentCt1Received` (`idx = 4`, `+6712..+6876`) -/

theorem step_send_drop_inner_ekSentCt1Received_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : V1State.Chunked.EkSentCt1Received)
    (x23 : BitVec 64) (Frame : SepProp) (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.ekSentCt1Received st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hloop := step_send_poly_decoder_loop_6844_placed (ext := ext) hdealloc_raw
  have htail := step_send_poly_decoder_pts_tail_325d4_sp_placed hdealloc s
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedEkSentCt1ReceivedAt, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hloop htail ⊢
  let a := s.sp + 4832#64
  have hjoin144 : memRegion (a + 8#64) 104 ∗ memRegion (a + 112#64) 40 ⊢ memRegion (a + 8#64) 144 := by
    rw [ProofLib.memRegion_split (a + 8#64) 104 40 (by decide), BitVec.add_assoc a 8#64 104#64]; exact Entails.refl _
  have hjoin224 : (a ↦₆₄ 0x8000000000000004#64) ∗ memRegion (a + 8#64) 144 ∗ memRegion (a + 152#64) 72 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000004#64 144 72 152#64 (BitVec.add_assoc a 8#64 144#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin144 hjoin224 ⊢
  refine seq_clean (mid := (blkPl_427).base + 6812#64)
    (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s.sp + 4840#64) 104 ∗
      optProtoPolynomialDecoderAt A (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
      memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]; dsimp only [spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone104 := optProtoUnchunked2Vec_none_entails_memRegion_104 (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone104
      refine SepWP.focus_weaken hnone104 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      have huc_dealloc := protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A (s.sp + 4840#64) u; simp only [BitVec.add_assoc, BitVec.reduceAdd] at huc_dealloc
      refine SepWP.focus_weaken huc_dealloc (by sep_focus) ?_; wp_pull_exists; rename_i g; wp_focus_pure; intro hcap1_lt
      have hne_none1 := Drop.cap_add_one_beq_zero_false hcap1_lt
      have hhdr104 := protoUnchunked2VecHeadersAt_entails_memRegion_104' (s.sp + 4840#64) g; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr104 ⊢
      refine seq_clean (mid := (blkPl_427).base + 6772#64)
        (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ (protoUnchunked2VecHeadersAt (s.sp + 4840#64) g ∗ memRegion (s.sp + 4888#64) 48 ∗
            memRegion (s.sp + 4936#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
          optProtoPolynomialDecoderAt A (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
          memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          have hnone48 := optProtoAuthenticatorAt_48_none_entails_memRegion_48 A (s.sp + 4840#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
          rw [optProtoAuthenticatorAt_none]; dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
          refine SepWP.focus_weaken hnone48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (s.sp + 4888#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [show s.sp + 4888#64 = (s.sp + 4840#64) + 48#64 from (BitVec.add_assoc s.sp 4840#64 48#64).symm, twoVecHeadersAt_48_eq]
          wp_focus_pure; intro hga_lt; have hne_nonea := Drop.cap_add_one_beq_zero_false hga_lt
          have hhdr48 := auth48HeadersAt_entails_memRegion_48 (s.sp + 4840#64) ga; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          refine seq_clean (mid := (blkPl_427).base + 6752#64)
            (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ (protoUnchunked2VecHeadersAt (s.sp + 4840#64) g ∗
                (auth48HeadersAt (s.sp + 4840#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
                memRegion (s.sp + 4936#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialDecoderAt A (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
              memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc, spqrSendDropJumpTablePlacedExpanded]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
              exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro sa1 hpca1 hruna1 ⟨hspa1, htra1, hvregsa1, hx19_a1, hx23_a1⟩
            have hspa1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hspa1]
            dsimp only [auth48HeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken hhdr48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
            · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1); rw [hspa1]
              refine SepWP.focus_weaken hhdr48 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
      · intro s01 hpc01 hrun01 ⟨hsp01, htr01, hvregs01, hx19_01, hx23_01⟩
        have hsp01_align : (s01.sp &&& 15#64 == 0#64) = true := by rwa [hsp01]
        refine seq_clean (mid := (blkPl_427).base + 6792#64)
          (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ (protoUnchunked2VecHeadersAt (s.sp + 4840#64) g ∗ memRegion (s.sp + 4888#64) 48 ∗
              memRegion (s.sp + 4936#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ optProtoPolynomialDecoderAt A (s.sp + 4944#64) (st.receivingCt2.map pbToProtoPolyDecoder) ∗
            memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23) ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (g.v1.ptr, g.v1.cap.toNat, 1); rw [hsp01]
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · intro s02 hpc02 hrun02 ⟨hsp02, htr02, hvregs02, hx23_02⟩
          have hsp02_align : (s02.sp &&& 15#64 == 0#64) = true := by rwa [hsp02]
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine SepWP.focus_weaken hhdr104 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps; wp_call hdealloc_raw (g.v2.ptr, g.v2.cap.toNat, 1); rw [hsp02]
            refine SepWP.focus_weaken hhdr104 (by sep_focus) (ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
    cases hct2 : st.receivingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none', BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
      have hnone40 := optProtoPolyDecoder_none_entails_memRegion_40 (s.sp + 4944#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone40
      refine SepWP.focus_weaken hnone40 (by sep_focus) (SepWP.focus_weaken hjoin144 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_))
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']; let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (s.sp + 4944#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := Drop.cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 := protoPolyDecoderHeaders_entails_memRegion_40 (s.sp + 4944#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr40 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7544#64)
        (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ (((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗
            memRegion (s.sp + 4840#64) 104 ∗ ((s.sp + 4944#64) ↦₆₄ g.cap) ∗ ((s.sp + 4952#64) ↦₆₄ g.ptr) ∗
            ((s.sp + 4960#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (s.sp + 4968#64) 16 ∗
            memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧ sm.readReg64 .x23 = x23) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢; cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]; wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        | cons bs tl =>
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by have := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 (by simp) hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := (blkPl_427).base + 6856#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
              (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗
               memRegion (s.sp + 4840#64) 104 ∗ ((s.sp + 4944#64) ↦₆₄ g.cap) ∗ ((s.sp + 4952#64) ↦₆₄ g.ptr) ∗
               ((s.sp + 4960#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ memRegion (s.sp + 4968#64) 16 ∗
               memRegion (s.sp + 4984#64) 72 ∗ spqrSendDropJumpTablePlacedExpanded ∗ Frame))
            (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64 ∧ sm.readReg64 .x23 = x23) ?_ ?_
          · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · intro s_loop hpc_loop hrun_loop ⟨hsp_l, htr_l, hvregs_l, hx19_l, hx20_l, hx21_l, hx22_l, hx23_l⟩
            exact SepWP.strengthen_entails_const (poly_pts_loop_post_entails A g (bs :: tl).length s.sp _ hpts_le hpts_cap_lt)
              (hloop s s.sp g.ptr g.cap x23 hsp_align (bs :: tl) g.ptr s_loop _ (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hsp_l htr_l hvregs_l hx19_l hx20_l hx21_l hx22_l hx23_l)
      · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx19_2, hx20_2, hx23_2⟩
        refine SepWP.seq (htail s2 g x23 _ hsp_align hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx23_2 hpts_cap_lt) ?_
        intro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine SepWP.weaken_pre hQf (SepWP.focus_weaken hhdr40 (by sep_focus) (SepWP.focus_weaken hjoin144 (by sep_focus) (SepWP.focus_weaken hjoin224 (by sep_focus) ?_)))
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 8. Top-Level `step_send_drop_inner_32164_placed`, `step_send_drop_pq_state_32134_placed`, and `step_send_finish_320a4_placed` -/

theorem step_send_drop_inner_32164_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (inner : Option PqRatchetState.Inner)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = s.sp + 4704#64)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (optProtoPqRatchetInnerAt A (s.sp + 4832#64) inner ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  rcases inner with _ | ⟨⟨_ | st⟩⟩
  · exact @step_send_drop_inner_none_32164_placed _ A ext s x23 _ hpc hrun hsp_align hx23
  · exact @step_send_drop_inner_v1_none_32164_placed _ A ext s x23 _ hpc hrun hsp_align hx23
  · cases st with
    | keysUnsampled st => exact step_send_drop_inner_keysUnsampled_32164_placed hdealloc s st x23 Frame hpc hrun hsp_align hx23
    | keysSampled st => exact step_send_drop_inner_keysSampled_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx23
    | headerSent st => exact step_send_drop_inner_headerSent_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx23
    | ct1Received st => exact step_send_drop_inner_ct1Received_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx23
    | ekSentCt1Received st => exact step_send_drop_inner_ekSentCt1Received_32164_placed hdealloc s st x23 Frame hpc hrun hsp_align hx23
    | noHeaderReceived st => exact step_send_drop_inner_noHeaderReceived_32164_placed hdealloc s st x23 Frame hpc hrun hsp_align hx23
    | headerReceived st => exact step_send_drop_inner_headerReceived_32164_placed hdealloc s st x23 Frame hpc hrun hsp_align hx23
    | ct1Sampled st => exact step_send_drop_inner_ct1Sampled_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx19 hx23
    | ekReceivedCt1Sampled st => exact step_send_drop_inner_ekReceivedCt1Sampled_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx23
    | ct1Acknowledged st => exact step_send_drop_inner_ct1Acknowledged_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx23
    | ct2Sampled st => exact step_send_drop_inner_ct2Sampled_32164_placed hdealloc s st x23 Frame hcl hpc hrun hsp_align hx23

theorem step_send_drop_pq_state_32134_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (st : PqRatchetState)
    (x23 : BitVec 64) (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6360#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : (s.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (Drop.protoPqRatchetStateAt A (s.sp + 4704#64) st ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4704#64) 352 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hjoin352 : memRegion (s.sp + 4704#64) 128 ∗ memRegion (s.sp + 4832#64) 224 ⊢ memRegion (s.sp + 4704#64) 352 := by
    have h4832 : (s.sp + 4704#64) + 128#64 = s.sp + 4832#64 := by bv_omega
    rw [← h4832, ProofLib.memRegion_split (s.sp + 4704#64) 128 224 (by decide)]; exact Entails.refl _
  dsimp only [Drop.protoPqRatchetStateAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (sepWP_seq_lscl hcl (SepWP.mono (step_send_drop_vn_chain_32134_placed hdealloc s st.versionNegotiation st.chain x23
      (optProtoPqRatchetInnerAt A (s.sp + 4832#64) st.inner ∗ spqrSendDropJumpTablePlacedAt ∗ Frame) hcl hpc hrun hsp_align hx23 hx25) ?_))
  intro s1 Q1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, hx23_1, hvregs1, hQ1⟩ hcl1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
  have hx19_1' : s1.readReg64 .x19 = s1.sp + 4704#64 := by rw [hsp1]; exact hx19_1
  rw [← hsp1] at hQ1
  refine SepWP.weaken_pre (Entails.trans hQ1 (Entails.of_eq (by ac_rfl)))
    (SepWP.mono (step_send_drop_inner_32164_placed hdealloc s1 st.inner x23
      (memRegion (s1.sp + 4704#64) 128 ∗ Frame) hcl1 hpc1 hrun1 hsp1_align hx19_1' hx23_1) ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
  refine ⟨hrunf, htrf.trans htr1, hspf.trans hsp1, hx23_f, hvregsf.trans hvregs1, ?_⟩; rw [hsp1] at hQf
  exact Entails.trans hQf (Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hjoin352))

theorem step_send_finish_320a4_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext) (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = spqrSendPlacedEntry + 6216#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hflag : x21 = noneCap ∨ BitVec.truncate 32 v_20 = 0#32) (hx25_ch : (x25 + 1#64 == 0#64) = !st.chain.isSome)
    (hret_align : (ret &&& 7#64 == 0#64) = true) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (memRegion ret 72 ∗ vecU8 A (s.sp + 1424#64) stBytes ∗ vecU8 A (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A s.sp key ∗ ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
        pqRatchetStatePBPinnedAt A g (s.sp + 4704#64) st ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗ memRegion (s.sp + 1424#64) 24 ∗
          memRegion (s.sp + 4080#64) 24 ∗ memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 4704#64) 352 ∗
          memRegion (s.sp + 7136#64) 16 ∗ spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  refine SepWP.focus_weaken (pqRatchetStatePBPinnedAt_entails_proto A g (s.sp + 4704#64) st) (by sep_focus) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (sepWP_seq_lscl hcl (SepWP.mono (step_send_build_result_320a4_placed hdealloc s ret v_20 x21 x23 x25 x27 stBytes msgBytes key
      (Drop.protoPqRatchetStateAt A (s.sp + 4704#64) st ∗ spqrSendDropJumpTablePlacedAt ∗ Frame)
      hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 hx28 hret_align hsp_align) ?_))
  intro s1 Q1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx25_1, _, hvregs1, hQ1⟩ hcl1
  have hflag1 : s1.readReg64 .x21 = noneCap ∨ s1.readReg32 .x19 = 0#32 := by
    rcases hflag with h21 | h20
    · left; rw [hx21_1, h21]
    · right; simp only [State.readReg32, hx19_1, h20]
  refine sepWP_seq_lscl hcl1 (SepWP.mono (step_send_epoch_dealloc_32114_placed s1 x23 x25 Q1 hpc1 hrun1 hx23_1 hx25_1 hflag1) ?_)
  intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hx25_2, hvregs2, hQ2⟩ hcl2
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2, hsp1]
  have hx25_2' : (s2.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome := by rw [hx25_2, hx25_ch]
  have hQ2' := Entails.trans hQ2 hQ1; rw [← hsp1, ← hsp2] at hQ2'
  refine SepWP.weaken_pre (Entails.trans hQ2' (Entails.of_eq (by ac_rfl)))
    (SepWP.mono (step_send_drop_pq_state_32134_placed hdealloc s2 st x23
      (spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
        memRegion (s2.sp + 8#64) 8 ∗ memRegion (s2.sp + 24#64) 24 ∗
        memRegion (s2.sp + 1424#64) 24 ∗ memRegion (s2.sp + 4080#64) 24 ∗
        memRegion (s2.sp + 4192#64) 48 ∗ memRegion (s2.sp + 7136#64) 16 ∗ Frame)
      hcl2 hpc2 hrun2 hsp2_align hx23_2 hx25_2') ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
  refine ⟨hrunf, htrf.trans (htr2.trans htr1), hspf.trans (hsp2.trans hsp1), hx23_f, hvregsf.trans (hvregs2.trans hvregs1), ?_⟩
  rw [hsp2, hsp1] at hQf; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.SpqrV1.Top.Send
