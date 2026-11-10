/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPoly
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Phase 4 (Part 2) of `spqr::send::<signal_session_ratchet::Coins>`: Non-Looping `InnerState` Drops

Proves the non-looping `InnerState` drop arms and shared `PolynomialDecoder` tail and
`pts` drop loop (`+6928..+6960`) for the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession

open CryptoVerification


open CryptoVerification.CodeLayout

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr v1StatePBPinnedAt CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt optProtoPolynomialEncoderAt

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]")

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]")

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]")

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_stub% "__rustc::__rust_dealloc")

attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

/-- `entry + 7568#64 -> entry + 7632#64`: drops
    `uc : Option V1State.Unchunked.Ct2Sent` at `s.sp + 4896#64` and sets `x19 = s.sp + 4704#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ct2Sent_7568 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (uc : Option V1State.Unchunked.Ct2Sent) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7568#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7632#64) s
      (optProtoUnchunkedCt2SentAt A (s.sp + 4896#64) uc ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.sp + 4704#64 ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4896#64) 56 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 7568 64
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  cases uc with
  | none =>
    dsimp only [optProtoUnchunkedCt2SentAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (s.sp + 4896#64)
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
    refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | some u =>
    dsimp only [optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt]
    cases hauth : u.auth with
    | none =>
      have hnone64 := optProtoAuthenticatorAt_64_none_entails_memRegion_56 A (s.sp + 4832#64) u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone64
      rw [optProtoAuthenticatorAt_none]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      refine SepWP.focus_weaken hnone64 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken
        (protoAuthenticatorAt_entails_dealloc A (s.sp + 4896#64) auth)
        (by sep_focus) ?_
      wp_pull_exists; rename_i ga
      rw [show s.sp + 4896#64 = (s.sp + 4832#64) + 64#64 from
        (BitVec.add_assoc s.sp 4832#64 64#64).symm, twoVecHeadersAt_64_eq]
      wp_focus_pure; intro hga_lt
      have hne_none2 := Drop.cap_add_two_beq_zero_false hga_lt
      have hne_none1 := Drop.cap_add_one_beq_zero_false hga_lt
      have hhdr56 := auth64HeadersAt_entails_memRegion_56 (s.sp + 4832#64) ga u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
      refine seq_clean (mid := entry + 7612#64)
        (P_mid := ((auth64HeadersAt (s.sp + 4832#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
            ((s.sp + 4944#64) ↦₆₄ u.epoch)) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .x19 = s.sp + 4704#64 ∧ sm.readReg64 .x23 = x23)
        ?_ ?_
      · dsimp only [auth64HeadersAt, vecCapPtrDealloc]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · intro sa1 hpca1 hruna1 ⟨hsp_a1, htr_a1, hvregs_a1, hx19_a1, hx23_a1⟩
        have hsp_a1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hsp_a1]
        dsimp only [auth64HeadersAt, vecCapPtrDealloc]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1)
          rw [hsp_a1]
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `entry + 6408#64 -> entry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.ct2Sampled st)⟩)` (`idx = 10`, target `+7568 = entry + 7568#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_inner_ct2Sampled_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (st : V1State.Chunked.Ct2Sampled) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.ct2Sampled st)) ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (dropOptProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 18876) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]") (by decide))
    (CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_ok_ext hdealloc)
  have huc : ∀ (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7568#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7632#64) s1
        (optProtoUnchunkedCt2SentAt A (s1.sp + 4896#64) st.uc ∗
          A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
            optProtoPolynomialEncoderAt A (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 4952#64) 104 ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
        (fun sf Q =>
          sf.status = .Running ∧
          sf.trace = s1.trace ∧
          sf.sp = s1.sp ∧
          sf.readReg64 .x19 = s1.sp + 4704#64 ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
          (Q ⊢ memRegion (s1.sp + 4896#64) 56 ∗
            A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
              optProtoPolynomialEncoderAt A (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
              memRegion (s.sp + 4952#64) 104 ∗
              CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))) :=
    fun s1 hpc1 hrun1 hsp1_align hx23_1 =>
      CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ct2Sent_7568 hdealloc s1 st.uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6408 40
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 7632 12
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt2SampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
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
  refine seq_clean (mid := entry + 7568#64)
    (P_mid := optProtoUnchunkedCt2SentAt A (s.sp + 4896#64) st.uc ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
      (((s.sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
        optProtoPolynomialEncoderAt A (s.sp + 4840#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
        memRegion (s.sp + 4952#64) 104 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
    ?_ ?_
  · wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.of_eq (by ac_rfl),
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine SepWP.seq huc1 ?_
    intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx19_2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_enc ⟨s.sp + 4840#64, st.sendingCt2.map pbToProtoPolyEncoder⟩
    wp_steps
    rw [hsp2]
    dsimp only [protoPolynomialEncoderSize]
    refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `entry + 6472#64 -> entry + 6572#64`: drops
    `uc : Option V1State.Unchunked.EkSentCt1Received` at `s.sp + 4840#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ekSentCt1Received_6472 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (uc : Option V1State.Unchunked.EkSentCt1Received) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6472#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6572#64) s
      (optProtoUnchunkedEkSentCt1ReceivedAt A (s.sp + 4840#64) uc ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4840#64) 104 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6472 100
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  let a := s.sp + 4840#64
  cases uc with
  | none =>
    rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
    have hnone104 := optProtoUnchunked2Vec_none_entails_memRegion_104 a
    simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone104 ⊢
    wp_steps
    refine SepWP.focus_weaken hnone104 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | some u =>
    rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
    refine SepWP.focus_weaken
      (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A (s.sp + 4840#64) u)
      (by sep_focus) ?_
    wp_pull_exists; rename_i g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := Drop.cap_add_one_beq_zero_false hcap1_lt
    have hhdr104 := protoUnchunked2VecHeadersAt_entails_memRegion_104' a g
    refine seq_clean (mid := entry + 6532#64)
      (P_mid := (protoUnchunked2VecHeadersAt a g ∗
          memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23)
      ?_ ?_
    · cases hauth : u.auth with
      | none =>
        have hnone48 := optProtoAuthenticatorAt_48_none_entails_memRegion_48 A a
        rw [show s.sp + 4840#64 + 48#64 = a + 48#64 from rfl, optProtoAuthenticatorAt_48_none]
        dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone48 ⊢
        wp_steps
        refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.of_eq (by ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken
          (protoAuthenticatorAt_entails_dealloc A ((s.sp + 4840#64) + 48#64) auth)
          (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [show (s.sp + 4840#64) + 48#64 = a + 48#64 from rfl, twoVecHeadersAt_48_eq]
        wp_focus_pure; intro hga_lt
        have hne_nonea := Drop.cap_add_one_beq_zero_false hga_lt
        have hhdr48 := auth48HeadersAt_entails_memRegion_48 a ga
        refine seq_clean (mid := entry + 6512#64)
          (P_mid := (protoUnchunked2VecHeadersAt a g ∗
              (auth48HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
            A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23)
          ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · intro sa1 hpca1 hruna1 ⟨hsp_a1, htr_a1, hvregs_a1, hx19_a1, hx23_a1⟩
          have hsp_a1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hsp_a1]
          dsimp only [auth48HeadersAt, vecCapPtrDealloc]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1)
            rw [hsp_a1]
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx23_1⟩
      have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
      refine seq_clean (mid := entry + 6552#64)
        (P_mid := (protoUnchunked2VecHeadersAt a g ∗
            memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
        ?_ ?_
      · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (g.v1.ptr, g.v1.cap.toNat, 1)
          rw [hsp1]
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx23_2⟩
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
        dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr104 ⊢
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (g.v2.ptr, g.v2.cap.toNat, 1)
          rw [hsp2]
          refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `entry + 6408#64 -> entry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.ct1Received st)⟩)` (`idx = 3`, target `+6472 = entry + 6472#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_inner_ct1Received_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (st : V1State.Chunked.Ct1Received) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (halign : b &&& 0xfff#64 = 0#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.ct1Received st)) ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (dropOptProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 18876) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]") (by decide))
    (CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_ok_ext hdealloc)
  have huc : ∀ (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6472#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6572#64) s1
        (optProtoUnchunkedEkSentCt1ReceivedAt A (s1.sp + 4840#64) st.uc ∗
          A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
            optProtoPolynomialEncoderAt A (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5000#64) 56 ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
        (fun sf Q =>
          sf.status = .Running ∧
          sf.trace = s1.trace ∧
          sf.sp = s1.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
          (Q ⊢ memRegion (s1.sp + 4840#64) 104 ∗
            A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
              optProtoPolynomialEncoderAt A (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
              memRegion (s.sp + 5000#64) 56 ∗
              CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))) :=
    fun s1 hpc1 hrun1 hsp1_align hx23_1 =>
      CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ekSentCt1Received_6472 hdealloc s1 st.uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  have hadrp := CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_3218c (b := b) (H := Rust.withPanics ext) halign
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6408 64
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6572 20
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt1ReceivedAt,
    BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
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
  refine seq_clean (mid := entry + 6472#64)
    (P_mid := optProtoUnchunkedEkSentCt1ReceivedAt A (s.sp + 4840#64) st.uc ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
      (((s.sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗
        optProtoPolynomialEncoderAt A (s.sp + 4944#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
        memRegion (s.sp + 5000#64) 56 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
    ?_ ?_
  · rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt_eq_expanded]
    dsimp only [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableExpanded]
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.of_eq (by ac_rfl),
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine SepWP.seq huc1 ?_
    intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_enc ⟨s.sp + 4944#64, st.sendingEk.map pbToProtoPolyEncoder⟩
    wp_steps
    rw [hsp2]
    dsimp only [protoPolynomialEncoderSize]
    refine SepWP.focus_weaken hjoin160 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `entry + 6408#64 -> entry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.keysSampled st)⟩)` (`idx = 1`, target `+6472 = entry + 6472#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_inner_keysSampled_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (st : V1State.Chunked.KeysSampled) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (halign : b &&& 0xfff#64 = 0#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.keysSampled st)) ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (dropOptProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 18876) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]") (by decide))
    (CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_ok_ext hdealloc)
  have huc : ∀ (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6472#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6572#64) s1
        (optProtoUnchunkedEkSentCt1ReceivedAt A (s1.sp + 4840#64)
            (keysSampledToCt1Received st).uc ∗
          A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
            optProtoPolynomialEncoderAt A (s.sp + 4944#64)
              ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5000#64) 56 ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
        (fun sf Q =>
          sf.status = .Running ∧
          sf.trace = s1.trace ∧
          sf.sp = s1.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
          (Q ⊢ memRegion (s1.sp + 4840#64) 104 ∗
            A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
              optProtoPolynomialEncoderAt A (s.sp + 4944#64)
                ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
              memRegion (s.sp + 5000#64) 56 ∗
              CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))) :=
    fun s1 hpc1 hrun1 hsp1_align hx23_1 =>
      CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ekSentCt1Received_6472 hdealloc s1 (keysSampledToCt1Received st).uc x23 _
        hpc1 hrun1 hsp1_align hx23_1
  have hadrp := CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_3218c (b := b) (H := Rust.withPanics ext) halign
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6408 64
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6572 20
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, optProtoInnerStateAt,
    protoInnerStateAt, BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc hadrp ⊢
  rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]
  dsimp only [protoChunkedCt1ReceivedAt]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
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
  refine seq_clean (mid := entry + 6472#64)
    (P_mid := optProtoUnchunkedEkSentCt1ReceivedAt A (s.sp + 4840#64)
        (keysSampledToCt1Received st).uc ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
      (((s.sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗
        optProtoPolynomialEncoderAt A (s.sp + 4944#64)
          ((keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder) ∗
        memRegion (s.sp + 5000#64) 56 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
    ?_ ?_
  · rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt_eq_expanded]
    dsimp only [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableExpanded]
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.of_eq (by ac_rfl),
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine SepWP.seq huc1 ?_
    intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_enc ⟨s.sp + 4944#64,
      (keysSampledToCt1Received st).sendingEk.map pbToProtoPolyEncoder⟩
    wp_steps
    rw [hsp2]
    dsimp only [protoPolynomialEncoderSize]
    refine SepWP.focus_weaken hjoin160 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `entry + 7644#64 -> entry + 7764#64`: drops
    `uc : Option V1State.Unchunked.Ct1SentEkReceived` at `s.sp + 4840#64`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ct1SentEkReceived_7644 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (uc : Option V1State.Unchunked.Ct1SentEkReceived) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7644#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7764#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A (s.sp + 4840#64) uc ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4840#64) 128 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 7644 120
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  let a := s.sp + 4840#64
  cases uc with
  | none =>
    have hnone128 := optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A a
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none] at hnone128 ⊢
    simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone128 ⊢
    wp_steps
    refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    refine SepWP.focus_weaken
      (protoUnchunkedCt1SentEkReceivedAt_entails_dealloc A (s.sp + 4840#64) u)
      (by sep_focus) ?_
    wp_pull_exists; rename_i g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := Drop.cap_add_one_beq_zero_false hcap1_lt
    have hhdr128 := protoUnchunked3VecHeadersAt_entails_memRegion_128' a g
    refine seq_clean (mid := entry + 7704#64)
      (P_mid := (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23)
      ?_ ?_
    · cases hauth : u.auth with
      | none =>
        have hnone48 := optProtoAuthenticatorAt_72_none_entails_memRegion_48 A a
        rw [show s.sp + 4840#64 + 72#64 = a + 72#64 from rfl, optProtoAuthenticatorAt_72_none]
        dsimp only [protoUnchunked3VecHeadersAt]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hnone48 ⊢
        wp_steps
        refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.of_eq (by ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken
          (protoAuthenticatorAt_entails_dealloc A ((s.sp + 4840#64) + 72#64) auth)
          (by sep_focus) ?_
        wp_pull_exists; rename_i ga
        rw [show (s.sp + 4840#64) + 72#64 = a + 72#64 from rfl, twoVecHeadersAt_72_eq]
        wp_focus_pure; intro hga_lt
        have hne_nonea := Drop.cap_add_one_beq_zero_false hga_lt
        have hhdr48 := auth72HeadersAt_entails_memRegion_48' a ga
        refine seq_clean (mid := entry + 7684#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
              (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
            sm.readReg64 .x19 = g.v1.cap ∧ sm.readReg64 .x23 = x23)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · intro sa1 hpca1 hruna1 ⟨hsp_a1, htr_a1, hvregs_a1, hx19_a1, hx23_a1⟩
          have hsp_a1_align : (sa1.sp &&& 15#64 == 0#64) = true := by rwa [hsp_a1]
          dsimp only [auth72HeadersAt, vecCapPtrDealloc]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr48 ⊢
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1)
            rw [hsp_a1]
            refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx23_1⟩
      have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
      refine seq_clean (mid := entry + 7724#64)
        (P_mid := (protoUnchunked3VecHeadersAt a g ∗
            memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (g.v1.ptr, g.v1.cap.toNat, 1)
          rw [hsp1]
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2, hx23_2⟩
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
        refine seq_clean (mid := entry + 7744#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
              memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_raw (g.v2.ptr, g.v2.cap.toNat, 1)
            rw [hsp2]
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.of_eq (by ac_rfl),
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · intro s3 hpc3 hrun3 ⟨hsp3, htr3, hvregs3, hx23_3⟩
          have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rwa [hsp3]
          dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
          simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hhdr128 ⊢
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
          · rw [send_stackAt_callee_eq_allocHook s.sp]
            wp_steps
            wp_call hdealloc_raw (g.v3.ptr, g.v3.cap.toNat, 1)
            rw [hsp3]
            refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
            exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `entry + 6408#64 -> entry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.ekReceivedCt1Sampled st)⟩)` (`idx = 8`, target `+7644 = entry + 7644#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_inner_ekReceivedCt1Sampled_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (st : V1State.Chunked.EkReceivedCt1Sampled) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (halign : b &&& 0xfff#64 = 0#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.ekReceivedCt1Sampled st)) ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
          CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hpoly_enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (dropOptProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 18876) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]") (by decide))
    (CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_ok_ext hdealloc)
  have huc : ∀ (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7644#64 →
      s1.status = .Running →
      (s1.sp &&& 15#64 == 0#64) = true →
      s1.readReg64 .x23 = x23 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7764#64) s1
        (optProtoUnchunkedCt1SentEkReceivedAt A (s1.sp + 4840#64) st.uc ∗
          A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
          (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
            optProtoPolynomialEncoderAt A (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
            memRegion (s.sp + 5024#64) 32 ∗
            CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
        (fun sf Q =>
          sf.status = .Running ∧
          sf.trace = s1.trace ∧
          sf.sp = s1.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s1 ∧
          (Q ⊢ memRegion (s1.sp + 4840#64) 128 ∗
            A.pool ∗ stackAt s1.sp spqrSendCalleeStack ∗
            (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
              optProtoPolynomialEncoderAt A (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
              memRegion (s.sp + 5024#64) 32 ∗
              CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))) :=
    fun s1 hpc1 hrun1 hsp1_align hx23_1 =>
      CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_ct1SentEkReceived_7644 hdealloc s1 st.uc x23 _ hpc1 hrun1 hsp1_align hx23_1
  have hadrp := CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_3218c (b := b) (H := Rust.withPanics ext) halign
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6408 64
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 7764 20
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hpoly_enc huc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
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
  refine seq_clean (mid := entry + 7644#64)
    (P_mid := optProtoUnchunkedCt1SentEkReceivedAt A (s.sp + 4840#64) st.uc ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗
      (((s.sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗
        optProtoPolynomialEncoderAt A (s.sp + 4968#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
        memRegion (s.sp + 5024#64) 32 ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame))
    (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.readReg64 .x23 = x23)
    ?_ ?_
  · rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt_eq_expanded]
    dsimp only [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableExpanded]
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.of_eq (by ac_rfl),
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx23_1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    have huc1 := huc s1 hpc1 hrun1 hsp1_align hx23_1
    rw [hsp1] at huc1
    refine SepWP.seq huc1 ?_
    intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hvregs2, hQ2⟩
    refine SepWP.weaken_pre hQ2 ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
    rw [stackAt_spqrSendCallee_eq_dropStack64 s.sp]
    wp_steps
    wp_call hpoly_enc ⟨s.sp + 4968#64, st.sendingCt1.map pbToProtoPolyEncoder⟩
    wp_steps
    rw [hsp2]
    dsimp only [protoPolynomialEncoderSize]
    refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-! ## 1. Shared `PolynomialDecoder` Tail (`+7544 -> +4600`) & Loop (`+6928..+6960`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_poly_decoder_pts_tail_325d4 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (g : VecPin) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7544#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = g.ptr)
    (hx20 : s.readReg64 .x20 = g.cap)
    (hx23 : s.readReg64 .x23 = x23)
    (hpts_cap_lt : g.cap.toNat * 24 < 2 ^ 63) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      ((if g.cap = 0 then emp
        else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 7544 24
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4596 4
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  by_cases hc : g.cap = 0#64
  · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj] at hx20 ⊢
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := Drop.cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    rw [send_stackAt_callee_eq_allocHook s.sp]
    wp_steps
    wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
    dsimp only [wp_norm, arm64_norm]
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_poly_decoder_body_6928 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6940#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      s.readReg64 .x23 = x23 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6928#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧
          sm.readReg64 .x23 = x23) := by
  simp only [rustDeallocSpec] at hdealloc
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6940 24
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 6928#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧
        sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · wp_steps
      wp_call hdealloc (vptr, cap.toNat, 1)
      wp_steps
      rw [hsp]
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

attribute [local simp, local arm64_norm, local wp_norm] CryptoVerification.SpqrV1.Top.Send.ofNat_add_one_sub_one

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_poly_decoder_loop_6928 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (sp ptsPtr ptsCap x23 : BitVec 64)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6940#64 →
      s.status = .Running → s.sp = sp → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      s.readReg64 .x23 = x23 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 7544#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame) ∧
          sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x23 = x23) := by
  have hbody := CryptoVerification.Cli.SpqrV1.Top.Send.step_send_poly_decoder_body_6928 (b := b) (ext := ext) hdealloc s0 sp ptsPtr ptsCap x23 hsp_align
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6928 12
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := entry + 6928#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt sp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = sp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64 ∧
        sm.readReg64 .x23 = x23)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp htrace hvregs hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, htr1, hvregs1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_succ_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [show (bs :: bs2 :: tl2).length = (bs2 :: tl2).length + 1 from rfl] at hx21_1
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 24#64) _ (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl rfl (by assumption)
          hsp1 htr1 hvregs1 hx19_1 hx20_1
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, add_24_add_8]) hx23_1) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul bs (bs2 :: tl2) 24
      have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
      exact Entails.refl _

end CryptoVerification.SpqrV1.Top.Send
