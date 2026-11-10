/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack` (`0x58c20`)

Verifies `<EkReceivedCt1Sampled>::recv_ct1_ack` (`0x58c20`, 53 instructions) against
`ekReceivedCt1SampledRecvCt1AckSpec A F K b`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree spqrRecvCt2ChunkBin [
  0x58d04 → 0x58dd4
]

/-! ## Proof of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`0x58c20`, 53 insns) -/

theorem unchunkedCt1SentEkReceivedAt_400_eq (A : RustAlloc) {F : ShaCompress}
    (stA : BitVec 64) (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A (stA + 400#64) st =
      (authenticatorAt A (stA + 400#64) st.auth ∗
       vecU8 A (stA + 448#64) st.es ∗
       vecU8 A (stA + 472#64) st.ek ∗
       vecU8 A (stA + 496#64) st.ct1) ∗
      ((stA + 520#64) ↦₆₄ st.epoch) := by
  unfold unchunkedCt1SentEkReceivedAt
  simp only [BitVec.add_assoc, arm64_norm]

theorem stackAt_176_split (sp : BitVec 64) :
    stackAt sp ekReceivedCt1SampledRecvCt1AckStack =
      memRegion (sp - 17632#64) 736 ∗
      stackAt (sp - 176#64) unchunkedSendCt2Stack ∗
      memRegion (sp - 176#64) 8 ∗
      memRegion (sp - 168#64) 104 ∗
      memRegion (sp - 64#64) 64 := by
  change memRegion (sp - 17632#64) 17632 =
    memRegion (sp - 17632#64) 736 ∗ memRegion (sp - 176#64 - 16720#64) 16720 ∗ _
  have hsub : sp - 176#64 - 16720#64 = sp - 16896#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17632#64) (n := 736) (k := 16896) (b' := sp - 16896#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 16896#64) (n := 16720) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 168) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 104) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide)]

theorem stackAt_176_to_sendCt2Encoder (sp : BitVec 64) :
    memRegion (sp - 17632#64) 736 ∗ stackAt (sp - 176#64) unchunkedSendCt2Stack ⊢
    stackAt (sp - 176#64) sendCt2EncoderStack := by
  change memRegion (sp - 17632#64) 736 ∗ memRegion (sp - 176#64 - 16720#64) 16720 ⊢
    memRegion (sp - 176#64 - 17456#64) 17456
  have h1 : sp - 176#64 - 16720#64 = sp - 16896#64 := by bv_omega
  have h2 : sp - 176#64 - 17456#64 = sp - 17632#64 := by bv_omega
  rw [h1, h2, ← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 736) (k := 16720) (b' := sp - 16896#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_176_to_allocHook (sp : BitVec 64) :
    stackAt (sp - 176#64) sendCt2EncoderStack ⊢
    memRegion (sp - 17632#64) 13360 ∗ stackAt (sp - 176#64) allocHookStack := by
  change memRegion (sp - 176#64 - 17456#64) 17456 ⊢
    memRegion (sp - 17632#64) 13360 ∗ memRegion (sp - 176#64 - 4096#64) 4096
  have h1 : sp - 176#64 - 17456#64 = sp - 17632#64 := by bv_omega
  have h2 : sp - 176#64 - 4096#64 = sp - 4272#64 := by bv_omega
  rw [h1, h2, ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13360) (k := 4096) (b' := sp - 4272#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem uc_56_and_headers_recompose {A : RustAlloc} {F : ShaCompress}
    (outA sp : BitVec 64) (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (g : AuthWords) (w0 c0 c1 c2 m0 m1 m2 : BitVec 64) :
    wordsAt (outA + 400#64) (ct2SentWordsList g outUc.epoch) ∗
      wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ∗
      ((sp - 176#64) ↦₆₄ w0) ∗
      ((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
      ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2) ⊢
    unchunkedCt2SentAt A (outA + 400#64) outUc ∗ memRegion (sp - 176#64) 112 := by
  have h1 : wordsAt (outA + 400#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
      unchunkedCt2SentAt A (outA + 400#64) outUc := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 400#64)
  have h2_sp : wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ⊢
      memRegion (sp - 168#64) 56 :=
    wordsAt_entails_memRegion (ct2SentWordsList g outUc.epoch) (sp - 168#64) 56 rfl
  have h2_hdr :
      ((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
      ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2) ⊢
      memRegion (sp - 112#64) 48 := by
    have heq :
        (((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
         ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2)) =
        wordsAt (sp - 112#64) [c0, c1, c2, m0, m1, m2] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [c0, c1, c2, m0, m1, m2] (sp - 112#64) 48 rfl
  have h2_w0 : ((sp - 176#64) ↦₆₄ w0) ⊢ memRegion (sp - 176#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp - 176#64) w0
  have h2 :
      ((sp - 176#64) ↦₆₄ w0) ∗
      wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
       ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2)) ⊢
      memRegion (sp - 176#64) 112 := by
    refine Entails.trans (sepConj_mono h2_w0 (sepConj_mono h2_sp h2_hdr)) ?_
    rw [← ProofLib.memRegion_split' (b := sp - 168#64) (n := 56) (k := 48) (b' := sp - 112#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 104) (b' := sp - 168#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt (outA + 400#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch))) ∗
    (((sp - 176#64) ↦₆₄ w0) ∗
      wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
       ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2))) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem stackAt_176_to_dropPoly16 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    memRegion (sp - 17632#64) 13360 ∗ stackAt (sp - 176#64) allocHookStack ∗ memRegion (sp - 176#64) 112 ∗
      (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
       ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
       ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ⊢
    memRegion (sp - 17632#64) 13504 ∗ stackAt sp dropGluePoly16Stack := by
  have h8 :
      (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
       ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
       ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ⊢
      memRegion (sp - 64#64) 64 := by
    have heq :
        (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
         ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
         ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) =
        wordsAt (sp - 64#64) [w0, w1, w2, w3, w4, w5, w6, w7] := by simp only [wordsAt_8, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5, w6, w7] (sp - 64#64) 64 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h8))) ?_
  change memRegion (sp - 17632#64) 13360 ∗
      (memRegion (sp - 176#64 - 4096#64) 4096 ∗ (memRegion (sp - 176#64) 112 ∗ memRegion (sp - 64#64) 64)) ⊢
    memRegion (sp - 17632#64) 13504 ∗ memRegion (sp - 4128#64) 4128
  have hsub : sp - 176#64 - 4096#64 = sp - 4272#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := sp - 176#64) (n := 112) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 4272#64) (n := 4096) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13360) (k := 4272) (b' := sp - 4272#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13504) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_176_from_dropPoly16 (sp : BitVec 64) :
    memRegion (sp - 17632#64) 13504 ∗ stackAt sp dropGluePoly16Stack ⊢
    stackAt sp ekReceivedCt1SampledRecvCt1AckStack := by
  change memRegion (sp - 17632#64) 13504 ∗ memRegion (sp - 4128#64) 4128 ⊢ memRegion (sp - 17632#64) 17632
  rw [← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13504) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Callee-saved registers preserved across `__rust_dealloc` calls in `recv_ct1_ack`. -/
def RecvCt1AckSaved (s0 s : State) (sp176 stA ct2Cap ct2Ptr : BitVec 64) : Prop :=
  s.readReg64 .x19 = stA ∧ s.readReg64 .x20 = ct2Cap ∧ s.readReg64 .x21 = ct2Ptr ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = sp176 ∧ s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

set_option maxHeartbeats 800000 in
theorem ek_received_ct1_sampled_recv_ct1_ack_ok_ext {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hsendCt2 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      (ekReceivedCt1SampledRecvCt1AckSpec A F K b) := by
  simp only [ekReceivedCt1SampledRecvCt1AckSpec]
  have hsendCt2_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName + 772#64)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 772) (b := b) (X := Rust.withPanics ext)
      ekReceivedCt1SampledRecvCt1Ack_fnOff unchunkedCt1SentEkReceivedSendCt2_fnOff (by decide)).symm hsendCt2
  have hsendCt2Enc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName + 23084#64)
      (sendCt2EncoderSpec A) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 23084) (b := b) (X := Rust.withPanics ext)
      ekReceivedCt1SampledRecvCt1Ack_fnOff sendCt2Encoder_fnOff (by decide)).symm hsendCt2Enc
  have hdealloc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      ekReceivedCt1SampledRecvCt1Ack_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hpoly16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName + 18446744073709477312#64)
      (dropGluePoly16Spec A) := by
    have hrel : (leavesProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName =
        (leavesProgAtExt b ext).fnAddr dropPoly16Name + BitVec.ofNat 64 74304 :=
      Program.fnAddr_rel (k := 74304) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x46ac4 ekReceivedCt1SampledRecvCt1Ack_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches libsignalSessionCode spqrRecvCt2ChunkBin b
    (Rust.withPanics ext) ekReceivedCt1SampledRecvCt1Ack_fnOff
    (num% (ls_off% "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack")) 212
  dsimp only [leavesProgAtExt, ekReceivedCt1SampledRecvCt1AckName,
    chunkedCt2SampledSize, chunkedEkReceivedCt1SampledSize,
    BitVec.ofNat_eq_ofNat] at hsendCt2_raw hsendCt2Enc_raw hdealloc_raw hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack" = entry
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA› ‹s0.readReg64 (Reg.gpr 1#5) = stA›
  obtain ⟨ct2, mac, hsc_ok, henc_ok⟩ := recv_ct1_ack_ok_elim (by assumption)
  have hfsp_align : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 176#64 (by assumption) (by decide)
  apply SepWPp.of_sepWP (mid := entry + 772#64)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 0#5)) (n := 400) (k := 56)
        (b' := s0.readReg64 (Reg.gpr 0#5) + 400#64) rfl rfl (by decide),
        stackAt_176_split s0.sp]
    unfold chunkedEkReceivedCt1SampledAt
    rw [unchunkedCt1SentEkReceivedAt_400_eq A (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 176#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq (unchunkedCt1SentEkReceivedAt_400_eq A
    (s0.readReg64 (Reg.gpr 1#5)) st.uc).symm) (by sep_focus) ?_
  refine call_sendCt2 hsendCt2_raw (by assumption)
    (s0.sp - 168#64) (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc outSt.uc ct2 mac hsc_ok
    (ret_pc := entry + 60#64) (next_pc := entry + 23084#64) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have h56_eq : (s0.sp - 168#64) + 56#64 = s0.sp - 112#64 := by bv_omega
  have h80_eq : (s0.sp - 168#64) + 80#64 = s0.sp - 88#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (stackAt_176_to_sendCt2Encoder s0.sp) (by sep_focus) ?_
  refine SepWP.fold (unchunkedCt2SentAt_extract A (s0.sp - 168#64) outSt.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 112#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 88#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  refine SepWP.fold (cells_7_unfold (s0.readReg64 (Reg.gpr 0#5) + 400#64)) (by sep_focus) ?_
  wp_pull_exists
  have hsp_uc_words :
      wordsAt (s0.sp - 168#64) (ct2SentWordsList g_uc outSt.uc.epoch) =
      (((s0.sp - 168#64) ↦₆₄ g_uc.v1.w0) ∗ ((s0.sp - 160#64) ↦₆₄ g_uc.v1.w1) ∗
       ((s0.sp - 152#64) ↦₆₄ g_uc.v1.w2) ∗ ((s0.sp - 144#64) ↦₆₄ g_uc.v2.w0) ∗
       ((s0.sp - 136#64) ↦₆₄ g_uc.v2.w1) ∗ ((s0.sp - 128#64) ↦₆₄ g_uc.v2.w2) ∗
       ((s0.sp - 120#64) ↦₆₄ outSt.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  have hout_uc_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ct2SentWordsList g_uc outSt.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g_uc.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g_uc.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g_uc.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g_uc.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g_uc.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g_uc.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ outSt.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_conv_pre => rw [hsp_uc_words]; simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_56_and_headers_recompose
    (s0.readReg64 (Reg.gpr 0#5)) s0.sp outSt.uc g_uc _ _ _ _ _ _ _) (by sep_focus) ?_
  refine call_sendCt2Encoder hsendCt2Enc_raw
    (s0.readReg64 (Reg.gpr 0#5)) ct2Ptr macPtr ct2 mac outSt.sending_ct2
    hct2_ne hmac_ne henc_ok (ret_pc := entry + 116#64) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1]) (by simp only [Reg.x0, arm64_norm, hx22_1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx22_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_176_to_allocHook s0.sp) (by sep_focus) ?_
  have hout_join :
      polyEncoderAt A (s0.readReg64 (Reg.gpr 0#5)) outSt.sending_ct2 ∗
        unchunkedCt2SentAt A (s0.readReg64 (Reg.gpr 0#5) + 400#64) outSt.uc ⊢
      chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt := Entails.refl _
  refine SepWP.fold hout_join (by sep_focus) ?_
  refine Drop.seq_clean (mid := entry + 136#64)
    (P_mid := (chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
      polyEncoderAt A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
      memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
      vecCapPtrDealloc A ct2Cap ct2Ptr ∗
      unchunkedSendCt2RoAt b ∗
      memRegion (s0.sp - 17632#64) 13360 ∗ memRegion (s0.sp - 176#64) 112 ∗
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
      A.pool ∗ stackAt (s0.sp - 176#64) allocHookStack)
    (Q := fun sm => RecvCt1AckSaved s0 sm (s0.sp - 176#64) (s0.readReg64 (Reg.gpr 1#5)) ct2Cap ct2Ptr)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hmac : (macCap == 0#64) = true <;>
      simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp2, htr2, hvregs_2]⟩
    · wp_steps; wp_apply
      refine Drop.align_pre (by rw [hsp2]; dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_
      wp_done
  · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3⟩
    refine Drop.seq_clean (mid := entry + 156#64)
      (P_mid := (chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
        polyEncoderAt A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
        unchunkedSendCt2RoAt b ∗
        memRegion (s0.sp - 17632#64) 13360 ∗ memRegion (s0.sp - 176#64) 112 ∗
        (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) allocHookStack)
      (Q := fun sm => RecvCt1AckSaved s0 sm (s0.sp - 176#64) (s0.readReg64 (Reg.gpr 1#5)) ct2Cap ct2Ptr)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
      by_cases hct2 : (ct2Cap == 0#64) = true <;>
        simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3]⟩
      · wp_steps; wp_apply
        refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_
        wp_done
    · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp4, htr4, hvregs_4⟩
      refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A
        (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1) (by sep_focus) ?_
      wp_pull_exists; rename_i tag vecs
      wp_focus_pure; intro hvecs_len
      wp_steps
      refine SepWP.fold (stackAt_176_to_dropPoly16 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
      wp_call hpoly16_raw ⟨s0.readReg64 (Reg.gpr 1#5) + 8#64, vecs⟩
      refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 128 528 rfl (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_176_from_dropPoly16 s0.sp) (by sep_focus) ?_
      wp_done

end CryptoVerification.SpqrV1.States.Leaves

