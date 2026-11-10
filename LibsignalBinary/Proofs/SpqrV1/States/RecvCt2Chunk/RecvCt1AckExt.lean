/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1Ack
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<EkReceivedCt1Sampled>::recv_ct1_ack`: `.inImage` Proof

Lifts `ek_received_ct1_sampled_recv_ct1_ack_ok_ext` (`0x5e0fc`) to `.inImage img` callees,
yielding `StatesRecvContractsAx.ekReceivedCt1SampledRecvCt1Ack_ok`.
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode libsignalSessionCode_tree)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack allocFailedIn rustDeallocSpec vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (ImgCallInv sub_ok_at_of_fnAddr tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Mac MlKem PolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt)
open CryptoVerification.SpqrV1.Drop
  (DeallocOkExt chunkedCt2SampledAt chunkedCt2SampledSize chunkedEkReceivedCt1SampledAt
   chunkedEkReceivedCt1SampledSize chunked_400_join dropGluePoly16Spec dropPoly16Name
   dropProgAtExt drop_glue_poly16_ok_ext polyEncoderAt_entails_tag_vecs_tail
   unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.States.Leaves
  (RecvCt1AckSaved authWordsList bv_sub_sub cells_1_unfold cells_7_unfold cells_8_unfold
   ct2SentWordsList ekReceivedCt1SampledRecvCt1AckName ekReceivedCt1SampledRecvCt1AckSpec
   ekReceivedCt1SampledRecvCt1AckStack ekReceivedCt1SampledRecvCt1Ack_fnOff
   recv_ct1_ack_ok_elim sendCt2EncoderName sendCt2EncoderSpec sendCt2EncoderStack
   slice_and_tail_entails_vecCapPtrDealloc stackAt_176_from_dropPoly16
   stackAt_176_split stackAt_176_to_allocHook stackAt_176_to_dropPoly16
   stackAt_176_to_sendCt2Encoder uc_56_and_headers_recompose unchunkedCt1SentEkReceivedAt_400_eq
   unchunkedCt1SentEkReceivedSendCt2Name unchunkedCt1SentEkReceivedSendCt2Spec
   unchunkedCt2SentAt_extract unchunkedSendCt2RoAt unchunkedSendCt2Stack vecU8Tail
   vecU8_entails_slice_and_tail wordsAt wordsAt_7)
open CryptoVerification.SpqrV1.States.Recv (growToCalleeExt sub_ok_inImage_growToCalleeExt_ax)

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.RecvCt1AckExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree spqrRecvCt1Ack4KBin [
  0x58d04 → 0x58dd4
]

/-- Opaque wrapper around `ImgCallInv img s` so `dsimp`/`simp` never unfold `FrozenLoaded`. -/
structure RecvCt1AckInv (img : Obj.Image) (s : State) : Prop where
  val : ImgCallInv img s

private theorem sepWPp_of_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : RecvCt1AckInv img s)
    (h : SepWP prog mid s P (fun sm Pm => RecvCt1AckInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.val.1 hinv.val.2
    (SepWP.mono h fun _ _ _ _ hcont hF hsym => hcont ⟨⟨hF, hsym⟩⟩)

/-- Framed `.inImage img` call rule for `unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base`. -/
theorem call_sendCt2_inImage {A : RustAlloc} {F : ShaCompress} {K : MlKem} {img : Obj.Image}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hb : img.base &&& 4095#64 = 0#64)
    (outA stA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = Except.ok (outUc, ct2, mac))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A stA st ∗
      unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm => RecvCt1AckInv img sm →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm => RecvCt1AckInv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨outA, stA, st, outUc, ct2, mac⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hsc⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    refine sepWPp_of_inv (mid := next_pc) ⟨hinv_sf⟩ ?_
    have hassoc :
        (unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        (unchunkedCt2SentAt A outA outUc ∗
          (vecU8 A (outA + 56#64) ct2 ∗
            (vecU8 A (outA + 80#64) mac ∗
              (memRegion stA 128 ∗
                (unchunkedSendCt2RoAt img.base ∗
                  (A.pool ∗ stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed `.inImage img` call rule for `sendCt2EncoderSpec A`. -/
theorem call_sendCt2Encoder_inImage {A : RustAlloc} {img : Obj.Image} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((sendCt2EncoderSpec A).inImage img))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = Except.ok enc)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr)
    (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      RecvCt1AckInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => RecvCt1AckInv img sm →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hinv
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage
    hcall hinv.val (x := ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [sendCt2EncoderSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [sendCt2EncoderSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗ (A.pool ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by sep_ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) ⟨hinv_sf⟩

set_option maxHeartbeats 800000 in
/-- `<EkReceivedCt1Sampled>::recv_ct1_ack` meets
    `(ekReceivedCt1SampledRecvCt1AckSpec A F K img.base).inImage img` from `DeallocOkExt`
    and `.inImage img` contracts for `unchunkedCt1SentEkReceivedSendCt2` and `sendCt2Encoder`. -/
theorem ek_received_ct1_sampled_recv_ct1_ack_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext)
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((ekReceivedCt1SampledRecvCt1AckSpec A F K img.base).inImage img) := by
  have hsendCt2_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName + 772#64)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img) :=
    sub_ok_at_of_fnAddr hsendCt2 ekReceivedCt1SampledRecvCt1AckName 772 (by fnoff_eq)
  have hsendCt2Enc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName + 23084#64)
      ((sendCt2EncoderSpec A).inImage img) :=
    sub_ok_at_of_fnAddr hsendCt2Enc ekReceivedCt1SampledRecvCt1AckName 23084 (by fnoff_eq)
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) := CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack" "__rustc::__rust_dealloc"))) (b := img.base) (X := Rust.withPanics ext)
      ekReceivedCt1SampledRecvCt1Ack_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hpoly16_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName +
        (0#64 - 74304#64))
      (dropGluePoly16Spec A) := by
    have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName =
        (tripleRatchetProgAtExt img.base ext).fnAddr dropPoly16Name + BitVec.ofNat 64 74304 :=
      Program.fnAddr_rel (k := 74304) (b := img.base) (X := Rust.withPanics ext)
        (by fnoff_eq) ekReceivedCt1SampledRecvCt1Ack_fnOff (by decide)
    refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, tripleRatchetProgAtExt] at hrel ⊢
    rw [hrel]; bv_omega
  have hpoly16_raw' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName +
        BitVec.ofNat 64 (2 ^ 64 - 74304))
      (dropGluePoly16Spec A) := by
    simpa only [show (0#64 - 74304#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 74304) by decide]
      using hpoly16_raw
  clear hpoly16_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches CryptoVerification.libsignalSessionCode spqrRecvCt1Ack4KBin img.base
    (Rust.withPanics ext) ekReceivedCt1SampledRecvCt1Ack_fnOff
    (num% (ls_off% "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack")) 212
  dsimp only [Spec.inImage, ekReceivedCt1SampledRecvCt1AckSpec]
  dsimp only [tripleRatchetProgAtExt, ekReceivedCt1SampledRecvCt1AckName,
    chunkedCt2SampledSize, chunkedEkReceivedCt1SampledSize,
    BitVec.ofNat_eq_ofNat] at hsendCt2_raw hsendCt2Enc_raw hdealloc_raw hpoly16_raw' ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack" = entry
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : RecvCt1AckInv img s0 := ⟨⟨by assumption, by assumption⟩⟩
  clear ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab›
  rcases x with ⟨outA, stA, st, outSt⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA› ‹s0.readReg64 (Reg.gpr 1#5) = stA›
  obtain ⟨ct2, mac, hsc_ok, henc_ok⟩ := recv_ct1_ack_ok_elim (by assumption)
  have hfsp_align : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 176#64 (by assumption) (by decide)
  refine sepWPp_of_inv (mid := entry + 772#64) hinv0 ?_
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
  refine call_sendCt2_inImage hsendCt2_raw (by assumption)
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
  have hhsp104 : s0.sp - 96#64 = (s0.sp - 104#64) + 8#64 := by bv_omega
  wp_conv_pre =>
    rw [hsp_uc_words]
    simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
    rw [← CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 s0, hhsp104]
  wp_steps
  wp_conv_pre => rw [← hhsp104]
  refine SepWP.fold (Entails.of_eq hsp_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_56_and_headers_recompose
    (s0.readReg64 (Reg.gpr 0#5)) s0.sp outSt.uc g_uc _ _ _ _ _ _ _) (by sep_focus) ?_
  refine call_sendCt2Encoder_inImage hsendCt2Enc_raw
    (s0.readReg64 (Reg.gpr 0#5)) ct2Ptr macPtr ct2 mac outSt.sending_ct2
    hct2_ne hmac_ne henc_ok (ret_pc := entry + 116#64) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1]) (by simp only [Reg.x0, arm64_norm, hx22_1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 _ => ?_)
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
  refine CryptoVerification.SpqrV1.Drop.seq_clean (mid := entry + 136#64)
    (P_mid := (chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
      polyEncoderAt A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
      memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
      vecCapPtrDealloc A ct2Cap ct2Ptr ∗
      unchunkedSendCt2RoAt img.base ∗
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
      refine CryptoVerification.SpqrV1.Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp2, htr2, hvregs_2]⟩
    · wp_steps; wp_apply
      refine CryptoVerification.SpqrV1.Drop.align_pre (by rw [hsp2]; dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_
      wp_done
  · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3⟩
    refine CryptoVerification.SpqrV1.Drop.seq_clean (mid := entry + 156#64)
      (P_mid := (chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
        polyEncoderAt A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
        unchunkedSendCt2RoAt img.base ∗
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
        refine CryptoVerification.SpqrV1.Drop.align_pre (by sep_ac_rfl) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3]⟩
      · wp_steps; wp_apply
        refine CryptoVerification.SpqrV1.Drop.align_pre (by rw [hsp3]; sep_ac_rfl) ?_
        wp_done
    · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp4, htr4, hvregs_4⟩
      refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A
        (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1) (by sep_focus) ?_
      wp_pull_exists; rename_i tag vecs
      wp_focus_pure; intro hvecs_len
      wp_steps
      refine SepWP.fold (stackAt_176_to_dropPoly16 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
      wp_call hpoly16_raw' ⟨s0.readReg64 (Reg.gpr 1#5) + 8#64, vecs⟩
      refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 128 528 rfl (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_176_from_dropPoly16 s0.sp) (by sep_focus) ?_
      wp_done

/-- `StatesRecvContractsAx.ekReceivedCt1SampledRecvCt1Ack_ok` (`35936` B `growToCalleeExt` + `.inImage img`). -/
theorem ek_received_ct1_sampled_recv_ct1_ack_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext)
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((growToCalleeExt ekReceivedCt1SampledRecvCt1AckStack
        (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax ekReceivedCt1SampledRecvCt1AckStack
    (fun _ _ _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (ek_received_ct1_sampled_recv_ct1_ack_ok_inImage hdealloc hsendCt2 hsendCt2Enc)

theorem _root_.CryptoVerification.SpqrV1.States.RecvCt2Chunk.ek_received_ct1_sampled_recv_ct1_ack_ok_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext)
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((ekReceivedCt1SampledRecvCt1AckSpec A F K img.base).inImage img) :=
  LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.RecvCt1AckExt.ek_received_ct1_sampled_recv_ct1_ack_ok_inImage
    hdealloc hsendCt2 hsendCt2Enc

theorem _root_.CryptoVerification.SpqrV1.States.RecvCt2Chunk.ek_received_ct1_sampled_recv_ct1_ack_ok_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext)
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((sendCt2EncoderSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((growToCalleeExt ekReceivedCt1SampledRecvCt1AckStack
        (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)).inImage img) :=
  LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.RecvCt1AckExt.ek_received_ct1_sampled_recv_ct1_ack_ok_ax
    hdealloc hsendCt2 hsendCt2Enc

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.RecvCt1AckExt
