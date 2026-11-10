/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`)

**Checked by Lean.**

Verifies `ct1_acknowledged_recv_ek_chunk_ok_ext` (`0x5e9c8`, 153 instructions) against
`ct1AcknowledgedRecvEkChunkSpec A F K b`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff addChunkTotal
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

@[simp, local arm64_norm] theorem ct1AckEk_trace_writeVReg128 (s : State) (r : BitVec 5)
    (v : BitVec 128) : (s.writeVReg128 r v).trace = s.trace := rfl

@[local arm64_norm, local wp_norm]
private theorem hsp_add_8 (s₀ : State) :
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s₀ + 8#64 = s₀.sp - 680#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm]
private theorem hsp_592_add_8 (s₀ : State) :
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s₀ + 592#64) + 8#64 = s₀.sp - 88#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm]
private theorem esp_add_8 (s₀ : State) :
    CryptoVerification.LibsignalTripleRatchet.Expand.esp s₀ + 8#64 = s₀.sp - 488#64 := by
  unfold CryptoVerification.LibsignalTripleRatchet.Expand.esp; bv_omega

/-! ## 1. Done Branch (`+0x098..+0x184`) -/

theorem wordsAt_sp1176_fiveVec (sp : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt (sp - 1176#64) (fiveVecWordsList g ep) =
      ((sp - 1176#64) ↦₆₄ g.v1.w0) ∗ ((sp - 1168#64) ↦₆₄ g.v1.w1) ∗
      ((sp - 1160#64) ↦₆₄ g.v1.w2) ∗ ((sp - 1152#64) ↦₆₄ g.rest.v1.w0) ∗
      ((sp - 1144#64) ↦₆₄ g.rest.v1.w1) ∗ ((sp - 1136#64) ↦₆₄ g.rest.v1.w2) ∗
      ((sp - 1128#64) ↦₆₄ g.rest.rest.v1.w0) ∗ ((sp - 1120#64) ↦₆₄ g.rest.rest.v1.w1) ∗
      ((sp - 1112#64) ↦₆₄ g.rest.rest.v1.w2) ∗ ((sp - 1104#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
      ((sp - 1096#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗ ((sp - 1088#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
      ((sp - 1080#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗ ((sp - 1072#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
      ((sp - 1064#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗ ((sp - 1056#64) ↦₆₄ ep) := by
  rw [wordsAt_fiveVec]; simp only [arm64_norm]

theorem wordsAt_sp592_fiveVec (sp : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt (sp - 592#64) (fiveVecWordsList g ep) =
      ((sp - 592#64) ↦₆₄ g.v1.w0) ∗ ((sp - 584#64) ↦₆₄ g.v1.w1) ∗
      ((sp - 576#64) ↦₆₄ g.v1.w2) ∗ ((sp - 568#64) ↦₆₄ g.rest.v1.w0) ∗
      ((sp - 560#64) ↦₆₄ g.rest.v1.w1) ∗ ((sp - 552#64) ↦₆₄ g.rest.v1.w2) ∗
      ((sp - 544#64) ↦₆₄ g.rest.rest.v1.w0) ∗ ((sp - 536#64) ↦₆₄ g.rest.rest.v1.w1) ∗
      ((sp - 528#64) ↦₆₄ g.rest.rest.v1.w2) ∗ ((sp - 520#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
      ((sp - 512#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗ ((sp - 504#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
      ((sp - 496#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗ ((sp - 488#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
      ((sp - 480#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗ ((sp - 472#64) ↦₆₄ ep) := by
  rw [wordsAt_fiveVec]; simp only [arm64_norm]

/-- Callee-saved registers preserved across `__rust_dealloc` calls in `ct1_ack_recv_ek_done_branch`. -/
def Ct1AckDoneSaved (s0 s : State) (sp1760 outA ct2Cap ct2Ptr : BitVec 64) : Prop :=
  s.readReg64 .x19 = outA ∧ s.readReg64 .x20 = ct2Cap ∧ s.readReg64 .x21 = ct2Ptr ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.sp = sp1760 ∧ s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem ct1Ack_done_uc1_copy_recompose {A : RustAlloc} {F : ShaCompress}
    (sp : BitVec 64) (uc1 : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (g : FiveVecWords) (u0 u1 u2 : BitVec 64) :
    wordsAt (sp - 1176#64) (fiveVecWordsList g uc1.epoch) ∗
      wordsAt (sp - 592#64) (fiveVecWordsList g uc1.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst uc1)
        (wordsBytes (fiveVecWordsList g uc1.epoch)) ∗
      (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ⊢
    unchunkedCt1SentEkReceivedAt A (sp - 1176#64) uc1 ∗
      memRegion (sp - 1200#64) 24 ∗ memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 := by
  have h1 : wordsAt (sp - 1176#64) (fiveVecWordsList g uc1.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst uc1)
        (wordsBytes (fiveVecWordsList g uc1.epoch)) ⊢
      unchunkedCt1SentEkReceivedAt A (sp - 1176#64) uc1 :=
    recompose_wordsAt_relocatedHeap _ _ (sp - 1176#64)
  have h2 : (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ⊢
      memRegion (sp - 1200#64) 24 := by
    have heq : (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) =
        wordsAt (sp - 1200#64) [u0, u1, u2] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion _ (sp - 1200#64) 24 rfl
  have h3 : wordsAt (sp - 592#64) (fiveVecWordsList g uc1.epoch) ⊢
      memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 := by
    rw [← ProofLib.memRegion_split' (b := sp - 592#64) (n := 104) (k := 24) (b' := sp - 488#64) rfl (by bv_omega) (by decide)]
    exact wordsAt_entails_memRegion _ (sp - 592#64) 128 rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt (sp - 1176#64) (fiveVecWordsList g uc1.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst uc1)
        (wordsBytes (fiveVecWordsList g uc1.epoch))) ∗
    (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ∗
    wordsAt (sp - 592#64) (fiveVecWordsList g uc1.epoch) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 h3)

theorem ct1Ack_done_uc56_and_headers_recompose {A : RustAlloc} {F : ShaCompress}
    (sp : BitVec 64) (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (g : AuthWords) (c0 c1 c2 m0 m1 m2 : BitVec 64) :
    wordsAt (sp - 648#64) (ct2SentWordsList g outUc.epoch) ∗
      wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ∗
      ((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
      ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2) ⊢
    unchunkedCt2SentAt A (sp - 648#64) outUc ∗ memRegion (sp - 592#64) 104 := by
  have h1 : wordsAt (sp - 648#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
      unchunkedCt2SentAt A (sp - 648#64) outUc := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (sp - 648#64)
  have h2_sp : wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ⊢
      memRegion (sp - 592#64) 56 :=
    wordsAt_entails_memRegion (ct2SentWordsList g outUc.epoch) (sp - 592#64) 56 rfl
  have h2_hdr :
      ((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
      ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2) ⊢
      memRegion (sp - 536#64) 48 := by
    have heq :
        (((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
         ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2)) =
        wordsAt (sp - 536#64) [c0, c1, c2, m0, m1, m2] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [c0, c1, c2, m0, m1, m2] (sp - 536#64) 48 rfl
  have h2 :
      wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
       ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2)) ⊢
      memRegion (sp - 592#64) 104 := by
    refine Entails.trans (sepConj_mono h2_sp h2_hdr) ?_
    rw [← ProofLib.memRegion_split' (b := sp - 592#64) (n := 56) (k := 48) (b' := sp - 536#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt (sp - 648#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch))) ∗
    (wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
       ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2))) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem ct1Ack_done_scratch_join (sp : BitVec 64) :
    memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 24 ∗ memRegion (sp - 1176#64) 128 ∗
      memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 ∗ memRegion (sp - 464#64) 400 ⊢
    memRegion (sp - 1224#64) 176 ∗ memRegion (sp - 592#64) 528 := by
  have h1 : memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 24 ∗ memRegion (sp - 1176#64) 128 =
      memRegion (sp - 1224#64) 176 := by
    rw [← ProofLib.memRegion_split' (b := sp - 1200#64) (n := 24) (k := 128) (b' := sp - 1176#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 152) (b' := sp - 1200#64) rfl (by bv_omega) (by decide)]
  have h2 : memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 ∗ memRegion (sp - 464#64) 400 =
      memRegion (sp - 592#64) 528 := by
    rw [← ProofLib.memRegion_split' (b := sp - 488#64) (n := 24) (k := 400) (b' := sp - 464#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 592#64) (n := 104) (k := 424) (b' := sp - 488#64) rfl (by bv_omega) (by decide)]
  rw [← h1, ← h2]; exact Entails.of_eq (by ac_rfl)

theorem ct1Ack_done_stack_1160_rejoin (sp : BitVec 64) :
    memRegion (sp - 1224#64) 176 ∗ memRegion (sp - 1048#64) 456 ∗ memRegion (sp - 592#64) 528 ⊢
    memRegion (sp - 1224#64) 1160 := by
  rw [← ProofLib.memRegion_split' (b := sp - 1048#64) (n := 456) (k := 528) (b' := sp - 592#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 1224#64) (n := 176) (k := 984) (b' := sp - 1048#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem ct1Ack_done_outA_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (sendingCt2 : PolyEncoder)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .ok (.done { uc := outUc, sending_ct2 := sendingCt2 })) :
    (outA ↦₆₄ 0xffffffffffffffff#64) ∗
      chunkedCt2SampledAt A (outA + 8#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
      memRegion (outA + 464#64) 64 ⊢
    ct1AcknowledgedRecvEkChunkResAt A outA res := by
  subst hres; exact Entails.refl _

set_option maxHeartbeats 1600000 in
theorem ct1_ack_recv_ek_done_branch {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hsendCt2_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709550136#64)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 20832#64)
      (sendCt2EncoderSpec A))
    (hdealloc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A))
    (hmemcpy_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy")))
      sessionMemcpyRegionSpec)
    (hsortedSet16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
      (dropGlueSortedSetPt16Spec A))
    (outA stA chunkA : BitVec 64)
    (chunk : Chunk) (receivingEk : PolyDecoder)
    (uc1 : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (sendingCt2 : PolyEncoder)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hsc_ok : uc1.send_ct2 K = .ok (outUc, ct2, mac))
    (henc_ok : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok sendingCt2)
    (hres : res = .ok (.done { uc := outUc, sending_ct2 := sendingCt2 }))
    (s0 s : State) (R : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 632 ∗
        unchunkedCt1SentRecvEkResAt A (F := F) (s0.sp - 592#64) (.ok uc1) ∗
        memRegion (s0.sp - 464#64) 400 ∗ ct1AckSavedRegs s0 ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt b ∗
            tokenInitAt b ∗ reduceTableAt b ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  have hepilogue := ct1_ack_recv_ek_epilogue_244 (F := F) hsortedSet16_raw
    outA stA chunkA chunk receivingEk res s0
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches libsignalSessionCode spqrCt1AcknowledgedRecvEkChunkBin b
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 366032 612
  dsimp only [leavesProgAtExt, ct1AcknowledgedRecvEkChunkName, BitVec.ofNat_eq_ofNat] at hsendCt2_raw hsendCt2Enc_raw hdealloc_raw hmemcpy_raw hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 18446744073709550136#64)
  wp_conv_pre =>
    dsimp only [unchunkedCt1SentRecvEkResAt]
    rw [ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 24) (k := 608) (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 24) (k := 584) (b' := s0.sp - 1176#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1176#64) (n := 128) (k := 456) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 400) (k := 56) (b' := s0.sp - 648#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (unchunkedCt1SentEkReceivedAt_extract_nonNone A (s0.sp - 592#64) uc1)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc1
  wp_focus_pure; intro hne_uc1
  refine SepWP.fold (cells_3_unfold (s0.sp - 1200#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 1176#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  wp_steps
  wp_conv_pre => unfold CryptoVerification.LibsignalTripleRatchet.Expand.esp
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1176_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc1_copy_recompose s0.sp uc1 g_uc1 _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_sendCt2 hsendCt2_raw hb
    (s0.sp - 592#64) (s0.sp - 1176#64) uc1 outUc ct2 mac hsc_ok
    (ret_pc := entry + 256#64) (next_pc := entry + 20832#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx24, hx25, hx26, hx27, hsp, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have h56_eq : (s0.sp - 592#64) + 56#64 = s0.sp - 536#64 := by bv_omega
  have h80_eq : (s0.sp - 592#64) + 80#64 = s0.sp - 512#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (unchunkedCt2SentAt_extract A (s0.sp - 592#64) outUc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_outUc
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 536#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 512#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  refine SepWP.fold (cells_7_unfold (s0.sp - 648#64)) (by sep_focus) ?_
  wp_pull_exists
  have hsp_outUc_words :
      wordsAt (s0.sp - 592#64) (ct2SentWordsList g_outUc outUc.epoch) =
      (((s0.sp - 592#64) ↦₆₄ g_outUc.v1.w0) ∗ ((s0.sp - 584#64) ↦₆₄ g_outUc.v1.w1) ∗
       ((s0.sp - 576#64) ↦₆₄ g_outUc.v1.w2) ∗ ((s0.sp - 568#64) ↦₆₄ g_outUc.v2.w0) ∗
       ((s0.sp - 560#64) ↦₆₄ g_outUc.v2.w1) ∗ ((s0.sp - 552#64) ↦₆₄ g_outUc.v2.w2) ∗
       ((s0.sp - 544#64) ↦₆₄ outUc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  have h648_outUc_words :
      wordsAt (s0.sp - 648#64) (ct2SentWordsList g_outUc outUc.epoch) =
      (((s0.sp - 648#64) ↦₆₄ g_outUc.v1.w0) ∗ ((s0.sp - 640#64) ↦₆₄ g_outUc.v1.w1) ∗
       ((s0.sp - 632#64) ↦₆₄ g_outUc.v1.w2) ∗ ((s0.sp - 624#64) ↦₆₄ g_outUc.v2.w0) ∗
       ((s0.sp - 616#64) ↦₆₄ g_outUc.v2.w1) ∗ ((s0.sp - 608#64) ↦₆₄ g_outUc.v2.w2) ∗
       ((s0.sp - 600#64) ↦₆₄ outUc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  wp_conv_pre => rw [hsp_outUc_words]; simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_outUc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq h648_outUc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc56_and_headers_recompose s0.sp outUc g_outUc _ _ _ _ _ _)
    (by sep_focus) ?_
  refine call_sendCt2Encoder hsendCt2Enc_raw
    (s0.sp - 1048#64) ct2Ptr macPtr ct2 mac sendingCt2
    hct2_ne hmac_ne henc_ok (ret_pc := entry + 324#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  have hstack_alloc :
      stackAt (s0.sp - 1760#64) sendCt2EncoderStack =
      memRegion (s0.sp - 19216#64) 13360 ∗ stackAt (s0.sp - 1760#64) allocHookStack := by
    have h19216_sub : (s0.sp - 1760#64) - 17456#64 = s0.sp - 19216#64 := by bv_omega
    rw [stackAt_sendCt2Encoder_eq_allocHook (s0.sp - 1760#64), h19216_sub]
  refine SepWP.fold (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsampled_join :
      polyEncoderAt A (s0.sp - 1048#64) sendingCt2 ∗
        unchunkedCt2SentAt A (s0.sp - 648#64) outUc ⊢
      chunkedCt2SampledAt A (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } := by
    dsimp only [chunkedCt2SampledAt]
    have h400 : (s0.sp - 1048#64) + 400#64 = s0.sp - 648#64 := by bv_omega
    rw [h400]; exact Entails.refl _
  refine SepWP.fold hsampled_join (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_scratch_join s0.sp) (by sep_focus) ?_
  refine Drop.seq_clean (mid := entry + 344#64)
    (P_mid := (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
      polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
      memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 176 ∗
      chunkedCt2SampledAt A (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
      memRegion (s0.sp - 592#64) 528 ∗
      vecCapPtrDealloc A ct2Cap ct2Ptr ∗
      memRegion (s0.sp - 19216#64) 13360 ∗ ct1AckSavedRegs s0) ∗
      A.pool ∗ stackAt (s0.sp - 1760#64) allocHookStack)
    (Q := fun sm => Ct1AckDoneSaved s0 sm (s0.sp - 1760#64) outA ct2Cap ct2Ptr)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hmac : (macCap == 0#64) = true <;>
      simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hsp2, htr2, hvregs_2]⟩
    · wp_steps; wp_apply
      refine Drop.align_pre (by rw [hsp2]; ac_rfl) ?_
      wp_done
  · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hsp3, htr3, hvregs_3⟩
    refine Drop.seq_clean (mid := entry + 364#64)
      (P_mid := (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 176 ∗
        chunkedCt2SampledAt A (s0.sp - 1048#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
        memRegion (s0.sp - 592#64) 528 ∗
        memRegion (s0.sp - 19216#64) 13360 ∗ ct1AckSavedRegs s0) ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) allocHookStack)
      (Q := fun sm => Ct1AckDoneSaved s0 sm (s0.sp - 1760#64) outA ct2Cap ct2Ptr)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
      by_cases hct2 : (ct2Cap == 0#64) = true <;>
        simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hsp3, htr3, hvregs_3]⟩
      · wp_steps; wp_apply
        refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_
        wp_done
    · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx24_4, hx25_4, hx26_4, hx27_4, hsp4, htr4, hvregs_4⟩
      refine SepWP.fold (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
      wp_conv_pre =>
        rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 520) (b' := outA + 8#64) rfl rfl (by decide),
            ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 64) (b' := outA + 464#64) rfl (by bv_omega) (by decide)]
      refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
      wp_pull_exists
      wp_steps
      refine call_memcpy_relocate_cs hmemcpy_raw
        (Relocatable.of_chunkedCt2SampledAt A { uc := outUc, sending_ct2 := sendingCt2 })
        (outA + 8#64) (s0.sp - 1048#64)
        (ret_pc := entry + 388#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
        (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun4)
        (by simp only [State.sp, arm64_norm, hsp4]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr4])
        (by simp only [Reg.x0, arm64_norm, hx19_4]) (by simp only [Reg.x1, arm64_norm, hsp4])
        (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
        (fun sf5 hpc5 hrun5 hsp5 hcs5 htr5 => ?_)
      rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp_5, hvregs_5⟩
      simp only [arm64_norm, hx19_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4] at hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hfp_5 hvregs_5
      wp_steps
      refine SepWP.fold (ct1Ack_done_outA_recompose A outA outUc sendingCt2 res hres)
        (by sep_focus) ?_
      refine SepWP.fold (ct1Ack_done_stack_1160_rejoin s0.sp) (by sep_focus) ?_
      apply ct1AckEk_sepWP_congr_pre
      · refine hepilogue _ R hsp0_align ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · simp only [arm64_norm]
        · simpa only [arm64_norm] using hrun5
        · simp only [State.sp, arm64_norm, hsp5]
        · simp only [Reg.lr, arm64_norm]
        · simp only [arm64_norm, htr5]
        · simp only [Reg.x0, arm64_norm, hsp5]
        · simp only [arm64_norm, hx24_5]
        · simp only [arm64_norm, hx25_5]
        · simp only [arm64_norm, hx26_5]
        · simp only [arm64_norm, hx27_5]
        · simp only [arm64_norm, hvregs_5]
      · ac_rfl
      · funext sf P_f; simp only [sepConj_assoc]

/-! ## 2. Top-Level Theorem: `ct1_acknowledged_recv_ek_chunk_ok_ext` (`0x5e9c8`) -/

theorem ct1AckEk_sepWPp_congr_pre {prog : Program} {pc : BitVec 64} {s : State} {P1 P2 : SepProp}
    {post1 post2 fail1 fail2 : State → SepProp → Prop}
    (h : SepWPp prog pc s P1 post1 fail1) (hP : P1 = P2) (hpost : post1 = post2)
    (hfail : fail1 = fail2) :
    SepWPp prog pc s P2 post2 fail2 := by
  subst hP hpost hfail; exact h

theorem ct1Ack_some_pre_recvEk (A : RustAlloc) {F : ShaCompress}
    (sp stA : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (decoded : Bytes) (g_uc : FiveVecWords) (v_dec : VecWords) :
    wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ∗
      wordsAt (sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ∗
      wordsAt (sp - 1224#64) (vecWordsList v_dec) ∗
      relocatedHeap (fun dst => vecU8 A dst decoded) (wordsBytes (vecWordsList v_dec)) ∗
      memRegion (sp - 1200#64) 1136 ⊢
    memRegion stA 528 ∗ unchunkedCt1SentAt A (sp - 1760#64) uc ∗
      vecU8 A (sp - 1224#64) decoded ∗ memRegion (sp - 1200#64) 608 ∗
      memRegion (sp - 592#64) 128 ∗ memRegion (sp - 464#64) 400 := by
  have h1 : wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ⊢
      memRegion stA 528 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ stA 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := stA) (n := 128) (k := 400) (b' := stA + 128#64) rfl rfl (by decide)]
    exact Entails.refl _
  have h2 : wordsAt (sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ⊢
      unchunkedCt1SentAt A (sp - 1760#64) uc :=
    recompose_wordsAt_relocatedHeap _ _ (sp - 1760#64)
  have h3 : wordsAt (sp - 1224#64) (vecWordsList v_dec) ∗
      relocatedHeap (fun dst => vecU8 A dst decoded) (wordsBytes (vecWordsList v_dec)) ⊢
      vecU8 A (sp - 1224#64) decoded :=
    recompose_wordsAt_relocatedHeap _ _ (sp - 1224#64)
  have h4 : memRegion (sp - 1200#64) 1136 =
      memRegion (sp - 1200#64) 608 ∗ memRegion (sp - 592#64) 128 ∗ memRegion (sp - 464#64) 400 := by
    rw [ProofLib.memRegion_split' (b := sp - 1200#64) (n := 608) (k := 528) (b' := sp - 592#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 592#64) (n := 128) (k := 400) (b' := sp - 464#64) rfl (by bv_omega) (by decide)]
  rw [h4]
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400) ∗
    (wordsAt (sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g_uc uc.epoch))) ∗
    (wordsAt (sp - 1224#64) (vecWordsList v_dec) ∗
      relocatedHeap (fun dst => vecU8 A dst decoded) (wordsBytes (vecWordsList v_dec))) ∗
    (memRegion (sp - 1200#64) 608 ∗ memRegion (sp - 592#64) 128 ∗ memRegion (sp - 464#64) 400) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))

theorem ct1Ack_some_post_recvEk (sp : BitVec 64) :
    memRegion (sp - 1760#64) 128 ∗ memRegion (sp - 1632#64) 8 ∗
      memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 608 ⊢
    memRegion (sp - 1760#64) 136 ∗ memRegion (sp - 1224#64) 632 := by
  have h1 : memRegion (sp - 1760#64) 128 ∗ memRegion (sp - 1632#64) 8 = memRegion (sp - 1760#64) 136 :=
    (ProofLib.memRegion_split' (b := sp - 1760#64) (n := 128) (k := 8) (b' := sp - 1632#64) rfl (by bv_omega) (by decide)).symm
  have h2 : memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 608 = memRegion (sp - 1224#64) 632 :=
    (ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 608) (b' := sp - 1200#64) rfl (by bv_omega) (by decide)).symm
  rw [← sepConj_assoc, h1, h2]
  exact Entails.refl _

set_option maxHeartbeats 4000000 in
theorem ct1_acknowledged_recv_ek_chunk_ok_ext {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (haddChunk : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr addChunkName) (addChunkSpec A))
    (hdecodedMsg : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hrecvEk : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (hsendCt2 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      (ct1AcknowledgedRecvEkChunkSpec A F K b) := by
  simp only [ct1AcknowledgedRecvEkChunkSpec]
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy")))
      sessionMemcpyRegionSpec := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy"))) (b := b) (X := Rust.withPanics ext)
      ct1AcknowledgedRecvEkChunk_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  have hadd_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 55896#64)
      (addChunkSpec A) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 55896) (b := b) (X := Rust.withPanics ext)
      ct1AcknowledgedRecvEkChunk_fnOff libsignalSessionCode_fnOff_0x67028 (by decide)).symm haddChunk
  have hdecodedMsg_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 53688#64)
      (polyDecoderDecodedMessageSpec A b) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 53688) (b := b) (X := Rust.withPanics ext)
      ct1AcknowledgedRecvEkChunk_fnOff polyDecoderDecodedMessage_fnOff (by decide)).symm hdecodedMsg
  have hrecvEk_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709547768#64)
      (unchunkedCt1SentRecvEkSpec A F K) := by
    have hrel : (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName =
        (leavesProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName + BitVec.ofNat 64 3848 :=
      Program.fnAddr_rel (k := 3848) (b := b) (X := Rust.withPanics ext)
        unchunkedCt1SentRecvEk_fnOff ct1AcknowledgedRecvEkChunk_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ hrecvEk
    rw [hrel, BitVec.add_assoc]; simp
  have hsendCt2_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709550136#64)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b) := by
    have hrel : (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName =
        (leavesProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + BitVec.ofNat 64 1480 :=
      Program.fnAddr_rel (k := 1480) (b := b) (X := Rust.withPanics ext)
        unchunkedCt1SentEkReceivedSendCt2_fnOff ct1AcknowledgedRecvEkChunk_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ hsendCt2
    rw [hrel, BitVec.add_assoc]; simp
  have hsendCt2Enc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 20832#64)
      (sendCt2EncoderSpec A) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 20832) (b := b) (X := Rust.withPanics ext)
      ct1AcknowledgedRecvEkChunk_fnOff sendCt2Encoder_fnOff (by decide)).symm hsendCt2Enc
  have hdealloc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      ct1AcknowledgedRecvEkChunk_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hsortedSet16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName =
        (leavesProgAtExt b ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 76976 :=
      Program.fnAddr_rel (k := 76976) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x46920 ct1AcknowledgedRecvEkChunk_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  have hnone := ct1_ack_recv_ek_none_branch (A := A) (F := F) hmemcpy_raw
  have herr := ct1_ack_recv_ek_err_branch (F := F) hsortedSet16_raw
  have hdone := fun (hb : b &&& 0xfff#64 = 0#64) =>
    ct1_ack_recv_ek_done_branch (F := F) (K := K) hb
      hsendCt2_raw hsendCt2Enc_raw hdealloc_raw hmemcpy_raw hsortedSet16_raw
  code_fetches_range libsignalSessionCode spqrCt1AcknowledgedRecvEkChunkBin b
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 366032 0 152
  dsimp only [leavesProgAtExt, ct1AcknowledgedRecvEkChunkName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hadd_raw hdecodedMsg_raw hrecvEk_raw hnone herr hdone ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨outA, stA, chunkA, st, chunk, res⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 (by assumption) (by decide)
  apply SepWPp.of_sepWP (mid := entry + 55896#64)
  wp_conv_pre =>
    rw [stackAt_1760_entry_split s0.sp]
    unfold chunkedCt1AcknowledgedAt
  refine SepWP.fold (polyDecoderAt_dup_pts_len A (s0.readReg64 (Reg.gpr 1#5) + 128#64) st.receiving_ek)
    (by sep_focus) ?_
  wp_focus_pure; intro h16
  obtain ⟨decoded?, hdm, hcases⟩ := ct1_acknowledged_recv_ek_chunk_elim h16 (by assumption)
  refine SepWP.fold (unchunkedCt1SentAt_extract A (s0.readReg64 (Reg.gpr 1#5)) st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (cells_16_unfold (s0.sp - 1760#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_fiveVec (s0.readReg64 (Reg.gpr 1#5)) g_uc st.uc.epoch]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_fiveVec (s0.readReg64 (Reg.gpr 1#5)) g_uc st.uc.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1760_fiveVec s0.sp g_uc st.uc.epoch).symm)
    (by sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy_raw
    (Relocatable.of_polyDecoderAt A st.receiving_ek)
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 1#5) + 128#64)
    (ret_pc := entry + 96#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_addChunk (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_addChunk_mid hadd_raw
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ek chunk (by assumption)
    (ret_pc := entry + 108#64) (next_pc := entry + 53688#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx23_1]) (by simp only [Reg.x1, arm64_norm, hx22_1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hsorted' => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_addChunk (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)))
    (by sep_focus) ?_
  wp_steps
  refine ct1AckEk_call_decodedMessage hdecodedMsg_raw (by assumption)
    (s0.sp - 1224#64) (s0.sp - 1624#64) (addChunkTotal st.receiving_ek chunk) decoded?
    hsorted' hdm (ret_pc := entry + 120#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hx23_2])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  cases decoded? with
  | none =>
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    apply ct1AckEk_sepWP_congr_pre
    · exact hnone (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
        st.uc chunk (addChunkTotal st.receiving_ek chunk) g_uc res hcases s0 sf3 R
        (by assumption) hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hvregs_3
    · ac_rfl
    · funext sf P_f
      simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
  | some decoded =>
    rcases hcases with ⟨ucRes, huc, huc_cases⟩
    apply SepWPp.of_sepWP (mid := entry + 152#64)
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_decodedMessage (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    wp_conv_pre => dsimp only [optVecU8At]
    refine SepWP.fold (vecU8_extract_nonNone A (s0.sp - 1224#64) decoded) (by sep_focus) ?_
    wp_pull_exists; rename_i v_dec
    wp_focus_pure; intro hne_dec
    have hdec_words :
        wordsAt (s0.sp - 1224#64) (vecWordsList v_dec) =
        (((s0.sp - 1224#64) ↦₆₄ v_dec.w0) ∗ ((s0.sp - 1216#64) ↦₆₄ v_dec.w1) ∗
         ((s0.sp - 1208#64) ↦₆₄ v_dec.w2)) := by
      simp only [vecWordsList, wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    wp_conv_pre => rw [hdec_words]; simp only [arm64_norm]
    wp_steps
    refine SepWP.fold (Entails.of_eq hdec_words.symm) (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_pre_recvEk A s0.sp (s0.readReg64 (Reg.gpr 1#5)) st.uc decoded g_uc v_dec)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)))
      (by sep_focus) ?_
    refine call_unchunkedRecvEk hrecvEk_raw
      (s0.sp - 592#64) (s0.sp - 1760#64) (s0.sp - 1224#64) st.uc decoded ucRes huc
      (ret_pc := entry + 152#64) (target_pc := entry + 152#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp3]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hsp3]) (by simp only [Reg.x1, arm64_norm, hsp3])
      (by simp only [Reg.x2, arm64_norm, hx21_3, ‹s0.readReg64 .x2 = st.uc.epoch›])
      (by simp only [Reg.x3, arm64_norm, hsp3])
      (by sep_focus)
      (fun sf4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩
    simp only [arm64_norm, hx19_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hvregs_4
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_post_recvEk s0.sp) (by sep_focus) ?_
    apply SepWP.done hpc4 hrun4
    cases ucRes with
    | error e =>
      apply SepWPp.of_sepWP_ret
      apply ct1AckEk_sepWP_congr_pre
      · exact herr (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
          chunk (addChunkTotal st.receiving_ek chunk) e res huc_cases s0 sf4 R
          (by assumption) hpc4 hrun4 hsp4 htr4 hx19_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · ac_rfl
      · funext sf P_f
        simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
    | ok uc1 =>
      rcases huc_cases with ⟨outUc, ct2, mac, sendingCt2, hsc_ok, henc_ok, hres⟩
      apply ct1AckEk_sepWPp_congr_pre
      · exact hdone (by assumption) (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
          (s0.readReg64 (Reg.gpr 3#5)) chunk (addChunkTotal st.receiving_ek chunk)
          uc1 outUc ct2 mac sendingCt2 res hsc_ok henc_ok hres s0 sf4 R
          (by assumption) hpc4 hrun4 hsp4 htr4 hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · ac_rfl
      · funext sf P_f
        simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
      · funext sf P_f; simp only [satisfies_pure_sepConj]

end CryptoVerification.SpqrV1.States.Leaves
