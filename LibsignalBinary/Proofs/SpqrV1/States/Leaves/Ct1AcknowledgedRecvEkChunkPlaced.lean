/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSym
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSymPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (Block `349`)

Relocatable `[LibsignalPlacement]` verification of `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`,
153 instructions), proving the `.ok (.done ...)` branch, the cross-block callee-parameterized
contract `ct1_acknowledged_recv_ek_chunk_placed_cl_ext`, and `ct1_acknowledged_recv_ek_chunk_placed_ok_x`
discharging `<unchunked::Ct1Sent>::recv_ek` (Block `338`) and `send_ct2_encoder` (Block `382`).
-/

@[expose] public section

set_option autoImplicit false

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
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt unchunkedCt1SentEkReceivedSendCt2PlacedSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff addChunkTotal
attribute [-arm64_norm] Expand.sp_sub_496_eq_esp Expand.sp_add_neg496_eq_esp
  Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
  ct1AckEk_trace_writeVReg128

/-! ## 1. Done Branch (`+0x098..+0x184`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `.ok (.done ...)` branch of `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`). -/
theorem ct1_ack_recv_ek_done_branch_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hsendCt2_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (hsendCt2Enc_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)))
    (hdealloc_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "memcpy") sessionMemcpyRegionSpec)
    (hsortedSet16_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
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
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (blkPl_349).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 632 ∗
        unchunkedCt1SentRecvEkResAt A (F := F) (s0.sp - 592#64) (.ok uc1) ∗
        memRegion (s0.sp - 464#64) 400 ∗ ct1AckSavedRegs s0 ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2PlacedRoAt ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  have hepilogue := ct1_ack_recv_ek_epilogue_244_placed (F := F) hsortedSet16_raw
    outA stA chunkA chunk receivingEk res s0
  simp only [rustDeallocSpec] at hdealloc_raw
  apply of_sepWP_lscl hcl (mid := lsmpl.base 347)
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
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1176_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVec s0.sp g_uc1 uc1.epoch).symm)
    (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_done_uc1_copy_recompose s0.sp uc1 g_uc1 _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_sendCt2_cl hsendCt2_raw
    (s0.sp - 592#64) (s0.sp - 1176#64) uc1 outUc ct2 mac hsc_ok
    (ret_pc := (blkPl_349).base + 256#64) (next_pc := lsmpl.base 382) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx23, hx24, hx25, hx26, hx27, hsp, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
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
  refine call_sendCt2Encoder_cl hsendCt2Enc_raw
    (s0.sp - 1048#64) ct2Ptr macPtr ct2 mac sendingCt2
    hct2_ne hmac_ne henc_ok (ret_pc := (blkPl_349).base + 324#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hcl2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 264)
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
  refine Drop.seq_clean (mid := (blkPl_349).base + 344#64)
    (P_mid := (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
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
    refine Drop.seq_clean (mid := (blkPl_349).base + 364#64)
      (P_mid := (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
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
        (ret_pc := (blkPl_349).base + 388#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
        rfl (by simpa only [arm64_norm] using hrun4)
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
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun5) fun hcl_ep => ?_
      apply ct1AckEk_sepWP_congr_pre
      · refine hepilogue _ R hcl_ep hsp0_align (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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

/-! ## 2. Top-Level Theorems: `<Ct1Acknowledged>::recv_ek_chunk` (Block `349`, 153 insns) -/

set_option maxHeartbeats 800000 in
/-- `[LibsignalPlacement]` contract for `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk`
    (Block `349`, 153 instructions), taking `hadd` (Block `419`), `hdec` (Block `418`),
    `hrecv_ek` (Block `338`), `hsend_ct2` (Block `347`), `henc` (Block `382`) and discharging
    `drop_glue::<[SortedSet<Pt>; 16]>` (Block `264`) from `hdealloc`. -/
theorem ct1_acknowledged_recv_ek_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (hrecv_ek : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (henc : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX A F K ext := by
  unfold Ct1AcknowledgedRecvEkChunkPlacedOkX
  have hsortedSet16_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_of_block (i := 349) (j := 264)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok
          (spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc)))
  have hmemcpy_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy
  have hdealloc_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc
  dsimp only [lsProg_349] at hadd hdec hrecv_ek hsend_ct2 henc
  simp only [withLsCodeRoLoaded, ct1AcknowledgedRecvEkChunkPlacedSpec, lsProg_349]
  have hnone := ct1_ack_recv_ek_none_branch_placed (A := A) (F := F) hmemcpy_raw
  have herr := ct1_ack_recv_ek_err_branch_placed (F := F) hsortedSet16_raw
  have hdone := ct1_ack_recv_ek_done_branch_placed (F := F) (K := K)
    hsend_ct2 henc hdealloc_raw hmemcpy_raw hsortedSet16_raw
  wpp_init x s0
  rcases x with ⟨outA, stA, chunkA, st, chunk, res⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 (by assumption) (by decide)
  apply of_sepWP_lscro hcro0 (mid := lsmpl.base 419)
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
    (ret_pc := (blkPl_349).base + 96#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    rfl (by simpa only [arm64_norm] using ‹s0.status = .Running›)
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
  refine ct1AckEk_call_addChunk_cro hadd
    (s0.sp - 1624#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ek chunk (by assumption)
    (ret_pc := (blkPl_349).base + 108#64) (next_pc := lsmpl.base 418) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
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
  refine ct1AckEk_call_decodedMessage_cro hdec
    (s0.sp - 1224#64) (s0.sp - 1624#64) (addChunkTotal st.receiving_ek chunk) decoded?
    hsorted' hdm (ret_pc := (blkPl_349).base + 120#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hx23_2])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 hcro3 => ?_)
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
    apply of_sepWP_lscl hcro3.1 (mid := lsmpl.base 338)
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
    refine ct1AckEk_call_unchunkedRecvEk_cl hrecv_ek
      (s0.sp - 592#64) (s0.sp - 1760#64) (s0.sp - 1224#64) st.uc decoded ucRes huc
      (ret_pc := (blkPl_349).base + 152#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
      (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3)
      (by simp only [State.sp, arm64_norm, hsp3]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hsp3]) (by simp only [Reg.x1, arm64_norm, hsp3])
      (by simp only [Reg.x2, arm64_norm, hx21_3, ‹s0.readReg64 .x2 = st.uc.epoch›])
      (by simp only [Reg.x3, arm64_norm, hsp3])
      (by sep_focus)
      (fun sf4 hpc4 hrun4 hsp4 hcs4 htr4 hcl4 => ?_)
    rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩
    simp only [arm64_norm, hx19_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hvregs_4
    apply of_sepWP_lscl hcl4 (mid := (blkPl_349).base + 152#64)
    refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_unchunkedRecvEk (s0.sp - 1760#64)).symm)
      (by sep_focus) ?_
    refine SepWP.fold (ct1Ack_some_post_recvEk s0.sp) (by sep_focus) ?_
    apply SepWP.done hpc4 hrun4
    intro hcl4'
    cases ucRes with
    | error e =>
      apply SepWPp.of_sepWP_ret
      apply ct1AckEk_sepWP_congr_pre
      · exact herr (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
          chunk (addChunkTotal st.receiving_ek chunk) e res huc_cases s0 sf4 R hcl4'
          (by assumption) hpc4 hrun4 hsp4 htr4 hx19_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · ac_rfl
      · funext sf P_f
        simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
    | ok uc1 =>
      rcases huc_cases with ⟨outUc, ct2, mac, sendingCt2, hsc_ok, henc_ok, hres⟩
      apply ct1AckEk_sepWPp_congr_pre
      · exact hdone (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
          (s0.readReg64 (Reg.gpr 3#5)) chunk (addChunkTotal st.receiving_ek chunk)
          uc1 outUc ct2 mac sendingCt2 res hsc_ok henc_ok hres s0 sf4 R hcl4'
          (by assumption) hpc4 hrun4 hsp4 htr4 hx19_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hvregs_4
      · ac_rfl
      · funext sf P_f
        simp only [satisfies_pure_sepConj, sepConj_assoc, CalleeSavedPreserved,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp]
      · funext sf P_f; simp only [satisfies_pure_sepConj]

/-- Closed-callee `[LibsignalPlacement]` contract for
    `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (Block `349`),
    discharging `hrecv_ek` (Block `338`) via `unchunked_ct1_sent_recv_ek_placed_cl_ok_x` and
    `henc` (Block `382`) via `send_ct2_encoder_placed_ok_x`. -/
theorem ct1_acknowledged_recv_ek_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (mlkemValidatePkSpec K))
    (hadd : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (hdec : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (hsend_ct2 : subroutine_ok (lsProg_349 (Rust.withPanics ext))
      (lsmpl.base 347) (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K))) :
    Ct1AcknowledgedRecvEkChunkPlacedOkX A F K ext :=
  ct1_acknowledged_recv_ek_chunk_placed_cl_ext
    hdealloc hmemcpy hadd hdec
    (ls_subroutine_ok_of_block (i := 349) (j := 338)
      (unchunked_ct1_sent_recv_ek_placed_cl_ok_x hdealloc hval_pk))
    hsend_ct2
    (ls_subroutine_ok_of_block (i := 349) (j := 382)
      (send_ct2_encoder_placed_ok_x h_panic hshim halloc hrealloc hdealloc hmemcpy))

end CryptoVerification.SpqrV1.States.Leaves
