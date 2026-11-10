/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7i
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) Part J

Final epilogue output assembly `v7_epilogueOutFull_entails_ct1Sampled` and the
complete `+7404 (.ok dec) -> s0.x30` return path `v7_dec_ok_7404_to_ret` for
`InnerState.ct1Sampled`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Reassembly of `polyEncoderAt A out enc` (`out + 0 .. out + 400`) -/

theorem v7_out_96_realign (out w88 : BitVec 64) :
    ((out + 96#64) ↦₈ w88.extractLsb' 0 8) ∗
      ((out + 97#64) ↦₃₂ w88.extractLsb' 8 32) ∗
      ((out + 101#64) ↦₁₆ w88.extractLsb' 40 16) ∗
      ((out + 103#64) ↦₈ w88.extractLsb' 56 8) =
    (out + 96#64) ↦₆₄ w88 := by
  have h := (v7_pointsTo64_split_1_4_2_1 (out + 96#64) w88).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h
  exact h

theorem v7_out_120_realign (out w112 w120 : BitVec 64) :
    ((out + 120#64) ↦₈ loByte w112) ∗
      ((out + 121#64) ↦₆₄ unshiftWord w112 (loByte w120)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w112 (loByte w120)) (w120 >>> 8))) =
    ((out + 120#64) ↦₆₄ w112) ∗ ((out + 128#64) ↦₆₄ w120) := by
  rw [v7_overlapWord7_unshift_lsr8 w112 w120]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w112 w120).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h

theorem v7_out_144_realign (out w136 w144 w152 : BitVec 64) :
    ((out + 144#64) ↦₈ ((loByte w136).zeroExtend 32).setWidth 8) ∗
      ((out + 145#64) ↦₆₄ (v7_midQ128 w136 w144 w152).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v7_midQ128 w136 w144 w152).extractLsb' 64 64)) ∗
      ((out + 160#64) ↦₆₄
        overlapWord7 ((v7_midQ128 w136 w144 w152).extractLsb' 64 64) (w152 >>> 8)) =
    ((out + 144#64) ↦₆₄ w136) ∗ ((out + 152#64) ↦₆₄ w144) ∗ ((out + 160#64) ↦₆₄ w152) := by
  rw [v7_zext32_setWidth8 (loByte w136)]
  have hlo : (v7_midQ128 w136 w144 w152).extractLsb' 0 64 = unshiftWord w136 (loByte w144) := by
    unfold v7_midQ128; bv_kernel
  have hhi : (v7_midQ128 w136 w144 w152).extractLsb' 64 64 = unshiftWord w144 (loByte w152) := by
    unfold v7_midQ128; bv_kernel
  rw [hlo, hhi, v7_overlapWord7_unshift_lsr8 w144 w152]
  have hdst := v7_byte_qword_lo7_word_eq_triple64 (out + 144#64) w136 w144 w152
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd153 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rw [hd145, hd153, hd160, hd152] at hdst
  exact hdst

theorem v7_out_8_to_392_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((out + 8#64) ↦₆₄ v7_wordAt bs 0) ∗
      ((out + 16#64) ↦₆₄ v7_wordAt bs 8) ∗
      ((out + 24#64) ↦₆₄ v7_wordAt bs 16) ∗
      ((out + 32#64) ↦₆₄ v7_wordAt bs 24) ∗
      ((out + 40#64) ↦₆₄ v7_wordAt bs 32) ∗
      ((out + 48#64) ↦₆₄ v7_wordAt bs 40) ∗
      ((out + 56#64) ↦₆₄ v7_wordAt bs 48) ∗
      ((out + 64#64) ↦₆₄ v7_wordAt bs 56) ∗
      ((out + 72#64) ↦₆₄ v7_wordAt bs 64) ∗
      ((out + 80#64) ↦₆₄ v7_wordAt bs 72) ∗
      ((out + 88#64) ↦₆₄ v7_wordAt bs 80) ∗
      (((out + 96#64) ↦₈ (v7_wordAt bs 88).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v7_wordAt bs 88).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v7_wordAt bs 88).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v7_wordAt bs 88).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v7_wordAt bs 96) ∗
      ((out + 112#64) ↦₆₄ v7_wordAt bs 104) ∗
      (((out + 120#64) ↦₈ loByte (v7_wordAt bs 112)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120)))
           (v7_wordAt bs 120 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v7_wordAt bs 128) ∗
      (((out + 144#64) ↦₈ ((loByte (v7_wordAt bs 136)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 64 64)
           (v7_wordAt bs 152 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v7_quadAt bs 160) ∗
      ((out + 184#64) ↦₁₂₈ v7_quadAt bs 176) ∗
      ((out + 200#64) ↦₁₂₈ v7_quadAt bs 192) ∗
      ((out + 216#64) ↦₁₂₈ v7_quadAt bs 208) ∗
      ((out + 232#64) ↦₁₂₈ v7_quadAt bs 224) ∗
      ((out + 248#64) ↦₁₂₈ v7_quadAt bs 240) ∗
      ((out + 264#64) ↦₁₂₈ v7_quadAt bs 256) ∗
      ((out + 280#64) ↦₁₂₈ v7_quadAt bs 272) ∗
      ((out + 296#64) ↦₁₂₈ v7_quadAt bs 288) ∗
      ((out + 312#64) ↦₁₂₈ v7_quadAt bs 304) ∗
      ((out + 328#64) ↦₁₂₈ v7_quadAt bs 320) ∗
      ((out + 344#64) ↦₁₂₈ v7_quadAt bs 336) ∗
      ((out + 360#64) ↦₁₂₈ v7_quadAt bs 352) ∗
      ((out + 376#64) ↦₁₂₈ v7_quadAt bs 368) =
    (out + 8#64) ↦ₛ bs := by
  rw [v7_out_96_realign out (v7_wordAt bs 88),
      v7_out_120_realign out (v7_wordAt bs 112) (v7_wordAt bs 120),
      v7_out_144_realign out (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152),
      v7_bs384_eq_encCells bs hbs out]
  unfold v7_encCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 2. Reassembly of `unchunkedCt1SentAt` (`out + 400..528`) & `polyDecoderAt` (`out + 528..928`) -/

theorem v7_unchunkedCt1SentAt_400_pack (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64) :
    ((out + 400#64) ↦₆₄ c1) ∗ ((out + 408#64) ↦₆₄ p1) ∗ ((out + 416#64) ↦₆₄ l1) ∗
      ((out + 424#64) ↦₆₄ c2) ∗ ((out + 432#64) ↦₆₄ p2) ∗ ((out + 440#64) ↦₆₄ l2) ∗
      ((out + 448#64) ↦₆₄ c3) ∗ ((out + 456#64) ↦₆₄ p3) ∗ ((out + 464#64) ↦₆₄ l3) ∗
      ((out + 472#64) ↦₆₄ c4) ∗ ((out + 480#64) ↦₆₄ p4) ∗ ((out + 488#64) ↦₆₄ l4) ∗
      ((out + 496#64) ↦₆₄ c5) ∗ ((out + 504#64) ↦₆₄ p5) ∗ ((out + 512#64) ↦₆₄ l5) ∗
      ((out + 520#64) ↦₆₄ uc.epoch) ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
    unchunkedCt1SentAt A (F := F) (out + 400#64) uc := by
  rw [← v7_ct1SentAt_eq_unchunkedCt1SentAt A (F := F) (out + 400#64) uc]
  have hpack := v7_ct1SentAt_pack A (out + 400#64) uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
  dsimp only [v7_ct1SentWordsAt] at hpack
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hpack

theorem v7_out_536_realign (out w8_dec w16_dec w24_dec : BitVec 64) :
    ((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
      ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))) =
    ((out + 536#64) ↦₆₄ w8_dec) ∗ ((out + 544#64) ↦₆₄ w16_dec) ∗ ((out + 552#64) ↦₆₄ w24_dec) := by
  rw [v7_zext32_setWidth8 (loByte w8_dec)]
  have hhi : (v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64 =
      unshiftWord w16_dec (loByte w24_dec) := by
    unfold v7_midQ128; bv_kernel
  rw [hhi, v7_overlapWord7_unshift_lsr8 w16_dec w24_dec]
  have h := (v7_triple64_eq_byte_q128_tail7 (out + 536#64) w8_dec w16_dec w24_dec).symm
  change _ = ((out + 536#64) ↦₆₄ w8_dec) ∗ (((out + 536#64) + 8#64) ↦₆₄ w16_dec) ∗
    (((out + 536#64) + 16#64) ↦₆₄ w24_dec) at h
  have ha537 : (out + 536#64) + 1#64 = out + 537#64 := by bv_omega
  have ha553 : (out + 536#64) + 17#64 = out + 553#64 := by bv_omega
  have ha544 : (out + 536#64) + 8#64 = out + 544#64 := by bv_omega
  have ha552 : (out + 536#64) + 16#64 = out + 552#64 := by bv_omega
  rw [ha537, ha553, ha544, ha552] at h
  exact h

theorem v7_polyDecoderAt_528_pack (A : RustAlloc)
    (out w0_dec w8_dec w16_dec w24_dec : BitVec 64)
    (bs328_dec : List (BitVec 8))
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (dec : PolyDecoder) (P_dec_heap : SepProp)
    (hreloc_dec :
      ((out + 528#64) ↦₆₄ w0_dec) ∗ (((out + 528#64) + 8#64) ↦₆₄ w8_dec) ∗
        (((out + 528#64) + 16#64) ↦₆₄ w16_dec) ∗ (((out + 528#64) + 24#64) ↦₆₄ w24_dec) ∗
        (((out + 528#64) + 32#64) ↦ₛ bs328_dec) ∗
        (((out + 528#64) + 360#64) ↦₁₂₈ q328_dec) ∗
        (((out + 528#64) + 376#64) ↦₁₂₈ q344_dec) ∗
        (((out + 528#64) + 392#64) ↦₆₄ w360_dec) ∗ P_dec_heap ⊢
        polyDecoderAt A (out + 528#64) dec) :
    ((out + 528#64) ↦₆₄ w0_dec) ∗
      (((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
       ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
       ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))) ∗
       ((out + 560#64) ↦ₛ bs328_dec) ∗
       ((out + 888#64) ↦₁₂₈ q328_dec) ∗
       ((out + 904#64) ↦₁₂₈ q344_dec) ∗
       ((out + 920#64) ↦₆₄ w360_dec)) ∗
      P_dec_heap ⊢
    polyDecoderAt A (out + 528#64) dec := by
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hreloc_dec
  refine Entails.trans (Entails.of_eq (show _ =
    ((out + 528#64) ↦₆₄ w0_dec) ∗
    (((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
     ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
       (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8)))) ∗
    ((out + 560#64) ↦ₛ bs328_dec) ∗
    ((out + 888#64) ↦₁₂₈ q328_dec) ∗
    ((out + 904#64) ↦₁₂₈ q344_dec) ∗
    ((out + 920#64) ↦₆₄ w360_dec) ∗
    P_dec_heap by ac_rfl)) ?_
  rw [v7_out_536_realign out w8_dec w16_dec w24_dec]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hreloc_dec

/-! ## 3. Epilogue Output Entailment (`v7_epilogueOutFull_entails_ct1Sampled`) -/

theorem v7_epilogueOutFull_entails_ct1Sampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (dec : PolyDecoder)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (bs_enc : List (BitVec 8)) (hbs_enc : bs_enc.length = 384)
    (hi32_enc : BitVec 32) (P_enc_heap : SepProp)
    (hreloc_enc :
      (out ↦₆₄ v7_polyEncoderTag enc) ∗ ((out + 8#64) ↦ₛ bs_enc) ∗
        ((out + 392#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗ P_enc_heap ⊢
        polyEncoderAt A out enc)
    (w0_dec w8_dec w16_dec w24_dec : BitVec 64)
    (bs328_dec : List (BitVec 8))
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64) (P_dec_heap : SepProp)
    (hreloc_dec :
      ((out + 528#64) ↦₆₄ w0_dec) ∗ (((out + 528#64) + 8#64) ↦₆₄ w8_dec) ∗
        (((out + 528#64) + 16#64) ↦₆₄ w16_dec) ∗ (((out + 528#64) + 24#64) ↦₆₄ w24_dec) ∗
        (((out + 528#64) + 32#64) ↦ₛ bs328_dec) ∗
        (((out + 528#64) + 360#64) ↦₁₂₈ q328_dec) ∗
        (((out + 528#64) + 376#64) ↦₁₂₈ q344_dec) ∗
        (((out + 528#64) + 392#64) ↦₆₄ w360_dec) ∗ P_dec_heap ⊢
        polyDecoderAt A (out + 528#64) dec) :
    epilogueOutFull out
      (v7_polyEncoderTag enc)
      (v7_wordAt bs_enc 0) (v7_wordAt bs_enc 8) (v7_wordAt bs_enc 16)
      (v7_wordAt bs_enc 24) (v7_wordAt bs_enc 32) (v7_wordAt bs_enc 40) (v7_wordAt bs_enc 48)
      (v7_wordAt bs_enc 56) (v7_wordAt bs_enc 64) (v7_wordAt bs_enc 72) (v7_wordAt bs_enc 80)
      ((v7_wordAt bs_enc 88).extractLsb' 0 8) ((v7_wordAt bs_enc 88).extractLsb' 8 32)
      ((v7_wordAt bs_enc 88).extractLsb' 40 16) ((v7_wordAt bs_enc 88).extractLsb' 56 8)
      (v7_wordAt bs_enc 96) (v7_wordAt bs_enc 104) (loByte (v7_wordAt bs_enc 112))
      (unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120)))
      (overlapWord7 (unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120)))
        (v7_wordAt bs_enc 120 >>> 8))
      (v7_wordAt bs_enc 128)
      (((loByte (v7_wordAt bs_enc 136)).zeroExtend 32).setWidth 8)
      (v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152))
      (overlapWord7
        ((v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 64 64)
        (v7_wordAt bs_enc 152 >>> 8))
      (v7_quadAt bs_enc 160) (v7_quadAt bs_enc 176) (v7_quadAt bs_enc 192) (v7_quadAt bs_enc 208)
      (v7_quadAt bs_enc 224) (v7_quadAt bs_enc 240) (v7_quadAt bs_enc 256) (v7_quadAt bs_enc 272)
      (v7_quadAt bs_enc 288) (v7_quadAt bs_enc 304) (v7_quadAt bs_enc 320) (v7_quadAt bs_enc 336)
      (v7_quadAt bs_enc 352) (v7_quadAt bs_enc 368)
      (hi32_enc ++ enc.idx) c1
      p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5
      l5 uc.epoch w0_dec
      (((loByte w8_dec).zeroExtend 32).setWidth 8)
      (v7_midQ128 w8_dec w16_dec w24_dec)
      (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))
      bs328_dec q328_dec q344_dec w360_dec ∗
      P_enc_heap ∗
      P_dec_heap ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.ct1Sampled ⟨uc, enc, dec⟩)) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedCt1SampledAt]
  unfold epilogueOutFull
  have hbs_eq := v7_out_8_to_392_eq_bs out bs_enc hbs_enc
  have huc := v7_unchunkedCt1SentAt_400_pack A (F := F) out uc
    c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
  have hdec := v7_polyDecoderAt_528_pack A out w0_dec w8_dec w16_dec w24_dec
    bs328_dec q328_dec q344_dec w360_dec dec P_dec_heap hreloc_dec
  refine Entails.trans (Entails.of_eq (show _ =
    ((out ↦₆₄ v7_polyEncoderTag enc) ∗
     (((out + 8#64) ↦₆₄ v7_wordAt bs_enc 0) ∗
      ((out + 16#64) ↦₆₄ v7_wordAt bs_enc 8) ∗
      ((out + 24#64) ↦₆₄ v7_wordAt bs_enc 16) ∗
      ((out + 32#64) ↦₆₄ v7_wordAt bs_enc 24) ∗
      ((out + 40#64) ↦₆₄ v7_wordAt bs_enc 32) ∗
      ((out + 48#64) ↦₆₄ v7_wordAt bs_enc 40) ∗
      ((out + 56#64) ↦₆₄ v7_wordAt bs_enc 48) ∗
      ((out + 64#64) ↦₆₄ v7_wordAt bs_enc 56) ∗
      ((out + 72#64) ↦₆₄ v7_wordAt bs_enc 64) ∗
      ((out + 80#64) ↦₆₄ v7_wordAt bs_enc 72) ∗
      ((out + 88#64) ↦₆₄ v7_wordAt bs_enc 80) ∗
      (((out + 96#64) ↦₈ (v7_wordAt bs_enc 88).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v7_wordAt bs_enc 88).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v7_wordAt bs_enc 88).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v7_wordAt bs_enc 88).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v7_wordAt bs_enc 96) ∗
      ((out + 112#64) ↦₆₄ v7_wordAt bs_enc 104) ∗
      (((out + 120#64) ↦₈ loByte (v7_wordAt bs_enc 112)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v7_wordAt bs_enc 112) (loByte (v7_wordAt bs_enc 120)))
           (v7_wordAt bs_enc 120 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v7_wordAt bs_enc 128) ∗
      (((out + 144#64) ↦₈ ((loByte (v7_wordAt bs_enc 136)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v7_midQ128 (v7_wordAt bs_enc 136) (v7_wordAt bs_enc 144) (v7_wordAt bs_enc 152)).extractLsb' 64 64)
           (v7_wordAt bs_enc 152 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v7_quadAt bs_enc 160) ∗
      ((out + 184#64) ↦₁₂₈ v7_quadAt bs_enc 176) ∗
      ((out + 200#64) ↦₁₂₈ v7_quadAt bs_enc 192) ∗
      ((out + 216#64) ↦₁₂₈ v7_quadAt bs_enc 208) ∗
      ((out + 232#64) ↦₁₂₈ v7_quadAt bs_enc 224) ∗
      ((out + 248#64) ↦₁₂₈ v7_quadAt bs_enc 240) ∗
      ((out + 264#64) ↦₁₂₈ v7_quadAt bs_enc 256) ∗
      ((out + 280#64) ↦₁₂₈ v7_quadAt bs_enc 272) ∗
      ((out + 296#64) ↦₁₂₈ v7_quadAt bs_enc 288) ∗
      ((out + 312#64) ↦₁₂₈ v7_quadAt bs_enc 304) ∗
      ((out + 328#64) ↦₁₂₈ v7_quadAt bs_enc 320) ∗
      ((out + 344#64) ↦₁₂₈ v7_quadAt bs_enc 336) ∗
      ((out + 360#64) ↦₁₂₈ v7_quadAt bs_enc 352) ∗
      ((out + 376#64) ↦₁₂₈ v7_quadAt bs_enc 368)) ∗
     ((out + 392#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗
     P_enc_heap) ∗
    (((out + 400#64) ↦₆₄ c1) ∗ ((out + 408#64) ↦₆₄ p1) ∗ ((out + 416#64) ↦₆₄ l1) ∗
     ((out + 424#64) ↦₆₄ c2) ∗ ((out + 432#64) ↦₆₄ p2) ∗ ((out + 440#64) ↦₆₄ l2) ∗
     ((out + 448#64) ↦₆₄ c3) ∗ ((out + 456#64) ↦₆₄ p3) ∗ ((out + 464#64) ↦₆₄ l3) ∗
     ((out + 472#64) ↦₆₄ c4) ∗ ((out + 480#64) ↦₆₄ p4) ∗ ((out + 488#64) ↦₆₄ l4) ∗
     ((out + 496#64) ↦₆₄ c5) ∗ ((out + 504#64) ↦₆₄ p5) ∗ ((out + 512#64) ↦₆₄ l5) ∗
     ((out + 520#64) ↦₆₄ uc.epoch) ∗
     v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5) ∗
    (((out + 528#64) ↦₆₄ w0_dec) ∗
     (((out + 536#64) ↦₈ ((loByte w8_dec).zeroExtend 32).setWidth 8) ∗
      ((out + 537#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))) ∗
      ((out + 560#64) ↦ₛ bs328_dec) ∗
      ((out + 888#64) ↦₁₂₈ q328_dec) ∗
      ((out + 904#64) ↦₁₂₈ q344_dec) ∗
      ((out + 920#64) ↦₆₄ w360_dec)) ∗
     P_dec_heap) by ac_rfl)) ?_
  rw [hbs_eq]
  exact Entails.trans (sepConj_mono hreloc_enc (sepConj_mono huc hdec)) (Entails.of_eq (by ac_rfl))

/-! ## 4. Stack Splitting & Gap Packing Helpers for `+7404 -> +8180` -/

theorem v7_memRegion_0_16_split (fsp : BitVec 64) :
    memRegion fsp 16 ⊢
      memRegion fsp 8 ∗ (∃∗ w8 : BitVec 64, (fsp + 8#64) ↦₆₄ w8) := by
  exact split_top <| split_step0 (Entails.refl _) <| mem64_entails _

theorem v7_memRegion_32_168_split (fsp : BitVec 64) :
    memRegion (fsp + 32#64) 168 ⊢
      (∃∗ w32 : BitVec 64, (fsp + 32#64) ↦₆₄ w32) ∗
      (∃∗ w40 : BitVec 64, (fsp + 40#64) ↦₆₄ w40) ∗
      (∃∗ w48 : BitVec 64, (fsp + 48#64) ↦₆₄ w48) ∗
      (∃∗ w56 : BitVec 64, (fsp + 56#64) ↦₆₄ w56) ∗
      (∃∗ w64 : BitVec 64, (fsp + 64#64) ↦₆₄ w64) ∗
      (∃∗ w72 : BitVec 64, (fsp + 72#64) ↦₆₄ w72) ∗
      (∃∗ w80 : BitVec 64, (fsp + 80#64) ↦₆₄ w80) ∗
      memRegion (fsp + 88#64) 4 ∗
      (∃∗ d92 : BitVec 32, (fsp + 92#64) ↦₃₂ d92) ∗
      (∃∗ w96 : BitVec 64, (fsp + 96#64) ↦₆₄ w96) ∗
      (∃∗ w104 : BitVec 64, (fsp + 104#64) ↦₆₄ w104) ∗
      (∃∗ w112 : BitVec 64, (fsp + 112#64) ↦₆₄ w112) ∗
      (∃∗ w120 : BitVec 64, (fsp + 120#64) ↦₆₄ w120) ∗
      (∃∗ w128 : BitVec 64, (fsp + 128#64) ↦₆₄ w128) ∗
      (∃∗ w136 : BitVec 64, (fsp + 136#64) ↦₆₄ w136) ∗
      (∃∗ w144 : BitVec 64, (fsp + 144#64) ↦₆₄ w144) ∗
      (∃∗ w152 : BitVec 64, (fsp + 152#64) ↦₆₄ w152) ∗
      (∃∗ w160 : BitVec 64, (fsp + 160#64) ↦₆₄ w160) ∗
      memRegion (fsp + 168#64) 4 ∗
      (∃∗ d172 : BitVec 32, (fsp + 172#64) ↦₃₂ d172) ∗
      (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
      (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
      (∃∗ w192 : BitVec 64, (fsp + 192#64) ↦₆₄ w192) := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem32_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    mem64_entails _

theorem v7_pointsTo64_entails_loBytes7_mem1 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (a + 7#64) 1 := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w]
  have hsplit : unpack64 w = EncoderFromPb.loBytes7 w ++ [w.extractLsb' 56 8] := rfl
  rw [hsplit, ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w) [w.extractLsb' 56 8],
      EncoderFromPb.length_loBytes7 w]
  exact sepConj_mono_right
    (ProofLib.pointsToBytes_entails_memRegion (a + 7#64) [w.extractLsb' 56 8])

theorem v7_memRegion8_entails_loBytes7_mem1 (a : BitVec 64) :
    memRegion a 8 ⊢ (∃∗ w : BitVec 64, a ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (a + 7#64) 1 := by
  refine Entails.trans (mem64_entails a) ?_
  apply Entails.sepExists_elim; intro w
  refine Entails.trans (v7_pointsTo64_entails_loBytes7_mem1 a w) ?_
  exact sepConj_mono_left (Entails.sepExists_right w (Entails.refl _))

theorem v7_memRegion8_loBytes7_at (fsp o1 o2 : BitVec 64)
    (ho : o1 + 7#64 = o2 := by rfl) :
    memRegion (fsp + o1) 8 ⊢
      (∃∗ w : BitVec 64, (fsp + o1) ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (fsp + o2) 1 := by
  have ha : (fsp + o1) + 7#64 = fsp + o2 := by rw [BitVec.add_assoc, ho]
  rw [← ha]
  exact v7_memRegion8_entails_loBytes7_mem1 (fsp + o1)

theorem v7_memRegion16_loBytes7_at (fsp o1 o2 : BitVec 64)
    (ho : o1 + 7#64 = o2 := by rfl) :
    memRegion (fsp + o1) 16 ⊢
      (∃∗ w : BitVec 64, (fsp + o1) ↦ₛ EncoderFromPb.loBytes7 w) ∗ memRegion (fsp + o2) 9 := by
  have hsplit : memRegion (fsp + o1) 16 ⊢
      memRegion (fsp + o1) 8 ∗ memRegion ((fsp + o1) + 8#64) 8 := by
    rw [ProofLib.memRegion_split (fsp + o1) 8 8 (by decide)]
    exact Entails.refl _
  refine Entails.trans hsplit ?_
  refine Entails.trans (sepConj_mono_left (v7_memRegion8_loBytes7_at fsp o1 o2 ho)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right ?_
  have ha : (fsp + o1) + 8#64 = (fsp + o2) + 1#64 := by
    rw [← ho, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  rw [ha, ← ProofLib.memRegion_split (fsp + o2) 1 8 (by decide)]
  exact Entails.refl _

theorem v7_memRegion_208_1056_split (fsp : BitVec 64) :
    memRegion (fsp + 208#64) 1056 ⊢
      (∃∗ w208 : BitVec 64, (fsp + 208#64) ↦₆₄ w208) ∗
      (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 328 ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, (fsp + 576#64) ↦₁₂₈ q576) ∗
      ((∃∗ w592 : BitVec 64, (fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, (fsp + 608#64) ↦₁₂₈ q608) ∗
      (∃∗ q624 : BitVec 128, (fsp + 624#64) ↦₁₂₈ q624) ∗
      (∃∗ q640 : BitVec 128, (fsp + 640#64) ↦₁₂₈ q640) ∗
      (∃∗ q656 : BitVec 128, (fsp + 656#64) ↦₁₂₈ q656) ∗
      (∃∗ q672 : BitVec 128, (fsp + 672#64) ↦₁₂₈ q672) ∗
      (∃∗ q688 : BitVec 128, (fsp + 688#64) ↦₁₂₈ q688) ∗
      (∃∗ q704 : BitVec 128, (fsp + 704#64) ↦₁₂₈ q704) ∗
      (∃∗ q720 : BitVec 128, (fsp + 720#64) ↦₁₂₈ q720) ∗
      (∃∗ q736 : BitVec 128, (fsp + 736#64) ↦₁₂₈ q736) ∗
      (∃∗ q752 : BitVec 128, (fsp + 752#64) ↦₁₂₈ q752) ∗
      (∃∗ q768 : BitVec 128, (fsp + 768#64) ↦₁₂₈ q768) ∗
      (∃∗ q784 : BitVec 128, (fsp + 784#64) ↦₁₂₈ q784) ∗
      (∃∗ q800 : BitVec 128, (fsp + 800#64) ↦₁₂₈ q800) ∗
      (∃∗ q816 : BitVec 128, (fsp + 816#64) ↦₁₂₈ q816) ∗
      (∃∗ w832 : BitVec 64, (fsp + 832#64) ↦₆₄ w832) ∗
      memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, (fsp + 848#64) ↦₁₂₈ q848) ∗
      ((∃∗ w864 : BitVec 64, (fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, (fsp + 880#64) ↦₆₄ w880) ∗
      ((∃∗ w888 : BitVec 64, (fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗ memRegion (fsp + 895#64) 1) ∗
      memRegion (fsp + 896#64) 368 := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (v7_memRegion16_loBytes7_at fsp 592#64 599#64) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <|
    split_step (v7_memRegion16_loBytes7_at fsp 864#64 871#64) <|
    split_step (mem64_entails _) <|
    split_step (v7_memRegion8_loBytes7_at fsp 888#64 895#64) <|
    Entails.refl _

theorem v7_memRegion_1888_400_split (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 400 ⊢
      (∃∗ q1888 : BitVec 128, (fsp + 1888#64) ↦₁₂₈ q1888) ∗
      (∃∗ q1904 : BitVec 128, (fsp + 1904#64) ↦₁₂₈ q1904) ∗
      (∃∗ w1920 : BitVec 64, (fsp + 1920#64) ↦₆₄ w1920) ∗
      memRegion (fsp + 1928#64) 360 := by
  exact split_top <|
    split_step (mem128_entails _) <|
    split_step (mem128_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v7_epilogueStackGaps_pack (fsp w8 tag c1 w32 w40 w48 w56 w64 w72 w80 c4
    w128 w136 w144 w152 l3 l2 p1 w216 : BitVec 64)
    (bs328_dec : { l : List (BitVec 8) // l.length = 328 })
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (w1784 : BitVec 64) :
    memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ w8) ∗ ((fsp + 16#64) ↦₆₄ tag) ∗ ((fsp + 24#64) ↦₆₄ c1) ∗
      ((fsp + 32#64) ↦₆₄ w32) ∗ ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗
      ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
      ((fsp + 80#64) ↦₆₄ w80) ∗ memRegion (fsp + 88#64) 4 ∗
      ((fsp + 96#64) ↦₆₄ c4) ∗
      ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
      ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
      memRegion (fsp + 168#64) 4 ∗
      ((fsp + 176#64) ↦₆₄ l3) ∗ ((fsp + 184#64) ↦₆₄ l2) ∗
      ((fsp + 200#64) ↦₆₄ p1) ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 599#64) 9 ∗
      memRegion (fsp + 840#64) 8 ∗
      memRegion (fsp + 871#64) 9 ∗
      memRegion (fsp + 895#64) 1 ∗
      ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
      ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
      ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
      ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
      v7_ct1SentWordsAt (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep ∗
      ((fsp + 1392#64) ↦₆₄ tag) ∗
      v7_encCellsAt (fsp + 1392#64) bs ∗
      ((fsp + 1784#64) ↦₆₄ w1784) ∗
      memRegion (fsp + 1792#64) 96 ∗
      memRegion (fsp + 1928#64) 360 ∗
      memRegion (fsp + 2288#64) 16 ⊢
    epilogueStackGaps fsp := by
  unfold epilogueStackGaps
  have h92 : memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ w8) ∗ ((fsp + 16#64) ↦₆₄ tag) ∗ ((fsp + 24#64) ↦₆₄ c1) ∗
      ((fsp + 32#64) ↦₆₄ w32) ∗ ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗
      ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
      ((fsp + 80#64) ↦₆₄ w80) ∗ memRegion (fsp + 88#64) 4 ⊢
      memRegion fsp 92 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h96 : ((fsp + 96#64) ↦₆₄ c4) ⊢ memRegion (fsp + 96#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have h128 : ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
      ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ⊢
      memRegion (fsp + 128#64) 32 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h176 : ((fsp + 176#64) ↦₆₄ l3) ∗ ((fsp + 184#64) ↦₆₄ l2) ⊢ memRegion (fsp + 176#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h200 : ((fsp + 200#64) ↦₆₄ p1) ⊢ memRegion (fsp + 200#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have h216 : ((fsp + 216#64) ↦₆₄ w216) ⊢ memRegion (fsp + 216#64) 8 :=
    Drop.pointsTo64_entails_memRegion _ _
  have hbs328 : ((fsp + 896#64) ↦ₛ bs328_dec.val) ⊢ memRegion (fsp + 896#64) 328 := by
    simpa [bs328_dec.property] using
      ProofLib.pointsToBytes_entails_memRegion (fsp + 896#64) bs328_dec.val
  have henc384 : v7_encCellsAt (fsp + 1392#64) bs ⊢ memRegion (fsp + 1400#64) 384 := by
    rw [← v7_bs384_eq_encCells bs hbs (fsp + 1392#64)]
    have ha1400 : (fsp + 1392#64) + 8#64 = fsp + 1400#64 := by bv_omega
    rw [ha1400]
    simpa [hbs] using ProofLib.pointsToBytes_entails_memRegion (fsp + 1400#64) bs
  have h895 : memRegion (fsp + 895#64) 1 ∗
      ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
      ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
      ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
      ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
      v7_ct1SentWordsAt (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep ∗
      ((fsp + 1392#64) ↦₆₄ tag) ∗
      v7_encCellsAt (fsp + 1392#64) bs ∗
      ((fsp + 1784#64) ↦₆₄ w1784) ∗
      memRegion (fsp + 1792#64) 96 ⊢
      memRegion (fsp + 895#64) 993 :=
    collapse_top <| collapse_step (Entails.refl _) <|
      collapse_step hbs328 <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (v7_ct1SentWordsAt_entails_128 (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step henc384 <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have h1928 : memRegion (fsp + 1928#64) 360 ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 :=
    collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 8 ∗
     ((fsp + 8#64) ↦₆₄ w8) ∗ ((fsp + 16#64) ↦₆₄ tag) ∗ ((fsp + 24#64) ↦₆₄ c1) ∗
     ((fsp + 32#64) ↦₆₄ w32) ∗ ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗
     ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
     ((fsp + 80#64) ↦₆₄ w80) ∗ memRegion (fsp + 88#64) 4) ∗
    ((fsp + 96#64) ↦₆₄ c4) ∗
    (((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
     ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152)) ∗
    memRegion (fsp + 168#64) 4 ∗
    (((fsp + 176#64) ↦₆₄ l3) ∗ ((fsp + 184#64) ↦₆₄ l2)) ∗
    ((fsp + 200#64) ↦₆₄ p1) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 599#64) 9 ∗
    memRegion (fsp + 840#64) 8 ∗
    memRegion (fsp + 871#64) 9 ∗
    (memRegion (fsp + 895#64) 1 ∗
     ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
     ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
     ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
     ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
     v7_ct1SentWordsAt (fsp + 1264#64) c1' p1' l1 c2 p2 l2' c3 p3 l3' c4' p4 l4 c5 p5 l5 ep ∗
     ((fsp + 1392#64) ↦₆₄ tag) ∗
     v7_encCellsAt (fsp + 1392#64) bs ∗
     ((fsp + 1784#64) ↦₆₄ w1784) ∗
     memRegion (fsp + 1792#64) 96) ∗
    (memRegion (fsp + 1928#64) 360 ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  exact sepConj_mono h92 (sepConj_mono h96 (sepConj_mono h128 (sepConj_mono_right
    (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono h216 (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono h895 h1928)))))))))))

/-! ## 5. Complete Success Return Path (`+7404 (.ok dec) -> s0.x30`) -/

set_option maxHeartbeats 1600000 in
/-- At `+7404`, when `<PolyDecoder>::from_pb` returns `.ok dec` at `s0.sp - 2400 + 1888`,
    combines `v7_dec_ok_7404_to_7468`, `v7_dec_ok_7468_to_8180`, and `states_from_pb_epilogue_8180`
    to assemble `resultChunkedStatesAt A (F := F) out (.ok (.ct1Sampled ⟨uc, enc, dec⟩))` and
    return to `s0.readReg64 .x30`. -/
theorem v7_dec_ok_7404_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (dec : PolyDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 16 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        memRegion ((s0.sp - 2400#64) + 32#64) 168 ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 1056 ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 96 ∗
        resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.ok dec) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.ok (.ct1Sampled ⟨uc, enc, dec⟩)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  dsimp only [resultPolyDecoderFromPbAt]
  refine SepWP.weaken_pre
    (sepConj_mono (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))
      (sepConj_mono (v7_memRegion_0_16_split (s0.sp - 2400#64))
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (v7_memRegion_32_168_split (s0.sp - 2400#64))
            (sepConj_mono_right
              (sepConj_mono (v7_memRegion_208_1056_split (s0.sp - 2400#64))
                (sepConj_mono_right
                  (sepConj_mono (v7_polyEncoderAt_relocate A ((s0.sp - 2400#64) + 1392#64) out enc)
                    (sepConj_mono_right
                      (sepConj_mono_left
                        (v7_polyDecoderAt_relocate_368 A ((s0.sp - 2400#64) + 1888#64) (out + 528#64) dec)))))))))))) ?_
  wp_conv_pre => simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w0_dec =>
    ProofLib.SepWP.exists_left fun w8_dec =>
    ProofLib.SepWP.exists_left fun w16_dec =>
    ProofLib.SepWP.exists_left fun w24_dec =>
    ProofLib.SepWP.exists_left fun tail368_dec =>
    ProofLib.SepWP.exists_left fun P_dec_heap =>
    ProofLib.SepWP.exists_left fun bs_enc =>
    ProofLib.SepWP.exists_left fun hi32_enc =>
    ProofLib.SepWP.exists_left fun P_enc_heap =>
    ProofLib.SepWP.exists_left fun w888_old =>
    ProofLib.SepWP.exists_left fun w880_old =>
    ProofLib.SepWP.exists_left fun w864_old =>
    ProofLib.SepWP.exists_left fun q848_old =>
    ProofLib.SepWP.exists_left fun w832_old =>
    ProofLib.SepWP.exists_left fun q816_old =>
    ProofLib.SepWP.exists_left fun q800_old =>
    ProofLib.SepWP.exists_left fun q784_old =>
    ProofLib.SepWP.exists_left fun q768_old =>
    ProofLib.SepWP.exists_left fun q752_old =>
    ProofLib.SepWP.exists_left fun q736_old =>
    ProofLib.SepWP.exists_left fun q720_old =>
    ProofLib.SepWP.exists_left fun q704_old =>
    ProofLib.SepWP.exists_left fun q688_old =>
    ProofLib.SepWP.exists_left fun q672_old =>
    ProofLib.SepWP.exists_left fun q656_old =>
    ProofLib.SepWP.exists_left fun q640_old =>
    ProofLib.SepWP.exists_left fun q624_old =>
    ProofLib.SepWP.exists_left fun q608_old =>
    ProofLib.SepWP.exists_left fun w592_old =>
    ProofLib.SepWP.exists_left fun q576_old =>
    ProofLib.SepWP.exists_left fun w232_old =>
    ProofLib.SepWP.exists_left fun w224_old =>
    ProofLib.SepWP.exists_left fun w216_old =>
    ProofLib.SepWP.exists_left fun w208_old =>
    ProofLib.SepWP.exists_left fun w192_old =>
    ProofLib.SepWP.exists_left fun w184_old =>
    ProofLib.SepWP.exists_left fun w176_old =>
    ProofLib.SepWP.exists_left fun d172_old =>
    ProofLib.SepWP.exists_left fun w160_old =>
    ProofLib.SepWP.exists_left fun w152_old =>
    ProofLib.SepWP.exists_left fun w144_old =>
    ProofLib.SepWP.exists_left fun w136_old =>
    ProofLib.SepWP.exists_left fun w128_old =>
    ProofLib.SepWP.exists_left fun w120_old =>
    ProofLib.SepWP.exists_left fun w112_old =>
    ProofLib.SepWP.exists_left fun w104_old =>
    ProofLib.SepWP.exists_left fun w96_old =>
    ProofLib.SepWP.exists_left fun d92_old =>
    ProofLib.SepWP.exists_left fun w80_old =>
    ProofLib.SepWP.exists_left fun w72_old =>
    ProofLib.SepWP.exists_left fun w64_old =>
    ProofLib.SepWP.exists_left fun w56_old =>
    ProofLib.SepWP.exists_left fun w48_old =>
    ProofLib.SepWP.exists_left fun w40_old =>
    ProofLib.SepWP.exists_left fun w32_old =>
    ProofLib.SepWP.exists_left fun w8_old => ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜(out ↦₆₄ v7_polyEncoderTag enc) ∗ ((out + 8#64) ↦ₛ bs_enc.val) ∗
        ((out + 392#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗ P_enc_heap ⊢
        polyEncoderAt A out enc⌝ ∗
    ⌜w0_dec.toNat < 2 ^ 63 ∧
       (((out + 528#64) ↦₆₄ w0_dec) ∗ (((out + 528#64) + 8#64) ↦₆₄ w8_dec) ∗
          (((out + 528#64) + 16#64) ↦₆₄ w16_dec) ∗ (((out + 528#64) + 24#64) ↦₆₄ w24_dec) ∗
          (((out + 528#64) + 32#64) ↦ₛ tail368_dec.val) ∗ P_dec_heap ⊢
          polyDecoderAt A (out + 528#64) dec)⌝ ∗
    (stackAt (s0.sp - 2400#64) allocHookStack ∗
     (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92_old) ∗
     (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120_old) ∗
     (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576_old) ∗
     (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592_old) ∗
     memRegion ((s0.sp - 2400#64) + 896#64) 368 ∗
     (((s0.sp - 2400#64) + 1888#64) ↦₆₄ w0_dec) ∗
     (((s0.sp - 2400#64) + 1896#64) ↦₆₄ w8_dec) ∗
     (((s0.sp - 2400#64) + 1904#64) ↦₆₄ w16_dec) ∗
     (((s0.sp - 2400#64) + 1912#64) ↦₆₄ w24_dec) ∗
     (((s0.sp - 2400#64) + 1920#64) ↦ₛ tail368_dec.val) ∗
     (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
      memRegion (s0.sp - 2400#64) 8 ∗
      (((s0.sp - 2400#64) + 8#64) ↦₆₄ w8_old) ∗
      (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      (((s0.sp - 2400#64) + 32#64) ↦₆₄ w32_old) ∗
      (((s0.sp - 2400#64) + 40#64) ↦₆₄ w40_old) ∗
      (((s0.sp - 2400#64) + 48#64) ↦₆₄ w48_old) ∗
      (((s0.sp - 2400#64) + 56#64) ↦₆₄ w56_old) ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ w64_old) ∗
      (((s0.sp - 2400#64) + 72#64) ↦₆₄ w72_old) ∗
      (((s0.sp - 2400#64) + 80#64) ↦₆₄ w80_old) ∗
      memRegion ((s0.sp - 2400#64) + 88#64) 4 ∗
      (((s0.sp - 2400#64) + 96#64) ↦₆₄ w96_old) ∗
      (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104_old) ∗
      (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112_old) ∗
      (((s0.sp - 2400#64) + 128#64) ↦₆₄ w128_old) ∗
      (((s0.sp - 2400#64) + 136#64) ↦₆₄ w136_old) ∗
      (((s0.sp - 2400#64) + 144#64) ↦₆₄ w144_old) ∗
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ w152_old) ∗
      (((s0.sp - 2400#64) + 160#64) ↦₆₄ w160_old) ∗
      memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
      (((s0.sp - 2400#64) + 172#64) ↦₃₂ d172_old) ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ w176_old) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ w184_old) ∗
      (((s0.sp - 2400#64) + 192#64) ↦₆₄ w192_old) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
      (((s0.sp - 2400#64) + 208#64) ↦₆₄ w208_old) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ w216_old) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224_old) ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ w232_old) ∗
      memRegion ((s0.sp - 2400#64) + 240#64) 328 ∗
      memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
      (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ q608_old) ∗
      (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ q624_old) ∗
      (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ q640_old) ∗
      (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ q656_old) ∗
      (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ q672_old) ∗
      (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ q688_old) ∗
      (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ q704_old) ∗
      (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ q720_old) ∗
      (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ q736_old) ∗
      (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ q752_old) ∗
      (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ q768_old) ∗
      (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ q784_old) ∗
      (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ q800_old) ∗
      (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ q816_old) ∗
      (((s0.sp - 2400#64) + 832#64) ↦₆₄ w832_old) ∗
      memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
      (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ q848_old) ∗
      (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864_old) ∗
      memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
      (((s0.sp - 2400#64) + 880#64) ↦₆₄ w880_old) ∗
      (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888_old) ∗
      memRegion ((s0.sp - 2400#64) + 895#64) 1 ∗
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      (((s0.sp - 2400#64) + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      (((s0.sp - 2400#64) + 1400#64) ↦ₛ bs_enc.val) ∗
      (((s0.sp - 2400#64) + 1784#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗
      memRegion ((s0.sp - 2400#64) + 1792#64) 96 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      P_enc_heap ∗
      P_dec_heap ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
      Rest)) by
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hreloc_enc
  apply ProofLib.SepWP.pure_elim; intro ⟨hw0_dec_lt, hreloc_dec⟩
  refine SepWP.seq (v7_dec_ok_7404_to_7468 hA s0 s1 (s0.sp - 2400#64) out pbA c2 l1
    w0_dec w8_dec w16_dec w24_dec w120_old w592_old d92_old q576_old tail368_dec _
    hfsp_align hw0_dec_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  obtain ⟨bs328_dec, q328_dec, q344_dec, w360_dec, htail368_eq⟩ :=
    v7_tail368_split_328 tail368_dec.val tail368_dec.property
  have h896_eq : (((s0.sp - 2400#64) + 896#64) ↦ₛ tail368_dec.val) =
      (((s0.sp - 2400#64) + 896#64) ↦ₛ bs328_dec.val) ∗
      (((s0.sp - 2400#64) + 1224#64) ↦₁₂₈ q328_dec) ∗
      (((s0.sp - 2400#64) + 1240#64) ↦₁₂₈ q344_dec) ∗
      (((s0.sp - 2400#64) + 1256#64) ↦₆₄ w360_dec) := by
    have h := htail368_eq ((s0.sp - 2400#64) + 896#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have h1400_eq : (((s0.sp - 2400#64) + 1400#64) ↦ₛ bs_enc.val) =
      v7_encCellsAt ((s0.sp - 2400#64) + 1392#64) bs_enc.val := by
    have h := v7_bs384_eq_encCells bs_enc.val bs_enc.property ((s0.sp - 2400#64) + 1392#64)
    have ha : ((s0.sp - 2400#64) + 1392#64) + 8#64 = (s0.sp - 2400#64) + 1400#64 := by bv_omega
    rw [ha] at h
    exact h
  rw [h896_eq, h1400_eq]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v7_memRegion_1888_400_split (s0.sp - 2400#64))))))))) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w1920_old =>
    ProofLib.SepWP.exists_left fun q1904_old =>
    ProofLib.SepWP.exists_left fun q1888_old => ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) allocHookStack ∗
    (((s0.sp - 2400#64) + 8#64) ↦₆₄ w8_old) ∗
    (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
    (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
    (((s0.sp - 2400#64) + 32#64) ↦₆₄ w32_old) ∗
    (((s0.sp - 2400#64) + 40#64) ↦₆₄ w40_old) ∗
    (((s0.sp - 2400#64) + 48#64) ↦₆₄ w48_old) ∗
    (((s0.sp - 2400#64) + 56#64) ↦₆₄ w56_old) ∗
    (((s0.sp - 2400#64) + 64#64) ↦₆₄ w64_old) ∗
    (((s0.sp - 2400#64) + 72#64) ↦₆₄ w72_old) ∗
    (((s0.sp - 2400#64) + 80#64) ↦₆₄ w80_old) ∗
    (((s0.sp - 2400#64) + 96#64) ↦₆₄ w96_old) ∗
    (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104_old) ∗
    (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112_old) ∗
    (((s0.sp - 2400#64) + 128#64) ↦₆₄ w128_old) ∗
    (((s0.sp - 2400#64) + 136#64) ↦₆₄ w136_old) ∗
    (((s0.sp - 2400#64) + 144#64) ↦₆₄ w144_old) ∗
    (((s0.sp - 2400#64) + 152#64) ↦₆₄ w152_old) ∗
    (((s0.sp - 2400#64) + 160#64) ↦₆₄ w160_old) ∗
    (((s0.sp - 2400#64) + 172#64) ↦₃₂ d172_old) ∗
    (((s0.sp - 2400#64) + 176#64) ↦₆₄ w176_old) ∗
    (((s0.sp - 2400#64) + 184#64) ↦₆₄ w184_old) ∗
    (((s0.sp - 2400#64) + 192#64) ↦₆₄ w192_old) ∗
    (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
    (((s0.sp - 2400#64) + 208#64) ↦₆₄ w208_old) ∗
    (((s0.sp - 2400#64) + 216#64) ↦₆₄ w216_old) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224_old) ∗
    (((s0.sp - 2400#64) + 232#64) ↦₆₄ w232_old) ∗
    memRegion ((s0.sp - 2400#64) + 240#64) 328 ∗
    (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ q608_old) ∗
    (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ q624_old) ∗
    (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ q640_old) ∗
    (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ q656_old) ∗
    (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ q672_old) ∗
    (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ q688_old) ∗
    (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ q704_old) ∗
    (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ q720_old) ∗
    (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ q736_old) ∗
    (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ q752_old) ∗
    (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ q768_old) ∗
    (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ q784_old) ∗
    (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ q800_old) ∗
    (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ q816_old) ∗
    (((s0.sp - 2400#64) + 832#64) ↦₆₄ w832_old) ∗
    (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ q848_old) ∗
    (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864_old) ∗
    (((s0.sp - 2400#64) + 880#64) ↦₆₄ w880_old) ∗
    (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888_old) ∗
    (((s0.sp - 2400#64) + 896#64) ↦ₛ bs328_dec.val) ∗
    (((s0.sp - 2400#64) + 1224#64) ↦₁₂₈ q328_dec) ∗
    (((s0.sp - 2400#64) + 1240#64) ↦₁₂₈ q344_dec) ∗
    (((s0.sp - 2400#64) + 1256#64) ↦₆₄ w360_dec) ∗
    v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
    (((s0.sp - 2400#64) + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
    v7_encCellsAt ((s0.sp - 2400#64) + 1392#64) bs_enc.val ∗
    (((s0.sp - 2400#64) + 1784#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗
    (((s0.sp - 2400#64) + 1888#64) ↦₁₂₈ q1888_old) ∗
    (((s0.sp - 2400#64) + 1904#64) ↦₁₂₈ q1904_old) ∗
    (((s0.sp - 2400#64) + 1920#64) ↦₆₄ w1920_old) ∗
    (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
     (((s0.sp - 2400#64) + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 120#64) ↦₆₄ w0_dec) ∗
     (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
     (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
     memRegion (s0.sp - 2400#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 88#64) 4 ∗
     memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
     memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
     memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
     memRegion ((s0.sp - 2400#64) + 895#64) 1 ∗
     memRegion ((s0.sp - 2400#64) + 1792#64) 96 ∗
     memRegion ((s0.sp - 2400#64) + 1928#64) 360 ∗
     memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     P_enc_heap ∗
     P_dec_heap ∗
     v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
     Rest) by ac_rfl)) ?_
  have hreloc_dec_out :
      ((out + 528#64) ↦₆₄ w0_dec) ∗ (((out + 528#64) + 8#64) ↦₆₄ w8_dec) ∗
        (((out + 528#64) + 16#64) ↦₆₄ w16_dec) ∗ (((out + 528#64) + 24#64) ↦₆₄ w24_dec) ∗
        (((out + 528#64) + 32#64) ↦ₛ bs328_dec.val) ∗
        (((out + 528#64) + 360#64) ↦₁₂₈ q328_dec) ∗
        (((out + 528#64) + 376#64) ↦₁₂₈ q344_dec) ∗
        (((out + 528#64) + 392#64) ↦₆₄ w360_dec) ∗ P_dec_heap ⊢
        polyDecoderAt A (out + 528#64) dec := by
    have hp := htail368_eq ((out + 528#64) + 32#64)
    have ha360 : ((out + 528#64) + 32#64) + 328#64 = (out + 528#64) + 360#64 := by bv_omega
    have ha376 : ((out + 528#64) + 32#64) + 344#64 = (out + 528#64) + 376#64 := by bv_omega
    have ha392 : ((out + 528#64) + 32#64) + 360#64 = (out + 528#64) + 392#64 := by bv_omega
    rw [ha360, ha376, ha392] at hp
    rw [hp] at hreloc_dec
    exact Entails.trans (Entails.of_eq (by ac_rfl)) hreloc_dec
  refine SepWP.seq (v7_dec_ok_7468_to_8180 hA s0 s2 (s0.sp - 2400#64) out
    (v7_polyEncoderTag enc) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
    bs_enc.val bs_enc.property hi32_enc enc.idx bs328_dec q328_dec q344_dec w360_dec
    w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
    w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
    w224_old w232_old w832_old w864_old w880_old w888_old w1920_old
    d172_old
    q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
    q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old _
    hfsp_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx24_2 hx26_2 htr2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx6_3, hx19_3, hx23_3, hx8_3, hx15_3, hx20_3, hx13_3,
    hx25_3, hx30_3, hx9_3, hx14_3, hx18_3, hx17_3, hx0_3, hx3_3, hx27_3, hx27_hi16, hx27_hi8,
    hx4_3, hx5_3, hx21_3, hx7_3, hx2_3, hx11_3, hx22_3, hx24_3, hx10_3, hx26_3, hx12_3,
    hx1_3, hx28_3, hx16_3, htr3⟩
  have hgaps := v7_epilogueStackGaps_pack (s0.sp - 2400#64)
    (v7_wordAt bs_enc.val 128) (v7_polyEncoderTag enc) c1
    (((v7_wordAt bs_enc.val 88).extractLsb' 0 8).zeroExtend 64)
    (v7_wordAt bs_enc.val 40) (v7_wordAt bs_enc.val 96) (v7_wordAt bs_enc.val 0)
    p5 (v7_wordAt bs_enc.val 80) (v7_wordAt bs_enc.val 64) c4
    (v7_wordAt bs_enc.val 72) (v7_wordAt bs_enc.val 32) (v7_wordAt bs_enc.val 56)
    (v7_wordAt bs_enc.val 48) l3 l2 p1 (v7_wordAt bs_enc.val 24)
    bs328_dec q328_dec q344_dec w360_dec
    c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
    bs_enc.val bs_enc.property (hi32_enc ++ enc.idx)
  have hst_enc := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  have hP3' : P3 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        ((loByte w8_dec).zeroExtend 32)
        ((loByte (v7_wordAt bs_enc.val 136)).zeroExtend 32)
        l5 uc.epoch w0_dec c3 c5
        (v7_wordAt bs_enc.val 8) p4 p2 bs328_dec.val
        (v7_midQ128 w8_dec w16_dec w24_dec) (w24_dec >>> 8)
        (v7_quadAt bs_enc.val 160) (v7_quadAt bs_enc.val 176)
        (v7_quadAt bs_enc.val 192) (v7_quadAt bs_enc.val 208)
        (v7_quadAt bs_enc.val 224) (v7_quadAt bs_enc.val 240)
        (v7_quadAt bs_enc.val 256) (v7_quadAt bs_enc.val 272)
        (v7_quadAt bs_enc.val 288) (v7_quadAt bs_enc.val 304)
        (v7_quadAt bs_enc.val 320) (v7_quadAt bs_enc.val 336)
        (v7_quadAt bs_enc.val 352) (v7_quadAt bs_enc.val 368)
        (hi32_enc ++ enc.idx)
        (v7_midQ128 (v7_wordAt bs_enc.val 136) (v7_wordAt bs_enc.val 144) (v7_wordAt bs_enc.val 152))
        (v7_wordAt bs_enc.val 152 >>> 8)
        (unshiftWord (v7_wordAt bs_enc.val 112) (loByte (v7_wordAt bs_enc.val 120)))
        (v7_wordAt bs_enc.val 120 >>> 8)
        q328_dec q344_dec w360_dec ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗
      statesFromPbSavedCells s0 ∗
      (P_enc_heap ∗
       P_dec_heap ∗
       v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
       Rest) := by
    refine Entails.trans hP3 ?_
    unfold epilogueStackSlots
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗
       memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
      (memRegion (s0.sp - 2400#64) 8 ∗
       (((s0.sp - 2400#64) + 8#64) ↦₆₄ v7_wordAt bs_enc.val 128) ∗
       (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 32#64) ↦₆₄ ((v7_wordAt bs_enc.val 88).extractLsb' 0 8).zeroExtend 64) ∗
       (((s0.sp - 2400#64) + 40#64) ↦₆₄ v7_wordAt bs_enc.val 40) ∗
       (((s0.sp - 2400#64) + 48#64) ↦₆₄ v7_wordAt bs_enc.val 96) ∗
       (((s0.sp - 2400#64) + 56#64) ↦₆₄ v7_wordAt bs_enc.val 0) ∗
       (((s0.sp - 2400#64) + 64#64) ↦₆₄ p5) ∗
       (((s0.sp - 2400#64) + 72#64) ↦₆₄ v7_wordAt bs_enc.val 80) ∗
       (((s0.sp - 2400#64) + 80#64) ↦₆₄ v7_wordAt bs_enc.val 64) ∗
       memRegion ((s0.sp - 2400#64) + 88#64) 4 ∗
       (((s0.sp - 2400#64) + 96#64) ↦₆₄ c4) ∗
       (((s0.sp - 2400#64) + 128#64) ↦₆₄ v7_wordAt bs_enc.val 72) ∗
       (((s0.sp - 2400#64) + 136#64) ↦₆₄ v7_wordAt bs_enc.val 32) ∗
       (((s0.sp - 2400#64) + 144#64) ↦₆₄ v7_wordAt bs_enc.val 56) ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ v7_wordAt bs_enc.val 48) ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ l3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ l2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ v7_wordAt bs_enc.val 24) ∗
       memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
       memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
       memRegion ((s0.sp - 2400#64) + 895#64) 1 ∗
       (((s0.sp - 2400#64) + 896#64) ↦ₛ bs328_dec.val) ∗
       (((s0.sp - 2400#64) + 1224#64) ↦₁₂₈ q328_dec) ∗
       (((s0.sp - 2400#64) + 1240#64) ↦₁₂₈ q344_dec) ∗
       (((s0.sp - 2400#64) + 1256#64) ↦₆₄ w360_dec) ∗
       v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
       (((s0.sp - 2400#64) + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       v7_encCellsAt ((s0.sp - 2400#64) + 1392#64) bs_enc.val ∗
       (((s0.sp - 2400#64) + 1784#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 96 ∗
       memRegion ((s0.sp - 2400#64) + 1928#64) 360 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
      (memRegion out chunkedStatesSize ∗
       ((((s0.sp - 2400#64) + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
        (((s0.sp - 2400#64) + 104#64) ↦₆₄ l5) ∗
        (((s0.sp - 2400#64) + 112#64) ↦₆₄ uc.epoch) ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ w0_dec) ∗
        (((s0.sp - 2400#64) + 160#64) ↦₆₄ c3) ∗
        (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v7_wordAt bs_enc.val 136)).zeroExtend 32) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ c5) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ v7_wordAt bs_enc.val 8) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ p4) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        (((s0.sp - 2400#64) + 240#64) ↦ₛ bs328_dec.val) ∗
        (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
        (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
        (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v7_quadAt bs_enc.val 160) ∗
        (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v7_quadAt bs_enc.val 176) ∗
        (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v7_quadAt bs_enc.val 192) ∗
        (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v7_quadAt bs_enc.val 208) ∗
        (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v7_quadAt bs_enc.val 224) ∗
        (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v7_quadAt bs_enc.val 240) ∗
        (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v7_quadAt bs_enc.val 256) ∗
        (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v7_quadAt bs_enc.val 272) ∗
        (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v7_quadAt bs_enc.val 288) ∗
        (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v7_quadAt bs_enc.val 304) ∗
        (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v7_quadAt bs_enc.val 320) ∗
        (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v7_quadAt bs_enc.val 336) ∗
        (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v7_quadAt bs_enc.val 352) ∗
        (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v7_quadAt bs_enc.val 368) ∗
        (((s0.sp - 2400#64) + 832#64) ↦₆₄ (hi32_enc ++ enc.idx)) ∗
        (((s0.sp - 2400#64) + 848#64) ↦₁₂₈
          v7_midQ128 (v7_wordAt bs_enc.val 136) (v7_wordAt bs_enc.val 144) (v7_wordAt bs_enc.val 152)) ∗
        (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs_enc.val 152 >>> 8)) ∗
        (((s0.sp - 2400#64) + 880#64) ↦₆₄
          unshiftWord (v7_wordAt bs_enc.val 112) (loByte (v7_wordAt bs_enc.val 120))) ∗
        (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs_enc.val 120 >>> 8)) ∗
        (((s0.sp - 2400#64) + 1888#64) ↦₁₂₈ q328_dec) ∗
        (((s0.sp - 2400#64) + 1904#64) ↦₁₂₈ q344_dec) ∗
        (((s0.sp - 2400#64) + 1920#64) ↦₆₄ w360_dec)) ∗
       statesFromPbSavedCells s0 ∗
       (P_enc_heap ∗
        P_dec_heap ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst_enc (sepConj_mono_left hgaps)) (Entails.of_eq (by ac_rfl))
  have hep := states_from_pb_epilogue_8180 hA s0 s3 out
    ((loByte w8_dec).zeroExtend 32)
    ((loByte (v7_wordAt bs_enc.val 136)).zeroExtend 32)
    l5 uc.epoch w0_dec c3 c5
    (v7_wordAt bs_enc.val 8) p4 p2 bs328_dec.val bs328_dec.property
    (v7_midQ128 w8_dec w16_dec w24_dec) (w24_dec >>> 8)
    (v7_quadAt bs_enc.val 160) (v7_quadAt bs_enc.val 176)
    (v7_quadAt bs_enc.val 192) (v7_quadAt bs_enc.val 208)
    (v7_quadAt bs_enc.val 224) (v7_quadAt bs_enc.val 240)
    (v7_quadAt bs_enc.val 256) (v7_quadAt bs_enc.val 272)
    (v7_quadAt bs_enc.val 288) (v7_quadAt bs_enc.val 304)
    (v7_quadAt bs_enc.val 320) (v7_quadAt bs_enc.val 336)
    (v7_quadAt bs_enc.val 352) (v7_quadAt bs_enc.val 368)
    (hi32_enc ++ enc.idx)
    (v7_midQ128 (v7_wordAt bs_enc.val 136) (v7_wordAt bs_enc.val 144) (v7_wordAt bs_enc.val 152))
    (v7_wordAt bs_enc.val 152 >>> 8)
    (unshiftWord (v7_wordAt bs_enc.val 112) (loByte (v7_wordAt bs_enc.val 120)))
    (v7_wordAt bs_enc.val 120 >>> 8)
    q328_dec q344_dec w360_dec
    (P_enc_heap ∗
     P_dec_heap ∗
     v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
     Rest)
    hsp0_align hpc3 hrun3 hsp3 hx6_3 hx19_3 hx23_3 htr3
  refine SepWP.weaken_pre hP3' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  rw [hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3, hx14_3, hx18_3, hx17_3, hx0_3,
      hx3_3, v7_zext32_setWidth8, hx27_3, hx27_hi16, hx27_hi8, hx4_3, hx5_3,
      hx21_3, v7_zext32_setWidth8, hx7_3, hx2_3, hx11_3, hx22_3, hx24_3, hx10_3,
      hx26_3, hx12_3, hx1_3, hx28_3, hx16_3]
  have hout := v7_epilogueOutFull_entails_ct1Sampled A (F := F)
    out uc enc dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
    bs_enc.val bs_enc.property hi32_enc P_enc_heap hreloc_enc
    w0_dec w8_dec w16_dec w24_dec bs328_dec.val q328_dec q344_dec w360_dec P_dec_heap hreloc_dec_out
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out
      (v7_polyEncoderTag enc)
      (v7_wordAt bs_enc.val 0) (v7_wordAt bs_enc.val 8) (v7_wordAt bs_enc.val 16)
      (v7_wordAt bs_enc.val 24) (v7_wordAt bs_enc.val 32) (v7_wordAt bs_enc.val 40) (v7_wordAt bs_enc.val 48)
      (v7_wordAt bs_enc.val 56) (v7_wordAt bs_enc.val 64) (v7_wordAt bs_enc.val 72) (v7_wordAt bs_enc.val 80)
      ((v7_wordAt bs_enc.val 88).extractLsb' 0 8) ((v7_wordAt bs_enc.val 88).extractLsb' 8 32)
      ((v7_wordAt bs_enc.val 88).extractLsb' 40 16) ((v7_wordAt bs_enc.val 88).extractLsb' 56 8)
      (v7_wordAt bs_enc.val 96) (v7_wordAt bs_enc.val 104) (loByte (v7_wordAt bs_enc.val 112))
      (unshiftWord (v7_wordAt bs_enc.val 112) (loByte (v7_wordAt bs_enc.val 120)))
      (overlapWord7 (unshiftWord (v7_wordAt bs_enc.val 112) (loByte (v7_wordAt bs_enc.val 120)))
        (v7_wordAt bs_enc.val 120 >>> 8))
      (v7_wordAt bs_enc.val 128)
      (((loByte (v7_wordAt bs_enc.val 136)).zeroExtend 32).setWidth 8)
      (v7_midQ128 (v7_wordAt bs_enc.val 136) (v7_wordAt bs_enc.val 144) (v7_wordAt bs_enc.val 152))
      (overlapWord7
        ((v7_midQ128 (v7_wordAt bs_enc.val 136) (v7_wordAt bs_enc.val 144) (v7_wordAt bs_enc.val 152)).extractLsb' 64 64)
        (v7_wordAt bs_enc.val 152 >>> 8))
      (v7_quadAt bs_enc.val 160) (v7_quadAt bs_enc.val 176) (v7_quadAt bs_enc.val 192) (v7_quadAt bs_enc.val 208)
      (v7_quadAt bs_enc.val 224) (v7_quadAt bs_enc.val 240) (v7_quadAt bs_enc.val 256) (v7_quadAt bs_enc.val 272)
      (v7_quadAt bs_enc.val 288) (v7_quadAt bs_enc.val 304) (v7_quadAt bs_enc.val 320) (v7_quadAt bs_enc.val 336)
      (v7_quadAt bs_enc.val 352) (v7_quadAt bs_enc.val 368)
      (hi32_enc ++ enc.idx) c1
      p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5
      l5 uc.epoch w0_dec
      (((loByte w8_dec).zeroExtend 32).setWidth 8)
      (v7_midQ128 w8_dec w16_dec w24_dec)
      (overlapWord7 ((v7_midQ128 w8_dec w16_dec w24_dec).extractLsb' 64 64) (w24_dec >>> 8))
      bs328_dec.val q328_dec q344_dec w360_dec ∗
     P_enc_heap ∗
     P_dec_heap ∗
     v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5) ∗
    Rest ∗
    stackAt s0.sp statesFromPbStack by ac_rfl)) ?_
  exact sepConj_mono_left hout

end CryptoVerification.SpqrV1.States.FromPb
