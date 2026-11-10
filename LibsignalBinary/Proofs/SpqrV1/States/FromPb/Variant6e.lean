/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part E

Epilogue output packing into `resultChunkedStatesAt`, `<PolyDecoder>::from_pb` call and branch steps
(`+9936 -> +10000`), and pure model reductions for `InnerState.headerReceived`.
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

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. Packing `epilogueOutFull` into `resultChunkedStatesAt` for `HeaderReceived` -/

theorem v6hr_midQ128_lo64 (w56 w64 w72 : BitVec 64) :
    (v6hr_midQ128 w56 w64 w72).extractLsb' 0 64 = unshiftWord w56 (loByte w64) :=
  extractLsb'_0_64_append (unshiftWord w64 (loByte w72)) (unshiftWord w56 (loByte w64))

theorem v6hr_loBytes7_midQ128_hi64 (w56 w64 w72 : BitVec 64) :
    EncoderFromPb.loBytes7 ((v6hr_midQ128 w56 w64 w72).extractLsb' 64 64) =
      EncoderFromPb.hiBytes7 w64 := by
  have hhi : (v6hr_midQ128 w56 w64 w72).extractLsb' 64 64 = unshiftWord w64 (loByte w72) :=
    extractLsb'_64_64_append (unshiftWord w64 (loByte w72)) (unshiftWord w56 (loByte w64))
  rw [hhi]
  unfold EncoderFromPb.loBytes7
  rw [← v6hr_hiBytes7_append_loByte_eq_unpack64_unshiftWord w64 w72]
  simp only [EncoderFromPb.hiBytes7, unpack64, List.drop, List.cons_append, List.nil_append, List.take]

theorem v6hr_out_96_104_eq (out w8 : BitVec 64) :
    ((out + 96#64) ↦₈ w8.extractLsb' 0 8) ∗
    ((out + 97#64) ↦₃₂ w8.extractLsb' 8 32) ∗
    ((out + 101#64) ↦₁₆ w8.extractLsb' 40 16) ∗
    ((out + 103#64) ↦₈ w8.extractLsb' 56 8) =
    ((out + 96#64) ↦₆₄ w8) := by
  have h := (v6hr_pointsTo64_split_1_4_2_1 (out + 96#64) w8).symm
  have ha1 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha5 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha7 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rwa [ha1, ha5, ha7] at h

theorem v6hr_out_120_136_eq (out w32 w40 : BitVec 64) :
    ((out + 120#64) ↦₈ loByte w32) ∗
    ((out + 121#64) ↦₆₄ unshiftWord w32 (loByte w40)) ∗
    ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w40) =
    ((out + 120#64) ↦₆₄ w32) ∗ ((out + 128#64) ↦₆₄ w40) := by
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w32 w40).symm
  have ha1 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha9 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha8 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rwa [ha1, ha9, ha8] at h

theorem v6hr_out_144_160_eq (out w56 w64 w72 : BitVec 64) :
    ((out + 144#64) ↦₈ loByte w56) ∗
    ((out + 145#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 0 64) ∗
    ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v6hr_midQ128 w56 w64 w72).extractLsb' 64 64)) =
    ((out + 144#64) ↦₆₄ w56) ∗ ((out + 152#64) ↦₆₄ w64) := by
  rw [v6hr_midQ128_lo64, v6hr_loBytes7_midQ128_hi64]
  have h := (pair64_to_byte_word_tail7 (out + 144#64) w56 w64).symm
  have ha1 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have ha9 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have ha8 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rwa [ha1, ha9, ha8] at h

theorem v6hr_vecU8_pack (A : RustAlloc) (a c p : BitVec 64) (bs : List (BitVec 8)) :
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
    vecU8Payload A c p bs ⊢
    vecU8 A a bs := by
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (vecU8_of_header_payload A a c p bs)

theorem v6hr_vecU8_64_pack (A : RustAlloc) (a c0 p0 : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs.length = 64) :
    ((a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ p0) ∗ ((a + 16#64) ↦₆₄ 64#64)) ∗
    vecU8Payload A c0 p0 bs ⊢
    vecU8 A a bs := by
  have hvec := vecU8_of_header_payload A a c0 p0 bs
  rw [hbs] at hvec
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hvec

theorem v6hr_out_96_104_eq_rest (out w8 : BitVec 64) (Rest : SepProp) :
    ((out + 96#64) ↦₈ w8.extractLsb' 0 8) ∗
    (((out + 97#64) ↦₃₂ w8.extractLsb' 8 32) ∗
     (((out + 101#64) ↦₁₆ w8.extractLsb' 40 16) ∗
      (((out + 103#64) ↦₈ w8.extractLsb' 56 8) ∗ Rest))) =
    ((out + 96#64) ↦₆₄ w8) ∗ Rest := by
  have h := congrArg (· ∗ Rest) (v6hr_out_96_104_eq out w8)
  simpa only [sepConj_assoc] using h

theorem v6hr_out_120_136_eq_rest (out w32 w40 : BitVec 64) (Rest : SepProp) :
    ((out + 120#64) ↦₈ loByte w32) ∗
    (((out + 121#64) ↦₆₄ unshiftWord w32 (loByte w40)) ∗
     (((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w40) ∗ Rest)) =
    ((out + 120#64) ↦₆₄ w32) ∗ (((out + 128#64) ↦₆₄ w40) ∗ Rest) := by
  have h := congrArg (· ∗ Rest) (v6hr_out_120_136_eq out w32 w40)
  simpa only [sepConj_assoc] using h

theorem v6hr_out_144_160_eq_rest (out w56 w64 w72 : BitVec 64) (Rest : SepProp) :
    ((out + 144#64) ↦₈ loByte w56) ∗
    (((out + 145#64) ↦₆₄ (v6hr_midQ128 w56 w64 w72).extractLsb' 0 64) ∗
     (((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v6hr_midQ128 w56 w64 w72).extractLsb' 64 64)) ∗ Rest)) =
    ((out + 144#64) ↦₆₄ w56) ∗ (((out + 152#64) ↦₆₄ w64) ∗ Rest) := by
  have h := congrArg (· ∗ Rest) (v6hr_out_144_160_eq out w56 w64 w72)
  simpa only [sepConj_assoc] using h

theorem v6hr_epilogueOutFull_fold_dec (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 : BitVec 64)
    (dw : v6hr_DecWords)
    (w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8))
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 dw.g0.w0
      (dw.g0.w8.extractLsb' 0 8) (dw.g0.w8.extractLsb' 8 32)
      (dw.g0.w8.extractLsb' 40 16) (dw.g0.w8.extractLsb' 56 8)
      dw.g0.w16 dw.g0.w24 (loByte dw.g0.w32)
      (unshiftWord dw.g0.w32 (loByte dw.g0.w40))
      (overlapWord7 (unshiftWord dw.g0.w32 (loByte dw.g0.w40)) (dw.g0.w40 >>> 8))
      dw.g0.w48
      (((loByte dw.g0.w56).zeroExtend 32).setWidth 8)
      (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72)
      (overlapWord7 ((v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72).extractLsb' 64 64) (dw.g1.w72 >>> 8))
      dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
      dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
      dw.g3.u304 dw.g3.u312 dw.g3.u320 dw.g3.u328 dw.g3.u336 dw.g3.u344
      dw.g4.u352 dw.g4.u360 dw.g4.u368 dw.g4.u376 dw.g4.u384 dw.g4.u392
      w488 w496 w504 w512 w520 w528 b536 q537 w552 bs240 q888 q904 w920 =
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
    ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
    ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗ ((out + 80#64) ↦₆₄ w80) ∗
    v6hr_decWordsAt (out + 88#64) dw ∗
    (((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗ ((out + 504#64) ↦₆₄ w504) ∗
     ((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
     ((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
     ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)) := by
  rw [v6hr_overlapWord7_unshift dw.g0.w32 dw.g0.w40,
      v6hr_zext32_setWidth8 (loByte dw.g0.w56),
      v6hr_overlapWord7_midQ128_lsr8 dw.g0.w56 dw.g1.w64 dw.g1.w72]
  unfold epilogueOutFull v6hr_decWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    v6hr_out_96_104_eq_rest, v6hr_out_120_136_eq_rest, v6hr_out_144_160_eq_rest]

theorem v6hr_reassoc_out_ok
    (W0 W8 W16 W24 W32 W40 W48 W56 W64 W72 W80
     P_dec_words P_tail P_v1 P_v2 P_v0 P_dec_heap : SepProp) :
    (W0 ∗ W8 ∗ W16 ∗ W24 ∗ W32 ∗ W40 ∗ W48 ∗ W56 ∗ W64 ∗ W72 ∗ W80 ∗ P_dec_words ∗ P_tail) ∗
    P_v1 ∗ P_v2 ∗ P_v0 ∗ P_dec_heap =
    W0 ∗
    ((W8 ∗ W16 ∗ W24) ∗ P_v1) ∗
    ((W32 ∗ W40 ∗ W48) ∗ P_v2) ∗
    ((W56 ∗ W64 ∗ W72) ∗ P_v0) ∗
    W80 ∗
    (P_dec_words ∗ P_dec_heap) ∗
    P_tail := by
  ac_rfl

theorem v6hr_epilogueOutFull_entails_ok
    (A : RustAlloc) {F : ShaCompress} (out c0 p0 p1_new p2_new ep : BitVec 64)
    (rootKey macKey hdrBytes : List (BitVec 8))
    (dec : PolyDecoder) (dw : v6hr_DecWords)
    (w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64)
    (hhdr : hdrBytes.length = 64) :
    epilogueOutFull out
      8#64
      (BitVec.ofNat 64 rootKey.length) p1_new (BitVec.ofNat 64 rootKey.length)
      (BitVec.ofNat 64 macKey.length) p2_new (BitVec.ofNat 64 macKey.length)
      c0 p0 64#64 ep dw.g0.w0
      (dw.g0.w8.extractLsb' 0 8) (dw.g0.w8.extractLsb' 8 32)
      (dw.g0.w8.extractLsb' 40 16) (dw.g0.w8.extractLsb' 56 8)
      dw.g0.w16 dw.g0.w24 (loByte dw.g0.w32)
      (unshiftWord dw.g0.w32 (loByte dw.g0.w40))
      (overlapWord7 (unshiftWord dw.g0.w32 (loByte dw.g0.w40)) (dw.g0.w40 >>> 8))
      dw.g0.w48
      (((loByte dw.g0.w56).zeroExtend 32).setWidth 8)
      (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72)
      (overlapWord7 ((v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72).extractLsb' 64 64) (dw.g1.w72 >>> 8))
      dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
      dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
      dw.g3.u304 dw.g3.u312 dw.g3.u320 dw.g3.u328 dw.g3.u336 dw.g3.u344
      dw.g4.u352 dw.g4.u360 dw.g4.u368 dw.g4.u376 dw.g4.u384 dw.g4.u392
      w488 w496 w504 w512 w520 w528 b536 q537 w552 bs240 q888 q904 w920 ∗
    vecU8Payload A (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
    vecU8Payload A (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
    vecU8Payload A c0 p0 hdrBytes ∗
    v6hr_decHeap A dec dw ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.headerReceived
        { uc := { auth := { rootKey := rootKey, macKey := macKey }, hdr := hdrBytes, epoch := ep }
          receiving_ek := dec })) := by
  rw [v6hr_epilogueOutFull_fold_dec]
  dsimp only [resultChunkedStatesAt, chunkedStatesAt,
    chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt, authenticatorAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_rhs => simp only [sepConj_assoc]
  rw [v6hr_reassoc_out_ok]
  have h1 := v6hr_vecU8_pack A (out + 8#64) (BitVec.ofNat 64 rootKey.length) p1_new rootKey
  have h2 := v6hr_vecU8_pack A (out + 32#64) (BitVec.ofNat 64 macKey.length) p2_new macKey
  have h0 := v6hr_vecU8_64_pack A (out + 56#64) c0 p0 hdrBytes hhdr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h0
  have hdec := v6hr_polyDecoderAt_pack A (out + 88#64) dec dw
  have htail := epilogueOut_tail_488_entails_440 out
    w488 w496 w504 w512 w520 w528 b536 q537 w552 bs240 hbs240 q888 q904 w920
  exact sepConj_mono_right (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h0
    (sepConj_mono_right (sepConj_mono hdec htail)))))

/-! ## 2. Decoder Call (`+9936 -> +10000`) and Error/Ok Branches -/

theorem v6hr_protoPolynomialDecoderAt_pack (A : RustAlloc) (a : BitVec 64)
    (d : ProtoPolynomialDecoder) (ptsCap ptsPtr w120 : BitVec 64)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : EncoderFromPb.loByte w120 = boolByte d.isComplete) :
    ((a ↦₆₄ ptsCap) ∗ ((a + 8#64) ↦₆₄ ptsPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
     ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗ ((a + 32#64) ↦₆₄ w120)) ∗
    (if ptsCap = 0#64 then emp
     else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
       memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ⊢
    protoPolynomialDecoderAt A a d := by
  unfold protoPolynomialDecoderAt vecVecU8At vecOf Poly.vecHeaderBytes vecAt vecBuf vecHeader
    protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
  simp only [sepExists_sepConj_left, sepConj_assoc]
  have hb8 := v6hr_pointsTo64_entails_byte_pad7 (a + 32#64) w120 (boolByte d.isComplete) hw120
  have ha33 : (a + 32#64) + 1#64 = a + 33#64 := by bv_omega
  rw [ha33] at hb8
  have h123 : d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 := ⟨h1, h2, h3⟩
  refine Entails.sepExists_right ptsCap (Entails.sepExists_right ptsPtr ?_)
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((a + 32#64) ↦₆₄ w120) ∗
      ((a ↦₆₄ ptsCap) ∗ ((a + 8#64) ↦₆₄ ptsPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
       ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗
       (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24))) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hb8) ?_
  refine Entails.trans (Entails.pure_right h123 (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_memRegion_40_split (a : BitVec 64) :
    memRegion a 40 ⊢
      (∃∗ u0 : BitVec 64, (a ↦₆₄ u0)) ∗
      (∃∗ u8 : BitVec 64, ((a + 8#64) ↦₆₄ u8)) ∗
      (∃∗ u16 : BitVec 64, ((a + 16#64) ↦₆₄ u16)) ∗
      (∃∗ u24 : BitVec 32, ((a + 24#64) ↦₃₂ u24)) ∗
      (∃∗ u28 : BitVec 32, ((a + 28#64) ↦₃₂ u28)) ∗
      (∃∗ u32 : BitVec 64, ((a + 32#64) ↦₆₄ u32)) := by
  exact split_top <|
    split_step0 (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem32_entails _) <|
    split_step (mem32_entails _) <|
    mem64_entails _

@[simp, arm64_norm, wp_norm]
theorem v6hr_bfm_reconstruct_64 (x : BitVec 64) :
    (((x >>> 8) &&& 72057594037927935#64) <<< 8) |||
      (((x.setWidth 32).zeroExtend 64) &&& 255#64) = x := by
  bv_kernel

@[simp, arm64_norm, wp_norm]
theorem v6hr_bfm_reconstruct_64' (x : BitVec 64) :
    (((x.setWidth 32).zeroExtend 64) &&& 255#64) |||
      (((x >>> 8) &&& 72057594037927935#64) <<< 8) = x := by
  bv_kernel

theorem v6hr_step_9936_dec_none_to_10416
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (P : SepProp)
    (hl1 : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10416#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  have hne_l1 := cap_add_one_beq_zero_false hl1
  dsimp only [noneCap] at hx28_1
  states_from_pb_fetches_range b (Rust.withPanics ext) 9936 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem v6hr_step_9936_dec_some_to_35448
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : EncoderFromPb.loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          (memRegion ((s0.sp - 2400#64) + 1888#64) polyDecoderSize ∗
           protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1392#64) d ∗
           A.pool ∗ stackAt (s0.sp - 2400#64) decoderFromPbStack) ∗
          ((((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest)) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        s2.readReg64 .x1 = (s0.sp - 2400#64) + 1392#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10000#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = p1_new ∧
        s2.readReg64 .x26 = l1 ∧
        s2.readReg64 .x27 = c0 ∧
        TraceCalleeSaved s2 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hne_l1 := cap_add_one_beq_zero_false hl1
  have hpts_lt : ptsCap.toNat < 2 ^ 63 := by omega
  have hne_c3 := cap_add_one_beq_zero_false hpts_lt
  have hw11 : (d.ptsNeeded.zeroExtend 64).setWidth 32 = d.ptsNeeded := by bv_kernel
  have hw12 : (d.polys.zeroExtend 64).setWidth 32 = d.polys := by bv_kernel
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (v6hr_memRegion_40_split ((s0.sp - 2400#64) + 1392#64)))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u32
  apply ProofLib.SepWP.exists_left; intro u28
  apply ProofLib.SepWP.exists_left; intro u24
  apply ProofLib.SepWP.exists_left; intro u16
  apply ProofLib.SepWP.exists_left; intro u8
  apply ProofLib.SepWP.exists_left; intro u0
  states_from_pb_fetches_range b (Rust.withPanics ext) 9936 64
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpack := v6hr_protoPolynomialDecoderAt_pack A ((s0.sp - 2400#64) + 1392#64)
      d ptsCap ptsPtr w120 h1 h2 h3 hw120
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
    dsimp only [polyDecoderSize, decoderFromPbStack]
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64 + 1392#64) ↦₆₄ ptsCap) ∗
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ ptsPtr) ∗
          ((s0.sp - 2400#64 + 1408#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
          ((s0.sp - 2400#64 + 1416#64) ↦₃₂ d.ptsNeeded) ∗
          ((s0.sp - 2400#64 + 1420#64) ↦₃₂ d.polys) ∗
          ((s0.sp - 2400#64 + 1424#64) ↦₆₄ w120)) ∗
         (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24))) ∗
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
         A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v6hr_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    encoderFromPbOnPanic sm sf ∗ F ⊢ statesFromPbOnPanic s0 sf := by
  unfold encoderFromPbOnPanic statesFromPbOnPanic
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v6hr_sepWPp_call_entails {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    (x : α) (s : State) (P_step F : SepProp) (Qpan : State → SepProp)
    (post : State → SepProp → Prop)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => hpan sf)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v6hr_step_9936_dec_some_to_10000
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbOkExt b A ext)
    (s0 s1 : State) (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : EncoderFromPb.loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10000#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (decoderFromPbResult d) ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
          A.pool ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine v6hr_sepWPp_seq_clean
    (v6hr_step_9936_dec_some_to_35448 s0 s1 out c0 p1_new l1 ptsCap ptsPtr w120 d Rest
      hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx23_1 hx24_1
      hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  have hsp2_align : s2.spAligned = true := by
    change (s2.sp &&& 15#64 == 0#64) = true
    rwa [hsp2]
  refine v6hr_sepWPp_call_entails (v6hr_sub_ok_decoder_from_pb hdec)
    ⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 1392#64, d⟩
    s2 _ _ (statesFromPbOnPanic s0) _ hpc2 hrun2 hsp2_align hx30_2 ?_ ?_ (fun _ _ => rfl) ?_
  · dsimp only [decoderFromPbSpec]
    rw [hsp2]
    exact Entails.pure_right ⟨hx0_2, hx1_2⟩ (Entails.refl _)
  · intro sf
    exact v6hr_onPanic_frame_entails htr2
  · intro sf hpcf hrunf hspf hcsf
    rcases hcsf with ⟨hx19_f, _, hx21_f, _, _, _, _, hx26_f, hx27_f, _, _, hvregs_f⟩
    dsimp only [decoderFromPbSpec]
    rw [sepConj_assoc]
    apply ProofLib.SepWP.pure_elim; intro htr_f
    apply ProofLib.SepWP.done hpcf hrunf
    refine ⟨?_, by rw [hspf, hsp2], by rw [hx19_f, hx19_2], by rw [hx21_f, hx21_2],
      by rw [hx26_f, hx26_2], by rw [hx27_f, hx27_2], ⟨htr_f.trans htr2.1, hvregs_f.trans htr2.2⟩⟩
    rw [hsp2]
    dsimp only [protoPolynomialDecoderSize, decoderFromPbStack]
    exact Entails.of_eq (by ac_rfl)

theorem v6hr_resultPolyDecoder_err_entails_400 (A : RustAlloc) (a : BitVec 64) (e : PolynomialError) :
    resultPolyDecoderFromPbAt A a (.error e) ⊢ memRegion a 400 := by
  unfold resultPolyDecoderFromPbAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo8_entails_memRegion _ _) <|
    Entails.refl _

theorem v6hr_step_10000_err_to_10492
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (e : PolynomialError) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10000#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10492#64) s1
      (resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error e) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
  have herr := v6hr_resultPolyDecoder_err_entails_400 A ((s0.sp - 2400#64) + 1888#64) e
  unfold resultPolyDecoderFromPbAt at herr ⊢
  dsimp only [noneCap] at herr ⊢
  rw [h1888] at herr ⊢
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 10000 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · refine Entails.trans
      (Entails.of_eq (show _ =
        (((s0.sp - 512#64) ↦₆₄ 18446744073709551615#64) ∗
         ((s0.sp - 512#64 + resultPolyDecoderErrByteOff) ↦₈ polynomialErrorByte e) ∗
         memRegion (s0.sp - 512#64 + 9#64) resultPolyDecoderErrTailSize) ∗ Rest by ac_rfl)) ?_
    exact sepConj_mono_left herr
  · wp_done

/-! ## 3. Pure Model Reductions and Top-Level Composition (`+1464 -> s0.x30`) -/

theorem v6hr_from_pb_hdr_eq64_dec_none (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64)
    (hlen : hdr.length = 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived
          { uc := some { hdr := hdr, auth := some authPb, epoch := epoch },
            receivingEk := none }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [HEADER_SIZE, hlen, decoderFromPbStateDecode_none, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_hdr_eq64_dec_err (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64)
    (decPb : PolynomialDecoder) (e : PolynomialError)
    (heq : decPb.ptsNeeded = 576#32) (hlen : hdr.length = 64)
    (herr : decoderFromPbResult (pbToProtoPolyDecoder decPb) = .error e) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived
          { uc := some { hdr := hdr, auth := some authPb, epoch := epoch },
            receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [HEADER_SIZE, ENCAPSULATION_KEY_SIZE, heq, hlen, decoderFromPbStateDecode_some, herr,
    bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_hdr_eq64_dec_ok (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64)
    (decPb : PolynomialDecoder) (dec : PolyDecoder)
    (heq : decPb.ptsNeeded = 576#32) (hlen : hdr.length = 64)
    (hok : decoderFromPbResult (pbToProtoPolyDecoder decPb) = .ok dec) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived
          { uc := some { hdr := hdr, auth := some authPb, epoch := epoch },
            receivingEk := some decPb }) } =
    .ok (.headerReceived
      { uc := { epoch := epoch, auth := { rootKey := authPb.rootKey, macKey := authPb.macKey }, hdr := hdr },
        receiving_ek := dec }) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [HEADER_SIZE, ENCAPSULATION_KEY_SIZE, heq, hlen, decoderFromPbStateDecode_some, hok,
    (show (spqrAuthApi F).from_pb = Authenticator.fromPb from rfl), Authenticator.fromPb,
    bind, Except.bind, pure, Except.pure]

theorem v6hr_stack_0_240_8180_split (fsp l0 ep p2_new p0 l2 : BitVec 64) :
    memRegion fsp 80 ∗ ((fsp + 80#64) ↦₆₄ l0) ∗ memRegion (fsp + 88#64) 40 ∗
      ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 136#64) ↦₆₄ p2_new) ∗
      ((fsp + 144#64) ↦₆₄ p0) ∗ memRegion (fsp + 152#64) 8 ∗
      memRegion (fsp + 176#64) 32 ∗ ((fsp + 216#64) ↦₆₄ l2) ⊢
      (∃∗ d92 : BitVec 32, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64,
       ∃∗ w120 : BitVec 64, ∃∗ w192 : BitVec 64,
        ((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192)) ∗
      memRegion fsp 92 ∗
      memRegion (fsp + 96#64) 8 ∗
      memRegion (fsp + 128#64) 32 ∗
      memRegion (fsp + 176#64) 16 ∗
      memRegion (fsp + 200#64) 8 ∗
      memRegion (fsp + 216#64) 8 := by
  have h160 :
      memRegion fsp 80 ∗ ((fsp + 80#64) ↦₆₄ l0) ∗ memRegion (fsp + 88#64) 40 ∗
      ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 136#64) ↦₆₄ p2_new) ∗
      ((fsp + 144#64) ↦₆₄ p0) ∗ memRegion (fsp + 152#64) 8 ⊢
      memRegion fsp 160 := by
    exact collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Entails.refl _
  have hs160 :
      memRegion fsp 160 ⊢
      memRegion fsp 92 ∗
      (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      memRegion (fsp + 96#64) 8 ∗
      (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
      (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗
      memRegion (fsp + 128#64) 32 := by
    exact split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem32_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      Entails.refl _
  have hs32 :
      memRegion (fsp + 176#64) 32 ⊢
      memRegion (fsp + 176#64) 16 ∗
      (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      memRegion (fsp + 200#64) 8 := by
    exact split_top <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      Entails.refl _
  have h216 := Drop.pointsTo64_entails_memRegion (fsp + 216#64) l2
  refine Entails.trans
    (Entails.of_eq (show _ =
      (memRegion fsp 80 ∗ ((fsp + 80#64) ↦₆₄ l0) ∗ memRegion (fsp + 88#64) 40 ∗
       ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 136#64) ↦₆₄ p2_new) ∗
       ((fsp + 144#64) ↦₆₄ p0) ∗ memRegion (fsp + 152#64) 8) ∗
      memRegion (fsp + 176#64) 32 ∗
      ((fsp + 216#64) ↦₆₄ l2) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (Entails.trans h160 hs160) (sepConj_mono hs32 h216)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w192; apply Entails.sepExists_elim; intro w120
  apply Entails.sepExists_elim; intro w112; apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro d92
  exact Entails.sepExists_right d92 (Entails.sepExists_right w104 (Entails.sepExists_right w112
    (Entails.sepExists_right w120 (Entails.sepExists_right w192 (Entails.of_eq (by ac_rfl))))))

theorem v6hr_memRegion_entails_bs :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 →
      ProofLib.memRegion a n ⊢
        ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a,
        sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (v6hr_memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]
    exact Entails.refl _

theorem v6hr_memRegion_328_entails_bs (a : BitVec 64) :
    ProofLib.memRegion a 328 ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) :=
  v6hr_memRegion_entails_bs 328 a (by decide)

theorem v6hr_stack_240_608_8180_split (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 368 ⊢
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 },
       ∃∗ q576 : BitVec 128, ∃∗ w592 : BitVec 64,
        ((fsp + 240#64) ↦ₛ bs240.val) ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗
        ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 599#64) 9 := by
  have hs :
      memRegion (fsp + 240#64) 368 ⊢
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗
       memRegion (fsp + 599#64) 9) := by
    exact split_top <|
      split_step (v6hr_memRegion_328_entails_bs (fsp + 240#64)) <|
      split_step (Entails.refl _) <|
      split_step (mem128_entails _) <|
      v6hr_memRegion_entails_loBytes7_and_tail fsp 592#64 599#64 8
  refine Entails.trans hs ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w592
  apply Entails.sepExists_elim; intro q576
  apply Entails.sepExists_elim; intro bs240
  exact Entails.sepExists_right bs240 (Entails.sepExists_right q576
    (Entails.sepExists_right w592 (Entails.of_eq (by ac_rfl))))

set_option maxHeartbeats 800000 in
theorem v6hr_stack_1888_2304_8180_split (fsp : BitVec 64) (dw : v6hr_DecWords) :
    v6hr_decWordsAt (fsp + 1888#64) dw ∗ memRegion (fsp + 2288#64) 16 ⊢
      ((fsp + 1888#64) ↦₁₂₈ (dw.g0.w8 ++ dw.g0.w0)) ∗
      ((fsp + 1904#64) ↦₁₂₈ (dw.g0.w24 ++ dw.g0.w16)) ∗
      ((fsp + 1920#64) ↦₆₄ dw.g0.w32) ∗
      memRegion (fsp + 1928#64) 376 := by
  have h1888 :
      ((fsp + 1888#64) ↦₆₄ dw.g0.w0) ∗ (((fsp + 1888#64) + 8#64) ↦₆₄ dw.g0.w8) =
      ((fsp + 1888#64) ↦₁₂₈ (dw.g0.w8 ++ dw.g0.w0)) :=
    EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (fsp + 1888#64) dw.g0.w0 dw.g0.w8
  have h1904 :
      (((fsp + 1888#64) + 16#64) ↦₆₄ dw.g0.w16) ∗ (((fsp + 1888#64) + 24#64) ↦₆₄ dw.g0.w24) =
      ((fsp + 1904#64) ↦₁₂₈ (dw.g0.w24 ++ dw.g0.w16)) := by
    have h := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 1888#64) + 16#64) dw.g0.w16 dw.g0.w24
    have ha1 : (fsp + 1888#64) + 16#64 = fsp + 1904#64 := by bv_omega
    have ha2 : (fsp + 1888#64) + 16#64 + 8#64 = (fsp + 1888#64) + 24#64 := by bv_omega
    rw [ha2] at h
    exact ha1 ▸ h
  have h1920 : (fsp + 1888#64) + 32#64 = fsp + 1920#64 := by bv_omega
  have h376 :
      (((fsp + 1888#64) + 40#64) ↦₆₄ dw.g0.w40) ∗
      (((fsp + 1888#64) + 48#64) ↦₆₄ dw.g0.w48) ∗
      (((fsp + 1888#64) + 56#64) ↦₆₄ dw.g0.w56) ∗
      (((fsp + 1888#64) + 64#64) ↦₆₄ dw.g1.w64) ∗
      (((fsp + 1888#64) + 72#64) ↦₆₄ dw.g1.w72) ∗
      (((fsp + 1888#64) + 80#64) ↦₁₂₈ dw.g1.q80) ∗
      (((fsp + 1888#64) + 96#64) ↦₁₂₈ dw.g1.q96) ∗
      (((fsp + 1888#64) + 112#64) ↦₁₂₈ dw.g1.q112) ∗
      (((fsp + 1888#64) + 128#64) ↦₁₂₈ dw.g1.q128) ∗
      (((fsp + 1888#64) + 144#64) ↦₁₂₈ dw.g1.q144) ∗
      (((fsp + 1888#64) + 160#64) ↦₁₂₈ dw.g1.q160) ∗
      (((fsp + 1888#64) + 176#64) ↦₁₂₈ dw.g2.q176) ∗
      (((fsp + 1888#64) + 192#64) ↦₁₂₈ dw.g2.q192) ∗
      (((fsp + 1888#64) + 208#64) ↦₁₂₈ dw.g2.q208) ∗
      (((fsp + 1888#64) + 224#64) ↦₁₂₈ dw.g2.q224) ∗
      (((fsp + 1888#64) + 240#64) ↦₁₂₈ dw.g2.q240) ∗
      (((fsp + 1888#64) + 256#64) ↦₁₂₈ dw.g2.q256) ∗
      (((fsp + 1888#64) + 272#64) ↦₁₂₈ dw.g2.q272) ∗
      (((fsp + 1888#64) + 288#64) ↦₁₂₈ dw.g2.q288) ∗
      (((fsp + 1888#64) + 304#64) ↦₆₄ dw.g3.u304) ∗
      (((fsp + 1888#64) + 312#64) ↦₆₄ dw.g3.u312) ∗
      (((fsp + 1888#64) + 320#64) ↦₆₄ dw.g3.u320) ∗
      (((fsp + 1888#64) + 328#64) ↦₆₄ dw.g3.u328) ∗
      (((fsp + 1888#64) + 336#64) ↦₆₄ dw.g3.u336) ∗
      (((fsp + 1888#64) + 344#64) ↦₆₄ dw.g3.u344) ∗
      (((fsp + 1888#64) + 352#64) ↦₆₄ dw.g4.u352) ∗
      (((fsp + 1888#64) + 360#64) ↦₆₄ dw.g4.u360) ∗
      (((fsp + 1888#64) + 368#64) ↦₆₄ dw.g4.u368) ∗
      (((fsp + 1888#64) + 376#64) ↦₆₄ dw.g4.u376) ∗
      (((fsp + 1888#64) + 384#64) ↦₆₄ dw.g4.u384) ∗
      (((fsp + 1888#64) + 392#64) ↦₆₄ dw.g4.u392) ∗
      memRegion ((fsp + 1888#64) + 400#64) 16 ⊢
      memRegion ((fsp + 1888#64) + 40#64) 376 := by
    exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (pointsTo128_entails_memRegion_16 _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Entails.refl _
  rw [show (fsp + 1888#64) + 400#64 = fsp + 2288#64 by bv_omega,
      show (fsp + 1888#64) + 40#64 = fsp + 1928#64 by bv_omega] at h376
  unfold v6hr_decWordsAt
  rw [← sepConj_assoc ((fsp + 1888#64) ↦₆₄ dw.g0.w0), h1888,
      ← sepConj_assoc (((fsp + 1888#64) + 16#64) ↦₆₄ dw.g0.w16), h1904, h1920]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h376)))

set_option maxHeartbeats 800000 in
theorem v6hr_stack_8180_entails (fsp l0 ep p2_new p0 l2 p1_new : BitVec 64) (dw : v6hr_DecWords) :
    ((fsp + 80#64) ↦₆₄ l0) ∗
      ((fsp + 128#64) ↦₆₄ ep) ∗
      ((fsp + 136#64) ↦₆₄ p2_new) ∗
      ((fsp + 144#64) ↦₆₄ p0) ∗
      ((fsp + 216#64) ↦₆₄ l2) ∗
      v6hr_stagingSlotsPost fsp dw p1_new ∗
      v6hr_decWordsAt (fsp + 1888#64) dw ∗
      v6hr_stackRest10000 fsp ⊢
      ∃∗ d92 : BitVec 32, ∃∗ w104 : BitVec 64, ∃∗ w112 : BitVec 64,
      ∃∗ w120 : BitVec 64, ∃∗ w192 : BitVec 64,
      ∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 },
      ∃∗ q576 : BitVec 128, ∃∗ w592 : BitVec 64,
        epilogueStackSlots fsp
          d92 ((loByte dw.g0.w56).zeroExtend 32)
          w104 w112 w120 dw.g4.u360 w192 p1_new dw.g4.u392 dw.g3.u344
          bs240.val q576 w592
          dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
          dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
          dw.g3.u304 (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72) (dw.g1.w72 >>> 8)
          (unshiftWord dw.g0.w32 (loByte dw.g0.w40)) (dw.g0.w40 >>> 8)
          (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32 ∗
        epilogueStackGaps fsp := by
  have hs0 := v6hr_stack_0_240_8180_split fsp l0 ep p2_new p0 l2
  have hs240 := v6hr_stack_240_608_8180_split fsp
  have hs1888 := v6hr_stack_1888_2304_8180_split fsp dw
  unfold v6hr_stackRest10000
  refine Entails.trans
    (Entails.of_eq (show _ =
      (memRegion fsp 80 ∗ ((fsp + 80#64) ↦₆₄ l0) ∗ memRegion (fsp + 88#64) 40 ∗
       ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 136#64) ↦₆₄ p2_new) ∗
       ((fsp + 144#64) ↦₆₄ p0) ∗ memRegion (fsp + 152#64) 8 ∗
       memRegion (fsp + 176#64) 32 ∗ ((fsp + 216#64) ↦₆₄ l2)) ∗
      memRegion (fsp + 240#64) 368 ∗
      (v6hr_decWordsAt (fsp + 1888#64) dw ∗ memRegion (fsp + 2288#64) 16) ∗
      (v6hr_stagingSlotsPost fsp dw p1_new ∗
       memRegion (fsp + 168#64) 4 ∗
       memRegion (fsp + 840#64) 8 ∗
       memRegion (fsp + 871#64) 9 ∗
       memRegion (fsp + 895#64) 993) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hs0 (sepConj_mono hs240 (sepConj_mono_left hs1888))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs240; apply Entails.sepExists_elim; intro q576
  apply Entails.sepExists_elim; intro w592; apply Entails.sepExists_elim; intro d92
  apply Entails.sepExists_elim; intro w104; apply Entails.sepExists_elim; intro w112
  apply Entails.sepExists_elim; intro w120; apply Entails.sepExists_elim; intro w192
  refine Entails.sepExists_right d92 (Entails.sepExists_right w104 (Entails.sepExists_right w112
    (Entails.sepExists_right w120 (Entails.sepExists_right w192 (Entails.sepExists_right bs240
      (Entails.sepExists_right q576 (Entails.sepExists_right w592 ?_)))))))
  unfold v6hr_stagingSlotsPost epilogueStackSlots epilogueStackGaps
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_lowStackAt_eq_fsp (sp0 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) :
    v6hr_lowStackAt sp0 v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 =
      (((sp0 - 2400#64) + 80#64) ↦₆₄ v80) ∗
      (((sp0 - 2400#64) + 128#64) ↦₆₄ v128) ∗
      (((sp0 - 2400#64) + 136#64) ↦₆₄ v136) ∗
      (((sp0 - 2400#64) + 144#64) ↦₆₄ v144) ∗
      (((sp0 - 2400#64) + 184#64) ↦₃₂ d184) ∗
      (((sp0 - 2400#64) + 192#64) ↦₆₄ v192) ∗
      (((sp0 - 2400#64) + 200#64) ↦₃₂ d200) ∗
      (((sp0 - 2400#64) + 208#64) ↦₆₄ v208) ∗
      (((sp0 - 2400#64) + 216#64) ↦₆₄ v216) ∗
      (((sp0 - 2400#64) + 224#64) ↦₆₄ v224) ∗
      (((sp0 - 2400#64) + 232#64) ↦₆₄ v232) ∗
      v6hr_lowStackGaps sp0 := by
  unfold v6hr_lowStackAt
  rw [show (sp0 - 2400#64) + 80#64 = sp0 - 2320#64 by bv_omega,
      show (sp0 - 2400#64) + 128#64 = sp0 - 2272#64 by bv_omega,
      show (sp0 - 2400#64) + 136#64 = sp0 - 2264#64 by bv_omega,
      show (sp0 - 2400#64) + 144#64 = sp0 - 2256#64 by bv_omega,
      show (sp0 - 2400#64) + 184#64 = sp0 - 2216#64 by bv_omega,
      show (sp0 - 2400#64) + 192#64 = sp0 - 2208#64 by bv_omega,
      show (sp0 - 2400#64) + 200#64 = sp0 - 2200#64 by bv_omega,
      show (sp0 - 2400#64) + 208#64 = sp0 - 2192#64 by bv_omega,
      show (sp0 - 2400#64) + 216#64 = sp0 - 2184#64 by bv_omega,
      show (sp0 - 2400#64) + 224#64 = sp0 - 2176#64 by bv_omega,
      show (sp0 - 2400#64) + 232#64 = sp0 - 2168#64 by bv_omega]

end CryptoVerification.SpqrV1.States.FromPb
