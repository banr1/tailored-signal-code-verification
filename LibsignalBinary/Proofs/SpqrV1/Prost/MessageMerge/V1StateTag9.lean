/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Tag Arm 9 (`EkReceivedCt1Sampled`) for `V1State::merge` (`0x4e7e8`)

Verifies 23-word (`184` B) relocation and symbolic execution of tag arm 9 (`EkReceivedCt1Sampled`,
entry `+748`, fresh-init `+1944`) to `entry + 2700#64` (`0x4f274`), both at fixed offset and under
`[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop hiding cap_add_one_beq_zero_false
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTableExpanded optProtoInnerStateJumpTableAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

/-! ## 1. 23-Word (`184`B) Relocation & Stack Helpers for Tag 9 (`EkReceivedCt1Sampled`) -/

def v1Tag9_words23At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64) : SepProp :=
  words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
    words7At (a + 128#64) w16 w17 w18 w19 w20 w21 w22

def v1Tag9_capHeap (A : RustAlloc) (bsLen : Nat)
    (ek : V1State.Chunked.EkReceivedCt1Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64) : SepProp :=
  optUnchunked5CapHeap A bsLen (ek.uc.map fun u => (u.epoch, u.auth, u.es, u.ek, u.ct1))
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
    optPolyEncoderHeap A ek.sendingCt1 w16 w17 w18 w19 w20 w21 w22

theorem v1Tag9_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (ek : V1State.Chunked.EkReceivedCt1Sampled) :
    chunkedEkReceivedCt1SampledPBCapAt A a bsLen ek ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64,
      ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
      ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
        v1Tag9_words23At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        v1Tag9_capHeap A bsLen ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 := by
  dsimp only [chunkedEkReceivedCt1SampledPBCapAt]
  rw [optCt1SentEkReceivedPBCapAt_eq_optUnchunked5]
  refine Entails.trans (sepConj_mono
    (optUnchunked5CapAt_extract_words A a bsLen (ek.uc.map fun u => (u.epoch, u.auth, u.es, u.ek, u.ct1)))
    (optPolynomialEncoderPBAt_extract_words A (a + 128#64) ek.sendingCt1)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w16 => ProofLib.Entails.sepExists_elim fun w17 =>
    ProofLib.Entails.sepExists_elim fun w18 => ProofLib.Entails.sepExists_elim fun w19 =>
    ProofLib.Entails.sepExists_elim fun w20 => ProofLib.Entails.sepExists_elim fun w21 =>
    ProofLib.Entails.sepExists_elim fun w22 => ProofLib.Entails.sepExists_elim fun w0 =>
    ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 =>
    ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
    ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w6 =>
    ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w8 =>
    ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w10 =>
    ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w12 =>
    ProofLib.Entails.sepExists_elim fun w13 => ProofLib.Entails.sepExists_elim fun w14 =>
    ProofLib.Entails.sepExists_elim fun w15 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  refine Entails.trans ?_ (Entails.sepExists_intro w14); refine Entails.trans ?_ (Entails.sepExists_intro w15)
  refine Entails.trans ?_ (Entails.sepExists_intro w16); refine Entails.trans ?_ (Entails.sepExists_intro w17)
  refine Entails.trans ?_ (Entails.sepExists_intro w18); refine Entails.trans ?_ (Entails.sepExists_intro w19)
  refine Entails.trans ?_ (Entails.sepExists_intro w20); refine Entails.trans ?_ (Entails.sepExists_intro w21)
  refine Entails.trans ?_ (Entails.sepExists_intro w22)
  dsimp only [v1Tag9_words23At, v1Tag9_capHeap]; exact Entails.of_eq (by ac_rfl)

theorem v1Tag9_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (ek : V1State.Chunked.EkReceivedCt1Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64) :
    v1Tag9_words23At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      v1Tag9_capHeap A bsLen ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ⊢
      chunkedEkReceivedCt1SampledPBCapAt A a bsLen ek := by
  dsimp only [chunkedEkReceivedCt1SampledPBCapAt, v1Tag9_words23At, v1Tag9_capHeap]
  rw [optCt1SentEkReceivedPBCapAt_eq_optUnchunked5]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono
      (optUnchunked5CapAt_of_words A a bsLen (ek.uc.map fun u => (u.epoch, u.auth, u.es, u.ek, u.ct1))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (optPolynomialEncoderPBAt_of_words A (a + 128#64) ek.sendingCt1 w16 w17 w18 w19 w20 w21 w22))

theorem v1Tag9_chunkedEkReceivedCt1SampledPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (ek : V1State.Chunked.EkReceivedCt1Sampled) :
    chunkedEkReceivedCt1SampledPBAt A a ek ⊢ chunkedEkReceivedCt1SampledPBCapAt A a 0 ek :=
  sepConj_mono_left (optCt1SentEkReceivedPBAt_entails_cap_zero A a ek.uc)

theorem v1Tag9_words_entails_protoChunkedEkReceivedCt1Sampled (A : RustAlloc) (a : BitVec 64)
    (ek : V1State.Chunked.EkReceivedCt1Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64) :
    v1Tag9_words23At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      v1Tag9_capHeap A 0 ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ⊢
      protoChunkedEkReceivedCt1SampledAt A a ek := by
  rw [← chunkedEkReceivedCt1SampledPBAt_eq_proto A a ek]
  exact Entails.trans
    (v1Tag9_of_words A a 0 ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22)
    (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A a 0 ek)

theorem v1Tag9_memRegion_128_eq_words16 (b : BitVec 64) :
    memRegion b 128 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
        words16At b w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 := by
  rw [memRegion_24_step b 104 (by decide), memRegion_104_eq_words13 (b + 24#64)]; dsimp only [words16At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem v1Tag9_memRegion_184_eq_words23 (a : BitVec 64) :
    memRegion a 184 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w22 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64,
      ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64,
        v1Tag9_words23At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 := by
  have s1 := memRegion_split' (b := a) (b' := a + 128#64) (n := 128) (k := 56) (N := 184) rfl (by bv_lin) (by decide)
  rw [s1, v1Tag9_memRegion_128_eq_words16 a]
  simp only [sepExists_sepConj_left]
  rw [memRegion_56_eq_words7 (a + 128#64)]
  simp only [sepExists_sepConj_right]; rfl

theorem v1Tag9_words23At_entails_memRegion_184 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64) :
    v1Tag9_words23At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 ⊢
      memRegion a 184 := by
  rw [v1Tag9_memRegion_184_eq_words23 a]
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w15)
  refine Entails.trans ?_ (Entails.sepExists_intro w14); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w22); refine Entails.trans ?_ (Entails.sepExists_intro w21)
  refine Entails.trans ?_ (Entails.sepExists_intro w20); refine Entails.trans ?_ (Entails.sepExists_intro w19)
  refine Entails.trans ?_ (Entails.sepExists_intro w18); refine Entails.trans ?_ (Entails.sepExists_intro w17)
  refine Entails.trans ?_ (Entails.sepExists_intro w16)
  exact Entails.refl _

theorem v1Tag9_memRegion_224_split_ok (a : BitVec 64) :
    memRegion a 224 =
      ∃∗ vd : BitVec 64,
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w22 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64,
      ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64,
        (a ↦₆₄ vd) ∗
        v1Tag9_words23At (a + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (a + 192#64) 32 := by
  have s1 := memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 216) (N := 224) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 8#64) (b' := a + 192#64) (n := 184) (k := 32) (N := 216) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_eight a, sepExists_sepConj_left, v1Tag9_memRegion_184_eq_words23 (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem v1Tag9_memRegion_split_temp (fsp : BitVec 64) :
    memRegion fsp 720 =
      memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 184 ∗
      memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 240#64) 184 ∗
      (∃∗ w_sp424 : BitVec 64, ((fsp + 424#64) ↦₆₄ w_sp424)) ∗
      memRegion (fsp + 432#64) 48 ∗
      memRegion (fsp + 480#64) 184 ∗
      memRegion (fsp + 664#64) 56 := by
  have s1 := memRegion_split' (b := fsp) (b' := fsp + 16#64) (n := 16) (k := 704) (N := 720) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 200#64) (n := 184) (k := 520) (N := 704) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 200#64) (b' := fsp + 240#64) (n := 40) (k := 480) (N := 520) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 424#64) (n := 184) (k := 296) (N := 480) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := fsp + 424#64) (b' := fsp + 432#64) (n := 8) (k := 288) (N := 296) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := fsp + 432#64) (b' := fsp + 480#64) (n := 48) (k := 240) (N := 288) rfl (by bv_lin) (by decide)
  have s7 := memRegion_split' (b := fsp + 480#64) (b' := fsp + 664#64) (n := 184) (k := 56) (N := 240) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (fsp + 424#64)]

theorem v1Tag9_memRegion_fold_temp (fsp w_sp424 : BitVec 64) :
    memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 184 ∗
      memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 240#64) 184 ∗
      ((fsp + 424#64) ↦₆₄ w_sp424) ∗
      memRegion (fsp + 432#64) 48 ∗
      memRegion (fsp + 480#64) 184 ∗
      memRegion (fsp + 664#64) 56 ⊢
      memRegion fsp 720 := by
  rw [v1Tag9_memRegion_split_temp fsp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (Entails.sepExists_intro w_sp424)))))

theorem v1Tag9_memRegion_184_split_init (fsp : BitVec 64) :
    memRegion (fsp + 16#64) 184 =
      (∃∗ w_sp16 : BitVec 64, ((fsp + 16#64) ↦₆₄ w_sp16)) ∗
      memRegion (fsp + 24#64) 120 ∗
      (∃∗ w_sp144 : BitVec 64, ((fsp + 144#64) ↦₆₄ w_sp144)) ∗
      memRegion (fsp + 152#64) 48 := by
  have s1 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 24#64) (n := 8) (k := 176) (N := 184) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 24#64) (b' := fsp + 144#64) (n := 120) (k := 56) (N := 176) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 144#64) (b' := fsp + 152#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, ProofLib.memRegion_eight (fsp + 16#64), ProofLib.memRegion_eight (fsp + 144#64)]

theorem v1Tag9_reconstruct_innerState (A : RustAlloc) (mPtr : BitVec 64) (bsLen : Nat)
    (ek : V1State.Chunked.EkReceivedCt1Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64) :
    (mPtr ↦₆₄ 0x8000000000000008#64) ∗
      v1Tag9_words23At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      memRegion (mPtr + 192#64) 32 ∗
      v1Tag9_capHeap A bsLen ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ⊢
      optProtoInnerStateCapAt A mPtr bsLen (some (.ekReceivedCt1Sampled ek)) := by
  dsimp only [optProtoInnerStateCapAt, protoInnerStateCapAt]
  refine Entails.trans (Entails.of_eq (show
    (mPtr ↦₆₄ 0x8000000000000008#64) ∗
      v1Tag9_words23At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      memRegion (mPtr + 192#64) 32 ∗
      v1Tag9_capHeap A bsLen ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 =
    (mPtr ↦₆₄ 0x8000000000000008#64) ∗
      (v1Tag9_words23At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 ∗
       v1Tag9_capHeap A bsLen ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22) ∗
      memRegion (mPtr + 192#64) 32 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left
    (v1Tag9_of_words A (mPtr + 8#64) bsLen ek w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22))

/-! ## 2. Stepping Lemmas for Tag 9 (`EkReceivedCt1Sampled`) -/

private theorem v1Tag9_err_uc_2028 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    {s : State} {fsp : BitVec 64} {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2048#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) optUc ∗
        A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc
  v1StateMerge_fetches b H 2028 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢
        memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone128 (by sep_focus); wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (fsp + 240#64) u) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (fsp + 240#64) cap ptr u) (by sep_focus)
    wp_apply
    dsimp only [protoUnchunkedCt1SentEkReceivedSize]
    wp_done

private theorem v1Tag9_err_enc_2048 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2048#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoPolynomialEncoderAt A (fsp + 368#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoPolyEncoderSpec] at hDropEnc
  v1StateMerge_fetches b H 2048 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 48 ⊢
        memRegion (fsp + 368#64) 56 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none',
      show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A (fsp + 368#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A (fsp + 368#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    wp_apply
    dsimp only [protoPolynomialEncoderSize]
    wp_steps; wp_done

private theorem v1Tag9_err_2028 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    {s : State} {fsp : BitVec 64} {ek : V1State.Chunked.EkReceivedCt1Sampled} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (protoChunkedEkReceivedCt1SampledAt A (fsp + 240#64) ek ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 184 ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedEkReceivedCt1SampledAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have hjoin184 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ⊢
      memRegion (fsp + 240#64) 184 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 56) (N := 184)
      rfl (by bv_lin) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) ek.uc ∗
      A.pool ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialEncoderAt A (fsp + 368#64) (ek.sendingCt1.map pbToProtoPolyEncoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [h368, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag9_err_uc_2028 hDropUc hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1, hx25_1⟩
  apply SepWP.weaken_pre hP1
  apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialEncoderAt A (fsp + 368#64) (ek.sendingCt1.map pbToProtoPolyEncoder) ∗
      A.pool ∗ stackAt fsp dropStack48 ∗
      (memRegion (fsp + 240#64) 128 ∗ v1StateBelowRest fsp dropStack48 ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_dropStack48 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag9_err_enc_2048 hDropEnc hsp_align hpc1 hrun1 (hsp1.trans hsp) (hx25_1.trans hx25)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2
  apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin184 (by sep_focus)
  refine SepWP.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hsp2.trans hsp1, htr2.trans htr1, hx21_2.trans hx21_1⟩

private theorem v1Tag9_setup_1944 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp144 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1944#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2f8c#64) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedEkReceivedCt1SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1964#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 48 ⊢
      chunkedEkReceivedCt1SampledPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedEkReceivedCt1SampledPBCapAt A (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedEkReceivedCt1SampledPBCapAt, optCt1SentEkReceivedPBCapAt, optPolynomialEncoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    rw [h24, h144, h152]; exact Entails.of_eq (by ac_rfl)
  v1StateMerge_fetches b H 1944 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag9_copy_ok_1964 {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp424 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3144#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag9_words23At_entails_memRegion_184 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  v1StateMerge_fetches b H 1964 64
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag9_copy_err_1964 {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp424 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2028#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 184 ∗
          v1Tag9_words23At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          ((fsp + 424#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  have hfold16 := v1Tag9_words23At_entails_memRegion_184 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  v1StateMerge_fetches b H 1964 64
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag9_pre_drop_3144 {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3144#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3204#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 480#64) 184 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 184 ∗
          v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag9_words23At_entails_memRegion_184 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15
  apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11
  apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u22; apply SepWP.exists_elim; intro u21
  apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19
  apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17
  apply SepWP.exists_elim; intro u16
  v1StateMerge_fetches b H 3144 60
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag9_post_drop_3204 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hb_align : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (mPtr ↦₆₄ 0x8000000000000008#64) ∗
          v1Tag9_words23At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          memRegion (mPtr + 192#64) 32 ∗
          memRegion (fsp + 480#64) 184 ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag9_words23At_entails_memRegion_184 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  simp only [dropOptProtoInnerStateSpec] at hDropInner
  v1StateMerge_fetches b H 3204 100
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  conv =>
    arg 4
    rw [v1Tag9_memRegion_224_split_ok mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d22; apply SepWP.exists_elim; intro d21
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19
  apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold480 ⊢
  wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done

private theorem v1Tag9_discrFull_other {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .ekReceivedCt1Sampled v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x8000000000000008#64) = true := by
  cases is with
  | ekReceivedCt1Sampled v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

private theorem v1Tag9_inplace {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2f8c#64)
      ((chunkedEkReceivedCt1SampledMergeSpec A).inImage img))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {ek : V1State.Chunked.EkReceivedCt1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 748#64)
    (hcont : V1StateTagCont img b A H s0 x R 9 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, _hb_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000008#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000008#64) = false := by rw [hx9_eq]; decide
  have hpe : OptPolyEncoderBound ek.sendingCt1 rest.length := by
    simpa only [hm_is] using ekReceivedCt1Sampled_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  v1StateMerge_fetches b H 748 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0x2f8c#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, ek, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 788#64) hEkCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedEkReceivedCt1SampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound ek.sendingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedEkReceivedCt1SampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag9 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hek_res : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) ek rest 99).toOption with
  | none =>
    rw [hek_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := entry + 2700#64)
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro ek'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000008#64) ∗
        chunkedEkReceivedCt1SampledPBAt A (x.msgPtr + 8#64) ek' ∗ memRegion (x.msgPtr + 192#64) 32 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedEkReceivedCt1SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ekReceivedCt1Sampled ek'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFrame]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err
  | some p =>
    rcases p with ⟨ek', rest'⟩
    rw [hek_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hek_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekReceivedCt1Sampled ek')) :=
      innerStatePolyBound_of_ekReceivedCt1Sampled hpe hek_res
    refine SepWPp.of_sepWP_img (mid := entry + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ekReceivedCt1Sampled ek') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ekReceivedCt1Sampled ek') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1Tag9_at_1944 {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2f8c#64)
      ((chunkedEkReceivedCt1SampledMergeSpec A).inImage img))
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1944#64)
    (hcont : V1StateTagCont img b A H s0 x R 9 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have hfsp240 : fsp + 240#64 = s0.sp - 576#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest.length :=
    optPolyEncoderBound_none h56
  refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2f8c#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, show s0.sp - 816#64 = fsp from rfl,
      v1Tag9_memRegion_split_temp fsp, v1Tag9_memRegion_184_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp424
  apply SepWP.exists_elim; intro w_sp144
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
        memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesAt b ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1Tag9_setup_1944 (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1964#64) hEkCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedEkReceivedCt1SampledMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpe0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedEkReceivedCt1SampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 9) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ekReceivedCt1Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag9]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ekReceivedCt1Sampled ek => exact absurd h (hm_not ek)
      | _ => rfl
  cases hek_res : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hek_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64)
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro ek'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hek_words : chunkedEkReceivedCt1SampledPBAt A (fsp + 16#64) ek' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64,
        ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
        ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
          v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          v1Tag9_capHeap A 0 ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 :=
      Entails.trans (v1Tag9_chunkedEkReceivedCt1SampledPBAt_entails_cap_zero A (fsp + 16#64) ek')
        (v1Tag9_extract_words A (fsp + 16#64) 0 ek')
    apply SepWP.fold hek_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
    apply SepWP.exists_elim; intro w22
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [← hfsp240] at hx25_m
    let Frame_err : SepProp :=
      v1Tag9_capHeap A 0 ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
      memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_copy_err_1964 hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx25_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (v1Tag9_words_entails_protoChunkedEkReceivedCt1Sampled A (fsp + 240#64) ek'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedEkReceivedCt1SampledAt A (fsp + 240#64) ek' ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
          memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
          memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesAt b ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_err_2028 hDropUc hDropEnc hfsp_align hpc2 hrun2
      (hsp2.trans hspm) (hx25_2.trans hx25_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 ?_
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFrame, fsp]; ac_rfl))
    exact hcont.onErr hm_field s3 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err
  | some p =>
    rcases p with ⟨ek', rest'⟩
    rw [hek_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hek_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekReceivedCt1Sampled ek')) :=
      innerStatePolyBound_of_ekReceivedCt1Sampled hpe0 hek_res
    refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag9_extract_words A (fsp + 16#64) rest'.length ek') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
    apply SepWP.exists_elim; intro w22
    rw [v1StateBelow_dropStack96 fsp]
    rw [← hfsp720] at hfp_m
    dsimp only [v1StateJumpTablesAt]
    let Frame_ok : SepProp :=
      v1Tag9_capHeap A rest'.length ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
      v1StateMergeJumpTableExpanded b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        (memRegion (fsp + 480#64) 184 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_copy_ok_1964 hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 184 ∗ Frame_ok) =
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 480#64) 184 ∗
        (memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1Tag9_pre_drop_3144 hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        (memRegion (fsp + 16#64) 184 ∗ memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
          v1Tag9_capHeap A rest'.length ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
          memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
          v1StateMergeJumpTableExpanded b ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_post_drop_3204 hDropInner hfsp_align hb_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag9_reconstruct_innerState A x.msgPtr rest'.length ek'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ekReceivedCt1Sampled ek') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ekReceivedCt1Sampled ek') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
       hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
       hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans hfsp720⟩
      hinv4

private theorem v1Tag9_branch_1944 {img : Obj.Image} {b : BitVec 64}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 748#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1944#64 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  v1StateMerge_fetches b H 748 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 1944#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ ek, is ≠ .ekReceivedCt1Sampled ek := fun ek h => hm_not ek (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000008#64) = true :=
      v1Tag9_discrFull_other hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag9_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x2f8c#64)
      ((chunkedEkReceivedCt1SampledMergeSpec A).inImage img))
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 748#64)
    (hcont : V1StateTagCont img b A H s0 x R 9 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ ek, m.innerState = some (.ekReceivedCt1Sampled ek)
  · rcases hex with ⟨ek, hm_is⟩
    exact v1Tag9_inplace hEkCall hm_is hentry hpc hcont
  · have hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek) := fun ek h => hex ⟨ek, h⟩
    refine v1Tag9_branch_1944 hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag9_at_1944 hEkCall hDropUc hDropEnc hDropInner hm_not hentry' hpc' hcont

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

private theorem v1Tag9_err_uc_2028_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    {s : State} {fsp : BitVec 64} {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2048#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) optUc ∗
        A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢
        memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone128 (by sep_focus); wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (fsp + 240#64) u) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (fsp + 240#64) cap ptr u) (by sep_focus)
    wp_apply
    dsimp only [protoUnchunkedCt1SentEkReceivedSize]
    wp_done

private theorem v1Tag9_err_enc_2048_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2048#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialEncoderAt A (fsp + 368#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoPolyEncoderSpec] at hDropEnc
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 48 ⊢
        memRegion (fsp + 368#64) 56 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none',
      show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A (fsp + 368#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A (fsp + 368#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    wp_apply
    dsimp only [protoPolynomialEncoderSize]
    wp_steps; wp_done

private theorem v1Tag9_err_2028_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    {s : State} {fsp : BitVec 64} {ek : V1State.Chunked.EkReceivedCt1Sampled} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2028#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedEkReceivedCt1SampledAt A (fsp + 240#64) ek ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 184 ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedEkReceivedCt1SampledAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have hjoin184 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ⊢
      memRegion (fsp + 240#64) 184 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 56) (N := 184)
      rfl (by bv_lin) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) ek.uc ∗
      A.pool ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialEncoderAt A (fsp + 368#64) (ek.sendingCt1.map pbToProtoPolyEncoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [h368, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag9_err_uc_2028_placed hDropUc hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1, hx25_1⟩
  apply SepWP.weaken_pre hP1
  apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialEncoderAt A (fsp + 368#64) (ek.sendingCt1.map pbToProtoPolyEncoder) ∗
      A.pool ∗ stackAt fsp dropStack48 ∗
      (memRegion (fsp + 240#64) 128 ∗ v1StateBelowRest fsp dropStack48 ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_dropStack48 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag9_err_enc_2048_placed hDropEnc hsp_align hpc1 hrun1 (hsp1.trans hsp) (hx25_1.trans hx25)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2
  apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin184 (by sep_focus)
  refine SepWP.done hpc2 hrun2 ⟨Entails.of_eq (by ac_rfl), hsp2.trans hsp1, htr2.trans htr1, hx21_2.trans hx21_1⟩

private theorem v1Tag9_setup_1944_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp144 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1944#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedEkReceivedCt1SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1964#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 48 ⊢
      chunkedEkReceivedCt1SampledPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedEkReceivedCt1SampledPBCapAt A (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedEkReceivedCt1SampledPBCapAt, optCt1SentEkReceivedPBCapAt, optPolynomialEncoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    rw [h24, h144, h152]; exact Entails.of_eq (by ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag9_copy_ok_1964_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp424 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3144#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag9_words23At_entails_memRegion_184 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag9_copy_err_1964_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp424 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1964#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2028#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 184 ∗
          v1Tag9_words23At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          ((fsp + 424#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  have hfold16 := v1Tag9_words23At_entails_memRegion_184 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag9_pre_drop_3144_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3144#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3204#64) s
      (v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 480#64) 184 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 184 ∗
          v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag9_words23At_entails_memRegion_184 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  conv =>
    arg 4
    rw [v1Tag9_memRegion_184_eq_words23 (fsp + 480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15
  apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11
  apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u22; apply SepWP.exists_elim; intro u21
  apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19
  apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17
  apply SepWP.exists_elim; intro u16
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag9_post_drop_3204_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
   
    (hpc : s.pc = (blkPl_298).base + 3204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (mPtr ↦₆₄ 0x8000000000000008#64) ∗
          v1Tag9_words23At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          memRegion (mPtr + 192#64) 32 ∗
          memRegion (fsp + 480#64) 184 ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag9_words23At_entails_memRegion_184 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  conv =>
    arg 4
    rw [v1Tag9_memRegion_224_split_ok mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15
  apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d22; apply SepWP.exists_elim; intro d21
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19
  apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag9_words23At, words16At, words13At, words10At, words7At, words3At] at hfold480 ⊢
  wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done


private theorem v1Tag9_inplace_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {ek : V1State.Chunked.EkReceivedCt1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 748#64)
    (hcont : V1StateTagContPlaced A H s0 x R 9 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000008#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000008#64) = false := by rw [hx9_eq]; decide
  have hpe : OptPolyEncoderBound ek.sendingCt1 rest.length := by
    simpa only [hm_is] using ekReceivedCt1Sampled_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 310) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, ek, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 788#64) hEkCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedEkReceivedCt1SampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound ek.sendingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedEkReceivedCt1SampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag9 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hek_res : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) ek rest 99).toOption with
  | none =>
    rw [hek_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro ek'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000008#64) ∗
        chunkedEkReceivedCt1SampledPBAt A (x.msgPtr + 8#64) ek' ∗ memRegion (x.msgPtr + 192#64) 32 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedEkReceivedCt1SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ekReceivedCt1Sampled ek'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err
  | some p =>
    rcases p with ⟨ek', rest'⟩
    rw [hek_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hek_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekReceivedCt1Sampled ek')) :=
      innerStatePolyBound_of_ekReceivedCt1Sampled hpe hek_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ekReceivedCt1Sampled ek') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ekReceivedCt1Sampled ek') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1Tag9_at_1944_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1944#64)
    (hcont : V1StateTagContPlaced A H s0 x R 9 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have hfsp240 : fsp + 240#64 = s0.sp - 576#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest.length :=
    optPolyEncoderBound_none h56
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 310) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag9_memRegion_split_temp fsp, v1Tag9_memRegion_184_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp424
  apply SepWP.exists_elim; intro w_sp144
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
        memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1Tag9_setup_1944_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1964#64) hEkCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedEkReceivedCt1SampledMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpe0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.EkReceivedCt1Sampled).sendingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedEkReceivedCt1SampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 9) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ekReceivedCt1Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag9]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ekReceivedCt1Sampled ek => exact absurd h (hm_not ek)
      | _ => rfl
  cases hek_res : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hek_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro ek'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hek_words : chunkedEkReceivedCt1SampledPBAt A (fsp + 16#64) ek' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64,
        ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
        ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
          v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          v1Tag9_capHeap A 0 ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 :=
      Entails.trans (v1Tag9_chunkedEkReceivedCt1SampledPBAt_entails_cap_zero A (fsp + 16#64) ek')
        (v1Tag9_extract_words A (fsp + 16#64) 0 ek')
    apply SepWP.fold hek_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
    apply SepWP.exists_elim; intro w22
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [← hfsp240] at hx25_m
    let Frame_err : SepProp :=
      v1Tag9_capHeap A 0 ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
      memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_copy_err_1964_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2, hx25_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (v1Tag9_words_entails_protoChunkedEkReceivedCt1Sampled A (fsp + 240#64) ek'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedEkReceivedCt1SampledAt A (fsp + 240#64) ek' ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
          memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 480#64) 184 ∗
          memRegion (fsp + 664#64) 56 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_err_2028_placed hDropUc hDropEnc hfsp_align hpc2 hrun2
      (hsp2.trans hspm) (hx25_2.trans hx25_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 ?_
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field s3 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err
  | some p =>
    rcases p with ⟨ek', rest'⟩
    rw [hek_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hek_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ekReceivedCt1Sampled ek')) :=
      innerStatePolyBound_of_ekReceivedCt1Sampled hpe0 hek_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedEkReceivedCt1SampledMergeSpec, hek_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag9_extract_words A (fsp + 16#64) rest'.length ek') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21
    apply SepWP.exists_elim; intro w22
    rw [v1StateBelow_dropStack96 fsp]
    rw [← hfsp720] at hfp_m
    dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag9_capHeap A rest'.length ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
      memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ w_sp424) ∗
        (memRegion (fsp + 480#64) 184 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_copy_ok_1964_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 184 ∗ Frame_ok) =
      v1Tag9_words23At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        memRegion (fsp + 480#64) 184 ∗
        (memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1Tag9_pre_drop_3144_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        v1Tag9_words23At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 ∗
        (memRegion (fsp + 16#64) 184 ∗ memRegion (fsp + 240#64) 184 ∗ ((fsp + 424#64) ↦₆₄ x.msgPtr) ∗
          v1Tag9_capHeap A rest'.length ek' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 200#64) 40 ∗
          memRegion (fsp + 432#64) 48 ∗ memRegion (fsp + 664#64) 56 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag9_post_drop_3204_placed hDropInner hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag9_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag9_reconstruct_innerState A x.msgPtr rest'.length ek'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ekReceivedCt1Sampled ek') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ekReceivedCt1Sampled ek') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
       hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
       hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans hfsp720⟩
      hinv4

private theorem v1Tag9_branch_1944_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 748#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1944#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1944#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ ek, is ≠ .ekReceivedCt1Sampled ek := fun ek h => hm_not ek (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000008#64) = true :=
      v1Tag9_discrFull_other hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag9_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEkCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 310)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 748#64)
    (hcont : V1StateTagContPlaced A H s0 x R 9 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ ek, m.innerState = some (.ekReceivedCt1Sampled ek)
  · rcases hex with ⟨ek, hm_is⟩
    exact v1Tag9_inplace_placed hEkCall hm_is hentry hpc hcont
  · have hm_not : ∀ ek, m.innerState ≠ some (.ekReceivedCt1Sampled ek) := fun ek h => hex ⟨ek, h⟩
    refine v1Tag9_branch_1944_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag9_at_1944_placed hEkCall hDropUc hDropEnc hDropInner hm_not hentry' hpc' hcont


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
