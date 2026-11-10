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
# Tag Arms 2–4 (`KeysSampled`, `HeaderSent`, `Ct1Received`) for `V1State::merge` (`0x4e7e8`)

Imports `V1StateTag24` (tag 4 `Ct1Received` and shared 20-word helpers) and `V1StateTag2` (tag 2
`KeysSampled`), and verifies tag arm 3 (`HeaderSent`, entry `+428`, non-inplace `+1044`) to
`entry + 2700#64` (`0x4f274`).
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
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. 22-Word (`176`B) Relocation & Stack Helpers for Tag 3 (`HeaderSent`) -/

def words22At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64) : SepProp :=
  words10At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ∗
    words7At (a + 80#64) w10 w11 w12 w13 w14 w15 w16 ∗
    words5At (a + 136#64) w17 w18 w19 w20 w21

def tag3CapHeap (A : RustAlloc) (bsLen : Nat)
    (hs : V1State.Chunked.HeaderSent)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64) : SepProp :=
  optUnchunked3CapHeap A bsLen (hs.uc.map fun u => (u.epoch, u.auth, u.dk))
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ∗
  optPolyEncoderHeap A hs.sendingEk w10 w11 w12 w13 w14 w15 w16 ∗
  optPolyDecoderHeap A hs.receivingCt1 w17 w18 w19 w20 w21

theorem tag3_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (hs : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBCapAt A a bsLen hs ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
      ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64,
        words22At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        tag3CapHeap A bsLen hs
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 := by
  dsimp only [chunkedHeaderSentPBCapAt]
  rw [optEkSentPBCapAt_eq_optUnchunked3]
  refine Entails.trans (sepConj_mono (optUnchunked3CapAt_extract_words A a bsLen
      (hs.uc.map fun u => (u.epoch, u.auth, u.dk)))
    (sepConj_mono (optPolynomialEncoderPBAt_extract_words A (a + 80#64) hs.sendingEk)
      (optPolynomialDecoderPBAt_extract_words A (a + 136#64) hs.receivingCt1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w17 => ProofLib.Entails.sepExists_elim fun w18 =>
    ProofLib.Entails.sepExists_elim fun w19 => ProofLib.Entails.sepExists_elim fun w20 =>
    ProofLib.Entails.sepExists_elim fun w21 => ProofLib.Entails.sepExists_elim fun w10 =>
    ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w12 =>
    ProofLib.Entails.sepExists_elim fun w13 => ProofLib.Entails.sepExists_elim fun w14 =>
    ProofLib.Entails.sepExists_elim fun w15 => ProofLib.Entails.sepExists_elim fun w16 =>
    ProofLib.Entails.sepExists_elim fun w0 => ProofLib.Entails.sepExists_elim fun w1 =>
    ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w3 =>
    ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w5 =>
    ProofLib.Entails.sepExists_elim fun w6 => ProofLib.Entails.sepExists_elim fun w7 =>
    ProofLib.Entails.sepExists_elim fun w8 => ProofLib.Entails.sepExists_elim fun w9 => ?_
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
  dsimp only [words22At, tag3CapHeap]; exact Entails.of_eq (by ac_rfl)

theorem tag3_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (hs : V1State.Chunked.HeaderSent)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64) :
    words22At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      tag3CapHeap A bsLen hs
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ⊢
      chunkedHeaderSentPBCapAt A a bsLen hs := by
  dsimp only [chunkedHeaderSentPBCapAt, words22At, tag3CapHeap]
  rw [optEkSentPBCapAt_eq_optUnchunked3]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (optUnchunked3CapAt_of_words A a bsLen (hs.uc.map fun u => (u.epoch, u.auth, u.dk))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
      (sepConj_mono (optPolynomialEncoderPBAt_of_words A (a + 80#64) hs.sendingEk w10 w11 w12 w13 w14 w15 w16)
        (optPolynomialDecoderPBAt_of_words A (a + 136#64) hs.receivingCt1 w17 w18 w19 w20 w21)))

theorem chunkedHeaderSentPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBAt A a s ⊢ chunkedHeaderSentPBCapAt A a 0 s :=
  sepConj_mono_left (optEkSentPBAt_entails_cap_zero A a s.uc)

theorem tag3_words_entails_protoChunkedHeaderSent (A : RustAlloc) (a : BitVec 64)
    (hs : V1State.Chunked.HeaderSent)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64) :
    words22At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      tag3CapHeap A 0 hs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ⊢
      protoChunkedHeaderSentAt A a hs := by
  rw [← chunkedHeaderSentPBAt_eq_proto]
  exact Entails.trans (tag3_of_words A a 0 hs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21)
    (chunkedHeaderSentPBCapAt_entails_pb A a 0 hs)

theorem memRegion_40_eq_words5At (b : BitVec 64) :
    memRegion b 40 =
      ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        words5At b w0 w1 w2 w3 w4 := by
  have s1 := memRegion_split' (b := b) (b' := b + 8#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  rw [s1, ProofLib.memRegion_eight b, memRegion_32_eq_words4 b]; dsimp only [words5At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_176_eq_words22 (a : BitVec 64) :
    memRegion a 176 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w17 : BitVec 64,
        words22At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 := by
  have s1 := memRegion_split' (b := a) (b' := a + 80#64) (n := 80) (k := 96) (N := 176) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 80#64) (b' := a + 136#64) (n := 56) (k := 40) (N := 96) rfl (by bv_lin) (by decide)
  rw [s1, s2, memRegion_80_eq_words10 a]
  simp only [sepExists_sepConj_left]
  rw [memRegion_56_eq_words7 (a + 80#64)]
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  rw [memRegion_40_eq_words5At (a + 136#64)]
  simp only [sepExists_sepConj_right]; rfl

theorem words22At_entails_memRegion_176 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64) :
    words22At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ⊢
      memRegion a 176 := by
  rw [memRegion_176_eq_words22 a]
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w16); refine Entails.trans ?_ (Entails.sepExists_intro w15)
  refine Entails.trans ?_ (Entails.sepExists_intro w14); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w21)
  refine Entails.trans ?_ (Entails.sepExists_intro w20); refine Entails.trans ?_ (Entails.sepExists_intro w19)
  refine Entails.trans ?_ (Entails.sepExists_intro w18); refine Entails.trans ?_ (Entails.sepExists_intro w17)
  exact Entails.refl _

theorem memRegion_224_split_tag3_ok (a : BitVec 64) :
    memRegion a 224 =
      ∃∗ vd : BitVec 64,
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w17 : BitVec 64,
        (a ↦₆₄ vd) ∗
        words22At (a + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (a + 184#64) 40 := by
  have s1 := memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 216) (N := 224) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 8#64) (b' := a + 184#64) (n := 176) (k := 40) (N := 216) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_eight a, sepExists_sepConj_left, memRegion_176_eq_words22 (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_split_tag3_temp (fsp : BitVec 64) :
    memRegion fsp 720 =
      memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 176 ∗
      memRegion (fsp + 192#64) 48 ∗
      memRegion (fsp + 240#64) 176 ∗
      (∃∗ w_sp416 : BitVec 64, ((fsp + 416#64) ↦₆₄ w_sp416)) ∗
      memRegion (fsp + 424#64) 56 ∗
      memRegion (fsp + 480#64) 176 ∗
      memRegion (fsp + 656#64) 64 := by
  have s1 := memRegion_split' (b := fsp) (b' := fsp + 16#64) (n := 16) (k := 704) (N := 720) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 192#64) (n := 176) (k := 528) (N := 704) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 192#64) (b' := fsp + 240#64) (n := 48) (k := 480) (N := 528) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 416#64) (n := 176) (k := 304) (N := 480) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := fsp + 416#64) (b' := fsp + 424#64) (n := 8) (k := 296) (N := 304) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := fsp + 424#64) (b' := fsp + 480#64) (n := 56) (k := 240) (N := 296) rfl (by bv_lin) (by decide)
  have s7 := memRegion_split' (b := fsp + 480#64) (b' := fsp + 656#64) (n := 176) (k := 64) (N := 240) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (fsp + 416#64)]

theorem memRegion_fold_tag3_temp (fsp w_sp416 : BitVec 64) :
    memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 176 ∗
      memRegion (fsp + 192#64) 48 ∗
      memRegion (fsp + 240#64) 176 ∗
      ((fsp + 416#64) ↦₆₄ w_sp416) ∗
      memRegion (fsp + 424#64) 56 ∗
      memRegion (fsp + 480#64) 176 ∗
      memRegion (fsp + 656#64) 64 ⊢
      memRegion fsp 720 := by
  rw [memRegion_split_tag3_temp fsp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (Entails.sepExists_intro w_sp416)))))

theorem memRegion_176_split_tag3_init (fsp : BitVec 64) :
    memRegion (fsp + 16#64) 176 =
      (∃∗ w_sp16 : BitVec 64, ((fsp + 16#64) ↦₆₄ w_sp16)) ∗
      memRegion (fsp + 24#64) 72 ∗
      (∃∗ w_sp96 : BitVec 64, ((fsp + 96#64) ↦₆₄ w_sp96)) ∗
      memRegion (fsp + 104#64) 48 ∗
      (∃∗ w_sp152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w_sp152)) ∗
      memRegion (fsp + 160#64) 32 := by
  have s1 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 24#64) (n := 8) (k := 168) (N := 176) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 24#64) (b' := fsp + 96#64) (n := 72) (k := 96) (N := 168) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 96#64) (b' := fsp + 104#64) (n := 8) (k := 88) (N := 96) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := fsp + 104#64) (b' := fsp + 152#64) (n := 48) (k := 40) (N := 88) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := fsp + 152#64) (b' := fsp + 160#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, ProofLib.memRegion_eight (fsp + 16#64),
      ProofLib.memRegion_eight (fsp + 96#64), ProofLib.memRegion_eight (fsp + 152#64)]

theorem tag3_reconstruct_innerState (A : RustAlloc) (mPtr : BitVec 64) (bsLen : Nat)
    (hs : V1State.Chunked.HeaderSent)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64) :
    (mPtr ↦₆₄ 0x8000000000000002#64) ∗
      words22At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      memRegion (mPtr + 184#64) 40 ∗
      tag3CapHeap A bsLen hs
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ⊢
      optProtoInnerStateCapAt A mPtr bsLen (some (.headerSent hs)) := by
  dsimp only [optProtoInnerStateCapAt, protoInnerStateCapAt]
  refine Entails.trans (Entails.of_eq (show
    (mPtr ↦₆₄ 0x8000000000000002#64) ∗
      words22At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      memRegion (mPtr + 184#64) 40 ∗
      tag3CapHeap A bsLen hs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 =
    (mPtr ↦₆₄ 0x8000000000000002#64) ∗
      (words22At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
       tag3CapHeap A bsLen hs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21) ∗
      memRegion (mPtr + 184#64) 40 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left
    (tag3_of_words A (mPtr + 8#64) bsLen hs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21))

/-! ## 2. Stepping Lemmas for Tag 3 (`HeaderSent`, `+1044..+1136`, `+2380..+2504`, `+3124..+3140`) -/

theorem v1State_tag3_err_1128 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropHs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe29c#64)
      (dropProtoChunkedHeaderSentSpec A))
    {s : State} {fsp : BitVec 64} {hs : V1State.Chunked.HeaderSent} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (protoChunkedHeaderSentAt A (fsp + 240#64) hs ∗
        A.pool ∗ stackAt fsp dropStack96 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 176 ∗ A.pool ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoChunkedHeaderSentSpec] at hDropHs
  v1StateMerge_fetches b H 1128 12
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply
  dsimp only [protoChunkedHeaderSentSize]
  wp_steps; wp_done

theorem v1State_tag3_setup {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp96 w_sp152 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x15c8#64) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
        ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 48 ∗
        ((fsp + 152#64) ↦₆₄ w_sp152) ∗ memRegion (fsp + 160#64) 32 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedHeaderSentPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1068#64 ∧
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
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 160#64) 32 ⊢
      chunkedHeaderSentPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedHeaderSentPBCapAt A (fsp + 16#64) restLen ⟨none, none, none⟩
    dsimp only [chunkedHeaderSentPBCapAt, optEkSentPBCapAt, optPolynomialEncoderPBAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h96 : (fsp + 16#64) + 80#64 = fsp + 96#64 := by bv_lin
    have h104 : (fsp + 96#64) + 8#64 = fsp + 104#64 := by bv_lin
    have h152 : (fsp + 16#64) + 136#64 = fsp + 152#64 := by bv_lin
    have h160 : (fsp + 152#64) + 8#64 = fsp + 160#64 := by bv_lin
    rw [h24, h96, h104, h152, h160]; exact Entails.of_eq (by ac_rfl)
  v1StateMerge_fetches b H 1044 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

theorem v1State_tag3_copy_ok {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp416 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1068#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2380#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ mPtr) ∗ Frame) ∧
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
  have hfold240 := words22At_entails_memRegion_176 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  conv =>
    arg 4
    rw [memRegion_176_eq_words22 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  v1StateMerge_fetches b H 1068 60
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

theorem v1State_tag3_copy_err {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp416 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1068#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1128#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 176 ∗
          words22At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          ((fsp + 416#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := words22At_entails_memRegion_176 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  conv =>
    arg 4
    rw [memRegion_176_eq_words22 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  v1StateMerge_fetches b H 1068 60
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

theorem v1State_tag3_pre_drop {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2380#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2432#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 480#64) 176 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 176 ∗
          words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗ Frame) ∧
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
  have hfold16 := words22At_entails_memRegion_176 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  rw [memRegion_176_eq_words22 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  v1StateMerge_fetches b H 2380 52
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag3_post_drop {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true) (hb_align : b &&& 4095#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2432#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 480#64) 176 ∗
          (mPtr ↦₆₄ 0x8000000000000002#64) ∗
          words22At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (mPtr + 184#64) 40 ∗
          A.pool ∗ optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗ Frame) ∧
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
  have hfold480 := words22At_entails_memRegion_176 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  simp only [dropOptProtoInnerStateSpec] at hDropInner
  v1StateMerge_fetches b H 2432 76
  v1StateMerge_fetches b H 3124 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag3_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done

/-! ## 3. Tag 3 (`HeaderSent`, `tag = 3`, entry `+428`, non-inplace `+1044`) -/

theorem discrFull_other_tag3 {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .headerSent v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x8000000000000002#64) = true := by
  cases is with
  | headerSent v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

theorem v1State_tag3_inplace {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hHsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x15c8#64)
      ((chunkedHeaderSentMergeSpec A).inImage img))
    {s0 : State} {x : V1StateMergeGhost} {R : SepProp}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat} {s : State}
    (hs : V1State.Chunked.HeaderSent)
    (hm_is : m.innerState = some (.headerSent hs))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 428#64)
    (hcont : V1StateTagCont img b A H s0 x R 3 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000002#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000002#64) = false := by
    rw [hx9_eq]; decide
  have hhs_bound : OptPolyEncoderBound hs.sendingEk rest.length ∧ OptPolyDecoderBound hs.receivingCt1 rest.length := by
    simpa only [hm_is] using headerSent_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  v1StateMerge_fetches b H 428 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0x15c8#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, hs, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 468#64) hHsCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedHeaderSentMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hhs_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyEncoderBound hs.sendingEk rest.length ∧ OptPolyDecoderBound hs.receivingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedHeaderSentMergeSpec] at hpan; exact allowPanic_frame' htr hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm] at hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m
  rw [hsp] at hspm
  rw [hx19] at hx19_m; rw [hx20] at hx20_m; rw [hx22] at hx22_m; rw [hx23] at hx23_m
  rw [hx24] at hx24_m; rw [hx25] at hx25_m; rw [hx26] at hx26_m; rw [hx27] at hx27_m
  rw [hx28] at hx28_m; rw [hx29] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) hs rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.headerSent v') }, rest')) := by
    rw [v1State_mergeField_tag3, hm_is]
  cases hhs_res : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) hs rest 99).toOption with
  | none =>
    rw [hhs_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := entry + 2700#64)
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro hs'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000002#64) ∗
        chunkedHeaderSentPBAt A (x.msgPtr + 8#64) hs' ∗ memRegion (x.msgPtr + 184#64) 40 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      refine Entails.trans ?_ (Entails.sepExists_intro (some (.headerSent hs')))
      dsimp only [optProtoInnerStateAt, protoInnerStateAt]
      rw [← chunkedHeaderSentPBAt_eq_proto]; exact Entails.refl _
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
    rcases p with ⟨hs', rest'⟩
    rw [hhs_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hhs_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.headerSent hs')) :=
      innerStatePolyBound_of_headerSent hhs_bound hhs_res
    refine SepWPp.of_sepWP_img (mid := entry + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_f
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.headerSent hs') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.headerSent hs') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_f

theorem v1State_tag3_at_1044 {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hHsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x15c8#64)
      ((chunkedHeaderSentMergeSpec A).inImage img))
    (hDropHs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe29c#64)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropIs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 : State} {x : V1StateMergeGhost} {R : SepProp}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat} {s : State}
    (hm_not : ∀ hs, m.innerState ≠ some (.headerSent hs))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1044#64)
    (hcont : V1StateTagCont img b A H s0 x R 3 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x15c8#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag3_temp fsp, memRegion_176_split_tag3_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp416
  apply SepWP.exists_elim; intro w_sp152
  apply SepWP.exists_elim; intro w_sp96
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ w_sp152) ∗ memRegion (fsp + 160#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗
        memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
        memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesAt b ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag3_setup (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
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
    (ret_pc := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1068#64) hHsCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedHeaderSentMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, optPolyEncoderBound_none h56, optPolyDecoderBound_none h56⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.HeaderSent).sendingEk rest.length ∧
        OptPolyDecoderBound (default : V1State.Chunked.HeaderSent).receivingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedHeaderSentMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.headerSent v') }, rest')) := by
    rw [v1State_mergeField_tag3]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | headerSent hs => exact absurd h (hm_not hs)
      | _ => rfl
  cases hhs_res : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hhs_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64)
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro hs'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (chunkedHeaderSentPBAt_entails_cap_zero A (fsp + 16#64) hs')
      (tag3_extract_words A (fsp + 16#64) 0 hs')) (by sep_focus)
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
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag3CapHeap A 0 hs'
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      A.pool ∗ stackAt fsp dropStack96 ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
      memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
      memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_copy_err hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (tag3_words_entails_protoChunkedHeaderSent A (fsp + 240#64) hs'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedHeaderSentAt A (fsp + 240#64) hs' ∗
        A.pool ∗ stackAt fsp dropStack96 ∗
        (memRegion (fsp + 16#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
          memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
          memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesAt b ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_err_1128 hDropHs hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag3_temp fsp x.msgPtr) (by sep_focus)
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
    rcases p with ⟨hs', rest'⟩
    rw [hhs_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hhs_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.headerSent hs')) :=
      innerStatePolyBound_of_headerSent (bs := rest) (m := default)
        ⟨optPolyEncoderBound_none h56, optPolyDecoderBound_none h56⟩ hhs_res
    refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (tag3_extract_words A (fsp + 16#64) rest'.length hs') (by sep_focus)
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
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag3CapHeap A rest'.length hs'
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
      memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 656#64) 64 ∗
      v1StateMergeJumpTableExpanded b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗
        (memRegion (fsp + 480#64) 176 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesAt, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_copy_ok hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2,
      hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    rw [hspm] at hsp2; rw [hx19_m] at hx19_2
    rw [hx22_m] at hx22_2; rw [hx23_m] at hx23_2; rw [hx24_m] at hx24_2
    rw [hx25_m] at hx25_2; rw [hx26_m] at hx26_2; rw [hx27_m] at hx27_2
    rw [hx28_m] at hx28_2; rw [hfp_m] at hx29_2
    apply SepWP.weaken_pre hP2
    refine SepWP.weaken_pre (P' :=
      words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 480#64) 176 ∗
        (memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗ Frame_ok))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_pre_drop hfsp_align hpc2 hrun2 hsp2 hx20_2 hx29_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3,
      hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    rw [hsp2] at hsp3; rw [hx19_2] at hx19_3
    rw [hx21_2] at hx21_3; rw [hx22_2] at hx22_3; rw [hx23_2] at hx23_3
    rw [hx24_2] at hx24_3; rw [hx25_2] at hx25_3; rw [hx26_2] at hx26_3
    rw [hx27_2] at hx27_3; rw [hx28_2] at hx28_3
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
        optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
        words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        (tag3CapHeap A rest'.length hs'
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (fsp + 16#64) 176 ∗ memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
          memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 656#64) 64 ∗
          v1StateMergeJumpTableExpanded b ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_post_drop hDropIs hfsp_align hb_align hpc3 hrun3 hsp3 hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4,
      hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    rw [hsp3] at hsp4; rw [hx19_3] at hx19_4
    rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4; rw [hx23_3] at hx23_4
    rw [hx24_3] at hx24_4; rw [hx25_3] at hx25_4; rw [hx26_3] at hx26_4
    rw [hx27_3] at hx27_4; rw [hx28_3] at hx28_4; rw [hfsp720] at hx29_4
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (tag3_reconstruct_innerState A x.msgPtr rest'.length hs'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21) (by sep_focus)
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag3_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc4 hrun4 ?_; intro hinv_4
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.headerSent hs') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.headerSent hs') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 hsp4
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      hx21_4
      ⟨hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩ hinv_4

private theorem v1State_tag3_branch_1044 {img : Obj.Image} {b : BitVec 64}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ hs, m.innerState ≠ some (.headerSent hs))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 428#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1044#64 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  v1StateMerge_fetches b H 428 28
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 1044#64) hinv ?_
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
    have hne : ∀ hs, is ≠ .headerSent hs := fun hs h => hm_not hs (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000002#64) = true :=
      discrFull_other_tag3 hne hx9_s
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

theorem v1State_tag3_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hHsCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x15c8#64)
      ((chunkedHeaderSentMergeSpec A).inImage img))
    (hDropHs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe29c#64)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropIs : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 : State} {x : V1StateMergeGhost} {R : SepProp}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat} {s : State}
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 428#64)
    (hcont : V1StateTagCont img b A H s0 x R 3 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ hs, m.innerState = some (.headerSent hs)
  · rcases hex with ⟨hs, hm_is⟩
    exact v1State_tag3_inplace hHsCall hs hm_is hentry hpc hcont
  · have hm_not : ∀ hs, m.innerState ≠ some (.headerSent hs) := fun hs h => hex ⟨hs, h⟩
    refine v1State_tag3_branch_1044 hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag3_at_1044 hHsCall hDropHs hDropIs hm_not hentry' hpc' hcont

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

theorem v1State_tag3_err_1128_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (dropProtoChunkedHeaderSentSpec A))
    {s : State} {fsp : BitVec 64} {hs : V1State.Chunked.HeaderSent} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedHeaderSentAt A (fsp + 240#64) hs ∗
        A.pool ∗ stackAt fsp dropStack96 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 176 ∗ A.pool ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoChunkedHeaderSentSpec] at hDropHs
  wp_steps; wp_apply
  dsimp only [protoChunkedHeaderSentSize]
  wp_steps; wp_done

theorem v1State_tag3_setup_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp96 w_sp152 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
        ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 48 ∗
        ((fsp + 152#64) ↦₆₄ w_sp152) ∗ memRegion (fsp + 160#64) 32 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedHeaderSentPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1068#64 ∧
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
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 160#64) 32 ⊢
      chunkedHeaderSentPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedHeaderSentPBCapAt A (fsp + 16#64) restLen ⟨none, none, none⟩
    dsimp only [chunkedHeaderSentPBCapAt, optEkSentPBCapAt, optPolynomialEncoderPBAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h96 : (fsp + 16#64) + 80#64 = fsp + 96#64 := by bv_lin
    have h104 : (fsp + 96#64) + 8#64 = fsp + 104#64 := by bv_lin
    have h152 : (fsp + 16#64) + 136#64 = fsp + 152#64 := by bv_lin
    have h160 : (fsp + 152#64) + 8#64 = fsp + 160#64 := by bv_lin
    rw [h24, h96, h104, h152, h160]; exact Entails.of_eq (by ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

theorem v1State_tag3_copy_ok_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp416 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1068#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2380#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ mPtr) ∗ Frame) ∧
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
  have hfold240 := words22At_entails_memRegion_176 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  conv =>
    arg 4
    rw [memRegion_176_eq_words22 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

theorem v1State_tag3_copy_err_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp416 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1068#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1128#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 176 ∗
          words22At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          ((fsp + 416#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := words22At_entails_memRegion_176 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  conv =>
    arg 4
    rw [memRegion_176_eq_words22 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

theorem v1State_tag3_pre_drop_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2380#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2432#64) s
      (words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 480#64) 176 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 176 ∗
          words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗ Frame) ∧
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
  have hfold16 := words22At_entails_memRegion_176 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  rw [memRegion_176_eq_words22 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag3_post_drop_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2432#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 480#64) 176 ∗
          (mPtr ↦₆₄ 0x8000000000000002#64) ∗
          words22At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (mPtr + 184#64) 40 ∗
          A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
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
  have hfold480 := words22At_entails_memRegion_176 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag3_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  dsimp only [words22At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done


theorem v1State_tag3_inplace_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A)))
    {s0 : State} {x : V1StateMergeGhost} {R : SepProp}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat} {s : State}
    (hs : V1State.Chunked.HeaderSent)
    (hm_is : m.innerState = some (.headerSent hs))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 428#64)
    (hcont : V1StateTagContPlaced A H s0 x R 3 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000002#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000002#64) = false := by
    rw [hx9_eq]; decide
  have hhs_bound : OptPolyEncoderBound hs.sendingEk rest.length ∧ OptPolyDecoderBound hs.receivingCt1 rest.length := by
    simpa only [hm_is] using headerSent_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 302) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, hs, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 468#64) hHsCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedHeaderSentMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hhs_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyEncoderBound hs.sendingEk rest.length ∧ OptPolyDecoderBound hs.receivingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedHeaderSentMergeSpec] at hpan; exact allowPanic_frame' htr hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm] at hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m
  rw [hsp] at hspm
  rw [hx19] at hx19_m; rw [hx20] at hx20_m; rw [hx22] at hx22_m; rw [hx23] at hx23_m
  rw [hx24] at hx24_m; rw [hx25] at hx25_m; rw [hx26] at hx26_m; rw [hx27] at hx27_m
  rw [hx28] at hx28_m; rw [hx29] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) hs rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.headerSent v') }, rest')) := by
    rw [v1State_mergeField_tag3, hm_is]
  cases hhs_res : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) hs rest 99).toOption with
  | none =>
    rw [hhs_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro hs'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000002#64) ∗
        chunkedHeaderSentPBAt A (x.msgPtr + 8#64) hs' ∗ memRegion (x.msgPtr + 184#64) 40 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      refine Entails.trans ?_ (Entails.sepExists_intro (some (.headerSent hs')))
      dsimp only [optProtoInnerStateAt, protoInnerStateAt]
      rw [← chunkedHeaderSentPBAt_eq_proto]; exact Entails.refl _
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
    rcases p with ⟨hs', rest'⟩
    rw [hhs_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hhs_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.headerSent hs')) :=
      innerStatePolyBound_of_headerSent hhs_bound hhs_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_f
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.headerSent hs') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.headerSent hs') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_f

theorem v1State_tag3_at_1044_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A)))
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropIs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 : State} {x : V1StateMergeGhost} {R : SepProp}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat} {s : State}
    (hm_not : ∀ hs, m.innerState ≠ some (.headerSent hs))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1044#64)
    (hcont : V1StateTagContPlaced A H s0 x R 3 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 302) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag3_temp fsp, memRegion_176_split_tag3_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp416
  apply SepWP.exists_elim; intro w_sp152
  apply SepWP.exists_elim; intro w_sp96
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 72 ∗
      ((fsp + 96#64) ↦₆₄ w_sp96) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ w_sp152) ∗ memRegion (fsp + 160#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗
        memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
        memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag3_setup_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
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
    (ret_pc := (blkPl_298).base + 1068#64) hHsCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedHeaderSentMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, optPolyEncoderBound_none h56, optPolyDecoderBound_none h56⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.HeaderSent).sendingEk rest.length ∧
        OptPolyDecoderBound (default : V1State.Chunked.HeaderSent).receivingCt1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedHeaderSentMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.headerSent v') }, rest')) := by
    rw [v1State_mergeField_tag3]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | headerSent hs => exact absurd h (hm_not hs)
      | _ => rfl
  cases hhs_res : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hhs_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro hs'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (Entails.trans (chunkedHeaderSentPBAt_entails_cap_zero A (fsp + 16#64) hs')
      (tag3_extract_words A (fsp + 16#64) 0 hs')) (by sep_focus)
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
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag3CapHeap A 0 hs'
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      A.pool ∗ stackAt fsp dropStack96 ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
      memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
      memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_copy_err_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (tag3_words_entails_protoChunkedHeaderSent A (fsp + 240#64) hs'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedHeaderSentAt A (fsp + 240#64) hs' ∗
        A.pool ∗ stackAt fsp dropStack96 ∗
        (memRegion (fsp + 16#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
          memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 480#64) 176 ∗
          memRegion (fsp + 656#64) 64 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_err_1128_placed hDropHs hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag3_temp fsp x.msgPtr) (by sep_focus)
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
    rcases p with ⟨hs', rest'⟩
    rw [hhs_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hhs_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.headerSent hs')) :=
      innerStatePolyBound_of_headerSent (bs := rest) (m := default)
        ⟨optPolyEncoderBound_none h56, optPolyDecoderBound_none h56⟩ hhs_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedHeaderSentMergeSpec, hhs_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (tag3_extract_words A (fsp + 16#64) rest'.length hs') (by sep_focus)
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
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag3CapHeap A rest'.length hs'
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
      memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 656#64) 64 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ w_sp416) ∗
        (memRegion (fsp + 480#64) 176 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_copy_ok_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2,
      hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    rw [hspm] at hsp2; rw [hx19_m] at hx19_2
    rw [hx22_m] at hx22_2; rw [hx23_m] at hx23_2; rw [hx24_m] at hx24_2
    rw [hx25_m] at hx25_2; rw [hx26_m] at hx26_2; rw [hx27_m] at hx27_2
    rw [hx28_m] at hx28_2; rw [hfp_m] at hx29_2
    apply SepWP.weaken_pre hP2
    refine SepWP.weaken_pre (P' :=
      words22At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        memRegion (fsp + 480#64) 176 ∗
        (memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗ Frame_ok))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_pre_drop_placed hfsp_align hpc2 hrun2 hsp2 hx20_2 hx29_2) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3,
      hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    rw [hsp2] at hsp3; rw [hx19_2] at hx19_3
    rw [hx21_2] at hx21_3; rw [hx22_2] at hx22_3; rw [hx23_2] at hx23_3
    rw [hx24_2] at hx24_3; rw [hx25_2] at hx25_3; rw [hx26_2] at hx26_3
    rw [hx27_2] at hx27_3; rw [hx28_2] at hx28_3
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        words22At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
        (tag3CapHeap A rest'.length hs'
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 ∗
          memRegion (fsp + 16#64) 176 ∗ memRegion (fsp + 240#64) 176 ∗ ((fsp + 416#64) ↦₆₄ x.msgPtr) ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 192#64) 48 ∗
          memRegion (fsp + 424#64) 56 ∗ memRegion (fsp + 656#64) 64 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag3_post_drop_placed hDropIs hfsp_align hpc3 hrun3 hsp3 hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4,
      hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    rw [hsp3] at hsp4; rw [hx19_3] at hx19_4
    rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4; rw [hx23_3] at hx23_4
    rw [hx24_3] at hx24_4; rw [hx25_3] at hx25_4; rw [hx26_3] at hx26_4
    rw [hx27_3] at hx27_4; rw [hx28_3] at hx28_4; rw [hfsp720] at hx29_4
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (tag3_reconstruct_innerState A x.msgPtr rest'.length hs'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21) (by sep_focus)
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag3_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc4 hrun4 ?_; intro hinv_4
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.headerSent hs') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.headerSent hs') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 hsp4
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      hx21_4
      ⟨hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩ hinv_4

private theorem v1State_tag3_branch_1044_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ hs, m.innerState ≠ some (.headerSent hs))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 428#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1044#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1044#64) hinv ?_
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
    have hne : ∀ hs, is ≠ .headerSent hs := fun hs h => hm_not hs (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000002#64) = true :=
      discrFull_other_tag3 hne hx9_s
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

theorem v1State_tag3_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hHsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 302)
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A)))
    (hDropHs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 281)
      (dropProtoChunkedHeaderSentSpec A))
    (hDropIs : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 : State} {x : V1StateMergeGhost} {R : SepProp}
    {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat} {s : State}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 428#64)
    (hcont : V1StateTagContPlaced A H s0 x R 3 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ hs, m.innerState = some (.headerSent hs)
  · rcases hex with ⟨hs, hm_is⟩
    exact v1State_tag3_inplace_placed hHsCall hs hm_is hentry hpc hcont
  · have hm_not : ∀ hs, m.innerState ≠ some (.headerSent hs) := fun hs h => hex ⟨hs, h⟩
    refine v1State_tag3_branch_1044_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag3_at_1044_placed hHsCall hDropHs hDropIs hm_not hentry' hpc' hcont


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
