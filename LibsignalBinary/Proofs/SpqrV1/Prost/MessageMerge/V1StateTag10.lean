/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag7
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Tag Arm 10 (`Ct1Acknowledged`) for `V1State::merge` (`0x4e7e8`)

Verifies tag arm 10 (`Ct1Acknowledged`, entry `+380`, fresh-init `+880`) from its jump-table entry
to the shared loop latch at `entry + 2700#64` (`0x4f274`), both at fixed offset and under
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

/-! ## 1. 21-Word (`168`B) Relocation & Stack Helpers for Tag 10 (`Ct1Acknowledged`) -/

def v1Tag10_words21At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64) : SepProp :=
  words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
    words5At (a + 128#64) w16 w17 w18 w19 w20

def v1Tag10_capHeap (A : RustAlloc) (bsLen : Nat)
    (ca : V1State.Chunked.Ct1Acknowledged)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64) : SepProp :=
  optUnchunked5CapHeap A bsLen (ca.uc.map fun u => (u.epoch, u.auth, u.hdr, u.es, u.ct1))
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
    optPolyDecoderHeap A ca.receivingEk w16 w17 w18 w19 w20

theorem v1Tag10_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (ca : V1State.Chunked.Ct1Acknowledged) :
    chunkedCt1AcknowledgedPBCapAt A a bsLen ca ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64,
      ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
      ∃∗ w20 : BitVec 64,
        v1Tag10_words21At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        v1Tag10_capHeap A bsLen ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 := by
  dsimp only [chunkedCt1AcknowledgedPBCapAt]
  rw [optUnchunkedCt1SentPBCapAt_eq_optUnchunked5]
  refine Entails.trans (sepConj_mono
    (optUnchunked5CapAt_extract_words A a bsLen (ca.uc.map fun u => (u.epoch, u.auth, u.hdr, u.es, u.ct1)))
    (optPolynomialDecoderPBAt_extract_words A (a + 128#64) ca.receivingEk)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w16 => ProofLib.Entails.sepExists_elim fun w17 =>
    ProofLib.Entails.sepExists_elim fun w18 => ProofLib.Entails.sepExists_elim fun w19 =>
    ProofLib.Entails.sepExists_elim fun w20 => ProofLib.Entails.sepExists_elim fun w0 =>
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
  refine Entails.trans ?_ (Entails.sepExists_intro w20)
  dsimp only [v1Tag10_words21At, v1Tag10_capHeap]; exact Entails.of_eq (by ac_rfl)

theorem v1Tag10_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (ca : V1State.Chunked.Ct1Acknowledged)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64) :
    v1Tag10_words21At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      v1Tag10_capHeap A bsLen ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ⊢
      chunkedCt1AcknowledgedPBCapAt A a bsLen ca := by
  dsimp only [chunkedCt1AcknowledgedPBCapAt, v1Tag10_words21At, v1Tag10_capHeap]
  rw [optUnchunkedCt1SentPBCapAt_eq_optUnchunked5]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono
      (optUnchunked5CapAt_of_words A a bsLen (ca.uc.map fun u => (u.epoch, u.auth, u.hdr, u.es, u.ct1))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)
      (optPolynomialDecoderPBAt_of_words A (a + 128#64) ca.receivingEk w16 w17 w18 w19 w20))

theorem v1Tag10_chunkedCt1AcknowledgedPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (ca : V1State.Chunked.Ct1Acknowledged) :
    chunkedCt1AcknowledgedPBAt A a ca ⊢ chunkedCt1AcknowledgedPBCapAt A a 0 ca :=
  sepConj_mono_left (optCt1SentPBAt_entails_cap_zero A a ca.uc)

theorem v1Tag10_words_entails_protoChunkedCt1Acknowledged (A : RustAlloc) (a : BitVec 64)
    (ca : V1State.Chunked.Ct1Acknowledged)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64) :
    v1Tag10_words21At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      v1Tag10_capHeap A 0 ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ⊢
      protoChunkedCt1AcknowledgedAt A a ca := by
  rw [← chunkedCt1AcknowledgedPBAt_eq_proto A a ca]
  exact Entails.trans
    (v1Tag10_of_words A a 0 ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20)
    (chunkedCt1AcknowledgedPBCapAt_entails_pb A a 0 ca)

theorem v1Tag10_memRegion_168_eq_words21 (a : BitVec 64) :
    memRegion a 168 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
      ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64,
        v1Tag10_words21At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 := by
  have s1 := memRegion_split' (b := a) (b' := a + 128#64) (n := 128) (k := 40) (N := 168) rfl (by bv_lin) (by decide)
  have s128 : memRegion a 128 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
        words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 := by
    rw [memRegion_24_step a 104 (by decide), memRegion_104_eq_words13 (a + 24#64)]; dsimp only [words16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [s1, s128]
  simp only [sepExists_sepConj_left]
  rw [v1Tag7_memRegion_40_eq_words5 (a + 128#64)]
  simp only [sepExists_sepConj_right]; rfl

theorem v1Tag10_words21At_entails_memRegion_168 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64) :
    v1Tag10_words21At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 ⊢
      memRegion a 168 := by
  rw [v1Tag10_memRegion_168_eq_words21 a]
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w15)
  refine Entails.trans ?_ (Entails.sepExists_intro w14); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w20); refine Entails.trans ?_ (Entails.sepExists_intro w19)
  refine Entails.trans ?_ (Entails.sepExists_intro w18); refine Entails.trans ?_ (Entails.sepExists_intro w17)
  refine Entails.trans ?_ (Entails.sepExists_intro w16)
  exact Entails.refl _

theorem v1Tag10_memRegion_224_split_ok (a : BitVec 64) :
    memRegion a 224 =
      ∃∗ vd : BitVec 64,
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
      ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64,
        (a ↦₆₄ vd) ∗
        v1Tag10_words21At (a + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (a + 176#64) 48 := by
  have s1 := memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 216) (N := 224) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 8#64) (b' := a + 176#64) (n := 168) (k := 48) (N := 216) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_eight a, sepExists_sepConj_left, v1Tag10_memRegion_168_eq_words21 (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem v1Tag10_memRegion_split_temp (fsp : BitVec 64) :
    memRegion fsp 720 =
      memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 168 ∗
      memRegion (fsp + 184#64) 56 ∗
      memRegion (fsp + 240#64) 168 ∗
      (∃∗ w_sp408 : BitVec 64, ((fsp + 408#64) ↦₆₄ w_sp408)) ∗
      memRegion (fsp + 416#64) 64 ∗
      memRegion (fsp + 480#64) 168 ∗
      memRegion (fsp + 648#64) 72 := by
  have s1 := memRegion_split' (b := fsp) (b' := fsp + 16#64) (n := 16) (k := 704) (N := 720) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 184#64) (n := 168) (k := 536) (N := 704) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 184#64) (b' := fsp + 240#64) (n := 56) (k := 480) (N := 536) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 408#64) (n := 168) (k := 312) (N := 480) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := fsp + 408#64) (b' := fsp + 416#64) (n := 8) (k := 304) (N := 312) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := fsp + 416#64) (b' := fsp + 480#64) (n := 64) (k := 240) (N := 304) rfl (by bv_lin) (by decide)
  have s7 := memRegion_split' (b := fsp + 480#64) (b' := fsp + 648#64) (n := 168) (k := 72) (N := 240) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (fsp + 408#64)]

theorem v1Tag10_memRegion_fold_temp (fsp w_sp408 : BitVec 64) :
    memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 168 ∗
      memRegion (fsp + 184#64) 56 ∗
      memRegion (fsp + 240#64) 168 ∗
      ((fsp + 408#64) ↦₆₄ w_sp408) ∗
      memRegion (fsp + 416#64) 64 ∗
      memRegion (fsp + 480#64) 168 ∗
      memRegion (fsp + 648#64) 72 ⊢
      memRegion fsp 720 := by
  rw [v1Tag10_memRegion_split_temp fsp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (Entails.sepExists_intro w_sp408)))))

theorem v1Tag10_memRegion_168_split_init (fsp : BitVec 64) :
    memRegion (fsp + 16#64) 168 =
      (∃∗ w_sp16 : BitVec 64, ((fsp + 16#64) ↦₆₄ w_sp16)) ∗
      memRegion (fsp + 24#64) 120 ∗
      (∃∗ w_sp144 : BitVec 64, ((fsp + 144#64) ↦₆₄ w_sp144)) ∗
      memRegion (fsp + 152#64) 32 := by
  have s1 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 24#64) (n := 8) (k := 160) (N := 168) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 24#64) (b' := fsp + 144#64) (n := 120) (k := 40) (N := 160) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 144#64) (b' := fsp + 152#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, ProofLib.memRegion_eight (fsp + 16#64), ProofLib.memRegion_eight (fsp + 144#64)]

theorem v1Tag10_reconstruct_innerState (A : RustAlloc) (mPtr : BitVec 64) (bsLen : Nat)
    (ca : V1State.Chunked.Ct1Acknowledged)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64) :
    (mPtr ↦₆₄ 0x8000000000000009#64) ∗
      v1Tag10_words21At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      memRegion (mPtr + 176#64) 48 ∗
      v1Tag10_capHeap A bsLen ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ⊢
      optProtoInnerStateCapAt A mPtr bsLen (some (.ct1Acknowledged ca)) := by
  dsimp only [optProtoInnerStateCapAt, protoInnerStateCapAt]
  refine Entails.trans (Entails.of_eq (show
    (mPtr ↦₆₄ 0x8000000000000009#64) ∗
      v1Tag10_words21At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 ∗
      memRegion (mPtr + 176#64) 48 ∗
      v1Tag10_capHeap A bsLen ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 =
    (mPtr ↦₆₄ 0x8000000000000009#64) ∗
      (v1Tag10_words21At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 ∗
       v1Tag10_capHeap A bsLen ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20) ∗
      memRegion (mPtr + 176#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left
    (v1Tag10_of_words A (mPtr + 8#64) bsLen ca w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20))

/-! ## 2. Error Drop (`+956..+1040 -> +2072..+2112 -> +2692 -> +2700`) -/

private theorem v1Tag10_err_dec_body_1020 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0)) (rustDeallocSpec A))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1020#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = cnt → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP (libsignalSessionCode.rebase b H)
        ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1008#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
  simp only [rustDeallocSpec] at hDealloc; v1StateMerge_fetches b H 1008 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hsp hx22 hx23 hx24 hx25
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b H) (entry + 1008#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem v1Tag10_err_dec_loop_1020 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0)) (rustDeallocSpec A))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1020#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 rest.length → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP (libsignalSessionCode.rebase b H)
        ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2072#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap) := by
  have hbody := v1Tag10_err_dec_body_1020 (b := b) (H := H) hDealloc (ptsPtr := ptsPtr) (ptsCap := ptsCap) hsp_align
  v1StateMerge_fetches b H 1008 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp hx22 hx23 hx24 hx25
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := entry + 1008#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 (Reg.gpr 25#5) = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp hx22 hx23 hx24 hx25) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx24_1 ⊢; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx24_1
      refine seq_clean (mid := entry + 1020#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
          sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 (Reg.gpr 25#5) = (cur + 24#64) + 8#64)
        (by rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
      refine SepWP.mono (ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
        (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2 hx24_2 hx25_2) ?_
      rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
      have hsplit := cons_len_mul bs (bs2 :: tl2) 24
      have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      refine ⟨Entails.trans hPm ?_, hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2, hx22_m, hx23_m⟩
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
      exact Entails.refl _

private theorem v1Tag10_err_dec_976 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0)) (rustDeallocSpec A))
    {s : State} {fsp : BitVec 64} {optDec : Option PolynomialDecoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoPolynomialDecoderAt A (fsp + 368#64) (optDec.map pbToProtoPolyDecoder) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 368#64) 40 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  cases optDec with
  | none =>
    v1StateMerge_fetches b H 976 32; v1StateMerge_fetches b H 2692 8
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
    examples_hide_fetches
    have hnone40 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 32 ⊢ memRegion (fsp + 368#64) 40 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyDecoder_none_entails_memRegion_40 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialDecoderAt_none', show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone40 (by sep_focus); wp_done
  | some dec =>
    simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
    let pb := pbToProtoPolyDecoder dec
    apply SepWP.fold (protoPolyDecoderAt_entails_dealloc A (fsp + 368#64) pb) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro g; apply SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _hpts_ptr_ne⟩
    have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
    have hne_none : (g.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hpts_cap_pow
    have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
    have h384 : (fsp + 368#64) + 16#64 = fsp + 384#64 := by bv_lin
    have h392 : (fsp + 368#64) + 24#64 = fsp + 392#64 := by bv_lin
    have hhdr40 : ((fsp + 368#64) ↦₆₄ g.cap) ∗ ((fsp + 376#64) ↦₆₄ g.ptr) ∗
        ((fsp + 384#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (fsp + 392#64) 16 ⊢
        memRegion (fsp + 368#64) 40 := by
      rw [← h376, ← h384, ← h392]
      exact protoPolyDecoderHeaders_entails_memRegion_40 (fsp + 368#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
    rw [h376, h384, h392]
    refine seq_clean (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2072#64)
      (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion (fsp + 368#64) 40 ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap) ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le hhdr40 ⊢
      cases xs with
      | nil =>
        v1StateMerge_fetches b H 976 32
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
        examples_hide_fetches
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj] at hhdr40 ⊢
        wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_clean (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1020#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗
            (A.live g.ptr (g.cap.toNat * 24) 8 ∗
              memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
              memRegion (fsp + 368#64) 40 ∗ Frame))
          (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
            sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
            sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap ∧
            sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
            sm.readReg64 (Reg.gpr 25#5) = g.ptr + 8#64)
          (by
            v1StateMerge_fetches b H 976 32
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
            examples_hide_fetches
            wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done) ?_
        intro s_loop hpc_loop hrun_loop ⟨hsp_loop, htr_loop, hx21_loop, hx22_loop, hx23_loop, hx24_loop, hx25_loop⟩
        refine SepWP.mono (v1Tag10_err_dec_loop_1020 hDealloc (ptsPtr := g.ptr) (ptsCap := g.cap) hsp_align
          (bs :: tl) g.ptr s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop (hsp_loop.trans hsp)
          hx22_loop hx23_loop hx24_loop hx25_loop) ?_
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
        have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        refine ⟨Entails.trans hPm ?_, hspm.trans hsp_loop, htrm.trans htr_loop, hx21_m.trans hx21_loop, hx22_m, hx23_m⟩
        conv_rhs =>
          arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
      refine SepWP.mono (v1Tag8_err_pts_buf_2072 hDealloc hsp_align hpts_cap_lt hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2) ?_
      rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2⟩

private theorem v1Tag10_err_uc_956 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    {s : State} {fsp : BitVec 64} {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 956#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 976#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) optUc ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc; v1StateMerge_fetches b H 956 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢ memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone128 (by sep_focus); wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (fsp + 240#64) u) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (fsp + 240#64) cap ptr u) (by sep_focus)
    wp_apply; dsimp only [protoUnchunkedCt1SentEkReceivedSize]; wp_done

private theorem v1Tag10_err_956 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0)) (rustDeallocSpec A))
    {s : State} {fsp : BitVec 64} {ca : V1State.Chunked.Ct1Acknowledged} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 956#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (protoChunkedCt1AcknowledgedAt A (fsp + 240#64) ca ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 168 ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedCt1AcknowledgedAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have hjoin168 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 40 ⊢
      memRegion (fsp + 240#64) 168 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 40) (N := 168) rfl (by bv_lin) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) (ca.uc.map ct1SentToCt1SentEkReceived) ∗ A.pool ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialDecoderAt A (fsp + 368#64) (ca.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [v1Tag8_optProtoUnchunkedCt1SentAt_eq, h368, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag10_err_uc_956 hDropUc hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1⟩
  apply SepWP.weaken_pre hP1; apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialDecoderAt A (fsp + 368#64) (ca.receivingEk.map pbToProtoPolyDecoder) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
      (memRegion (fsp + 240#64) 128 ∗ v1StateBelowRest fsp allocHookStack ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_allocHook fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag10_err_dec_976 hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2; apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin168 (by sep_focus)
  exact SepWP.done hpc2 hrun2
    ⟨Entails.of_eq (by ac_rfl), hsp2.trans hsp1, htr2.trans htr1, hx21_2.trans hx21_1⟩

/-! ## 3. Setup (`+880`), Post-Call Copy (`+900`), Pre-Drop (`+2232`), & Post-Drop (`+2284`) -/

private theorem v1Tag10_setup_880 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp144 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 880#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x27c4#64) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 32 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt1AcknowledgedPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧ s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧ s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 900#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 32 ⊢
      chunkedCt1AcknowledgedPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedCt1AcknowledgedPBCapAt A (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedCt1AcknowledgedPBCapAt, optUnchunkedCt1SentPBCapAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    rw [h24, h144, h152]; exact Entails.of_eq (by ac_rfl)
  v1StateMerge_fetches b H 880 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag10_copy_ok_900 {b : BitVec 64} {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp408 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2232#64) s
      (v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag10_words21At_entails_memRegion_168 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  conv => arg 4; rw [v1Tag10_memRegion_168_eq_words21 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  v1StateMerge_fetches b H 900 56
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag10_copy_err_900 {b : BitVec 64} {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp408 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 956#64) s
      (v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 168 ∗
          v1Tag10_words21At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          ((fsp + 408#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := v1Tag10_words21At_entails_memRegion_168 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  conv => arg 4; rw [v1Tag10_memRegion_168_eq_words21 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  v1StateMerge_fetches b H 900 56
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag10_pre_drop_2232 {b : BitVec 64} {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2232#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2284#64) s
      (v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 480#64) 168 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 168 ∗
          v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧ sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧ sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧ sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧ sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag10_words21At_entails_memRegion_168 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  conv => arg 4; rw [v1Tag10_memRegion_168_eq_words21 (fsp + 480#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1; apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3; apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15; apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11; apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19; apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17
  apply SepWP.exists_elim; intro u16
  v1StateMerge_fetches b H 2232 52
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag10_post_drop_2284 {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64) (dropOptProtoInnerStateSpec A b))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true) (hb_align : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
        v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (mPtr ↦₆₄ 0x8000000000000009#64) ∗
          v1Tag10_words21At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          memRegion (mPtr + 176#64) 48 ∗
          memRegion (fsp + 480#64) 168 ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧ sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag10_words21At_entails_memRegion_168 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  simp only [dropOptProtoInnerStateSpec] at hDropInner
  v1StateMerge_fetches b H 2284 96; v1StateMerge_fetches b H 2692 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply; dsimp only [optProtoInnerStateSize]
  conv => arg 4; rw [v1Tag10_memRegion_224_split_ok mPtr]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1; apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3; apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15; apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11; apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19; apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done

/-! ## 4. Discriminant Lemmas & Top-Level `v1State_tag10_step` -/

private theorem v1Tag10_discrFull_other {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .ct1Acknowledged v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x8000000000000009#64) = true := by
  cases is with
  | ct1Acknowledged v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

private theorem v1Tag10_inplace {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x27c4#64)
      ((chunkedCt1AcknowledgedMergeSpec A).inImage img))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {ca : V1State.Chunked.Ct1Acknowledged} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct1Acknowledged ca))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 380#64)
    (hcont : V1StateTagCont img b A H s0 x R 10 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, _hb_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000009#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000009#64) = false := by rw [hx9_eq]; decide
  have hpd : OptPolyDecoderBound ca.receivingEk rest.length := by
    simpa only [hm_is, OptInnerStatePolyBound, InnerStatePolyBound] using hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  v1StateMerge_fetches b H 380 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0x27c4#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, ca, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 420#64) hCaCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt1AcknowledgedMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, (optPolyDecoderBound_iff _ _).mp hpd⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        optPolyDecoderPtsLen ca.receivingEk + rest.length < 2 ^ 56)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1AcknowledgedMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag10 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hca_res : (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) ca rest 99).toOption with
  | none =>
    rw [hca_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := entry + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, hca_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro ca'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000009#64) ∗
        chunkedCt1AcknowledgedPBAt A (x.msgPtr + 8#64) ca' ∗ memRegion (x.msgPtr + 176#64) 48 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt1AcknowledgedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct1Acknowledged ca'))
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
    rcases p with ⟨ca', rest'⟩
    rw [hca_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hca_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Acknowledged ca')) :=
      innerStatePolyBound_of_ct1Acknowledged hpd hca_res
    refine SepWPp.of_sepWP_img (mid := entry + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, hca_res, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Acknowledged ca') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ct1Acknowledged ca') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1Tag10_at_880 {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x27c4#64) ((chunkedCt1AcknowledgedMergeSpec A).inImage img))
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0)) (rustDeallocSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64) (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 880#64)
    (hcont : V1StateTagCont img b A H s0 x R 10 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.Ct1Acknowledged).receivingEk rest.length := optPolyDecoderBound_none h56
  refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x27c4#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, show s0.sp - 816#64 = fsp from rfl,
      v1Tag10_memRegion_split_temp fsp, v1Tag10_memRegion_168_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp408; apply SepWP.exists_elim; intro w_sp144; apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗
        memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
        memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesAt b ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1Tag10_setup_880 (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 900#64) hCaCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedCt1AcknowledgedMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpd0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyDecoderBound (default : V1State.Chunked.Ct1Acknowledged).receivingEk rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1AcknowledgedMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 10) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Acknowledged v') }, rest')) := by
    rw [v1State_mergeField_tag10]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct1Acknowledged ca => exact absurd h (hm_not ca)
      | _ => rfl
  cases hca_res : (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hca_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64)
    conv => arg 4; simp only [chunkedCt1AcknowledgedMergeSpec, hca_res, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro ca'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hca_words : chunkedCt1AcknowledgedPBAt A (fsp + 16#64) ca' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64,
        ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64,
          v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
          v1Tag10_capHeap A 0 ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 :=
      Entails.trans (v1Tag10_chunkedCt1AcknowledgedPBAt_entails_cap_zero A (fsp + 16#64) ca') (v1Tag10_extract_words A (fsp + 16#64) 0 ca')
    apply SepWP.fold hca_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    let Frame_err : SepProp :=
      v1Tag10_capHeap A 0 ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
      memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
      memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_copy_err_900 hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2; dsimp only [Frame_err]
    apply SepWP.fold (v1Tag10_words_entails_protoChunkedCt1Acknowledged A (fsp + 240#64) ca'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedCt1AcknowledgedAt A (fsp + 240#64) ca' ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
          memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
          memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesAt b ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_err_956 hDropUc hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
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
    rcases p with ⟨ca', rest'⟩
    rw [hca_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hca_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Acknowledged ca')) :=
      innerStatePolyBound_of_ct1Acknowledged hpd0 hca_res
    refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) hinv_m ?_
    conv => arg 4; simp only [chunkedCt1AcknowledgedMergeSpec, hca_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag10_extract_words A (fsp + 16#64) rest'.length ca') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20
    rw [← hfsp720] at hfp_m; dsimp only [v1StateJumpTablesAt]
    let Frame_ok : SepProp :=
      v1Tag10_capHeap A rest'.length ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
      (v1StateBelowRest fsp dropStack96 ∗ stackAt fsp dropStack96) ∗
      memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 648#64) 72 ∗
      v1StateMergeJumpTableExpanded b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ (memRegion (fsp + 480#64) 168 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; rw [← v1StateBelow_dropStack96 fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_copy_ok_900 hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, _hx22_2, _hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ (memRegion (fsp + 480#64) 168 ∗ Frame_ok) =
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 480#64) 168 ∗ (memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1Tag10_pre_drop_2232 hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, _hx22_3, _hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3; dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
        v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        (memRegion (fsp + 16#64) 168 ∗ memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
          v1Tag10_capHeap A rest'.length ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 648#64) 72 ∗
          v1StateMergeJumpTableExpanded b ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_post_drop_2284 hDropInner hfsp_align hb_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag10_reconstruct_innerState A x.msgPtr rest'.length ca'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Acknowledged ca') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct1Acknowledged ca') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4, hx22_4, hx23_4,
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)), hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)), hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)), hx29_4.trans hfsp720⟩ hinv4

private theorem v1Tag10_branch_880 {img : Obj.Image} {b : BitVec 64} {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 380#64)
    (hcont : ∀ s' : State, V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 880#64 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  v1StateMerge_fetches b H 380 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 880#64) hinv ?_
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
    have hne : ∀ ca, is ≠ .ct1Acknowledged ca := fun ca h => hm_not ca (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000009#64) = true := v1Tag10_discrFull_other hne hx9_s
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

theorem v1State_tag10_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x27c4#64) ((chunkedCt1AcknowledgedMergeSpec A).inImage img))
    (hDropUc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe6a8#64) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0)) (rustDeallocSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64) (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 380#64)
    (hcont : V1StateTagCont img b A H s0 x R 10 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ ca, m.innerState = some (.ct1Acknowledged ca)
  · rcases hex with ⟨ca, hm_is⟩
    exact v1Tag10_inplace hCaCall hm_is hentry hpc hcont
  · have hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca) := fun ca h => hex ⟨ca, h⟩
    refine v1Tag10_branch_880 hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag10_at_880 hCaCall hDropUc hDealloc hDropInner hm_not hentry' hpc' hcont

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

private theorem v1Tag10_err_dec_body_1020_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_298).base + 1020#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = cnt → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 1008#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
  simp only [rustDeallocSpec] at hDealloc
  intro cur cnt bs s Frame hpc hrun hsp hx22 hx23 hx24 hx25
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 1008#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem v1Tag10_err_dec_loop_1020_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_298).base + 1020#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 rest.length → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 2072#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap) := by
  have hbody := v1Tag10_err_dec_body_1020_placed (H := H) hDealloc (ptsPtr := ptsPtr) (ptsCap := ptsCap) hsp_align
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp hx22 hx23 hx24 hx25
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_298).base + 1008#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 (Reg.gpr 25#5) = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp hx22 hx23 hx24 hx25) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx24_1 ⊢; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx24_1
      refine seq_clean (mid := (blkPl_298).base + 1020#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
          sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 (Reg.gpr 25#5) = (cur + 24#64) + 8#64)
        (by rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
      refine SepWP.mono (ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
        (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2 hx24_2 hx25_2) ?_
      rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
      have hsplit := cons_len_mul bs (bs2 :: tl2) 24
      have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      refine ⟨Entails.trans hPm ?_, hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2, hx22_m, hx23_m⟩
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
      exact Entails.refl _

private theorem v1Tag10_err_dec_976_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {s : State} {fsp : BitVec 64} {optDec : Option PolynomialDecoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialDecoderAt A (fsp + 368#64) (optDec.map pbToProtoPolyDecoder) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 368#64) 40 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  cases optDec with
  | none =>
    have hnone40 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 32 ⊢ memRegion (fsp + 368#64) 40 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyDecoder_none_entails_memRegion_40 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialDecoderAt_none', show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone40 (by sep_focus); wp_done
  | some dec =>
    simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
    let pb := pbToProtoPolyDecoder dec
    apply SepWP.fold (protoPolyDecoderAt_entails_dealloc A (fsp + 368#64) pb) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro g; apply SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _hpts_ptr_ne⟩
    have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
    have hne_none : (g.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hpts_cap_pow
    have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
    have h384 : (fsp + 368#64) + 16#64 = fsp + 384#64 := by bv_lin
    have h392 : (fsp + 368#64) + 24#64 = fsp + 392#64 := by bv_lin
    have hhdr40 : ((fsp + 368#64) ↦₆₄ g.cap) ∗ ((fsp + 376#64) ↦₆₄ g.ptr) ∗
        ((fsp + 384#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (fsp + 392#64) 16 ⊢
        memRegion (fsp + 368#64) 40 := by
      rw [← h376, ← h384, ← h392]
      exact protoPolyDecoderHeaders_entails_memRegion_40 (fsp + 368#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
    rw [h376, h384, h392]
    refine seq_clean (mid := (blkPl_298).base + 2072#64)
      (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion (fsp + 368#64) 40 ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap) ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le hhdr40 ⊢
      cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj] at hhdr40 ⊢
        wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_clean (mid := (blkPl_298).base + 1020#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗
            (A.live g.ptr (g.cap.toNat * 24) 8 ∗
              memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
              memRegion (fsp + 368#64) 40 ∗ Frame))
          (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
            sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
            sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap ∧
            sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
            sm.readReg64 (Reg.gpr 25#5) = g.ptr + 8#64)
          (by
            wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done) ?_
        intro s_loop hpc_loop hrun_loop ⟨hsp_loop, htr_loop, hx21_loop, hx22_loop, hx23_loop, hx24_loop, hx25_loop⟩
        refine SepWP.mono (v1Tag10_err_dec_loop_1020_placed hDealloc (ptsPtr := g.ptr) (ptsCap := g.cap) hsp_align
          (bs :: tl) g.ptr s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop (hsp_loop.trans hsp)
          hx22_loop hx23_loop hx24_loop hx25_loop) ?_
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
        have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        refine ⟨Entails.trans hPm ?_, hspm.trans hsp_loop, htrm.trans htr_loop, hx21_m.trans hx21_loop, hx22_m, hx23_m⟩
        conv_rhs =>
          arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
      refine SepWP.mono (v1Tag8_err_pts_buf_2072_placed hDealloc hsp_align hpts_cap_lt hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2) ?_
      rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2⟩

private theorem v1Tag10_err_uc_956_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    {s : State} {fsp : BitVec 64} {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 956#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 976#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) optUc ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢ memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone128 (by sep_focus); wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (fsp + 240#64) u) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (fsp + 240#64) cap ptr u) (by sep_focus)
    wp_apply; dsimp only [protoUnchunkedCt1SentEkReceivedSize]; wp_done

private theorem v1Tag10_err_956_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {s : State} {fsp : BitVec 64} {ca : V1State.Chunked.Ct1Acknowledged} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 956#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedCt1AcknowledgedAt A (fsp + 240#64) ca ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 168 ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedCt1AcknowledgedAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have hjoin168 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 40 ⊢
      memRegion (fsp + 240#64) 168 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 40) (N := 168) rfl (by bv_lin) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) (ca.uc.map ct1SentToCt1SentEkReceived) ∗ A.pool ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialDecoderAt A (fsp + 368#64) (ca.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [v1Tag8_optProtoUnchunkedCt1SentAt_eq, h368, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag10_err_uc_956_placed hDropUc hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx21_1⟩
  apply SepWP.weaken_pre hP1; apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialDecoderAt A (fsp + 368#64) (ca.receivingEk.map pbToProtoPolyDecoder) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
      (memRegion (fsp + 240#64) 128 ∗ v1StateBelowRest fsp allocHookStack ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_allocHook fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag10_err_dec_976_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2; apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin168 (by sep_focus)
  exact SepWP.done hpc2 hrun2
    ⟨Entails.of_eq (by ac_rfl), hsp2.trans hsp1, htr2.trans htr1, hx21_2.trans hx21_1⟩

/-! ## 5. Placed (`[LibsignalPlacement]`) Setup, Copy, Drop & Step Lemmas -/

private theorem v1Tag10_setup_880_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp144 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 880#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 32 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt1AcknowledgedPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧ s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧ s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 900#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 32 ⊢
      chunkedCt1AcknowledgedPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedCt1AcknowledgedPBCapAt A (fsp + 16#64) restLen ⟨none, none⟩
    dsimp only [chunkedCt1AcknowledgedPBCapAt, optUnchunkedCt1SentPBCapAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    rw [h24, h144, h152]; exact Entails.of_eq (by ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag10_copy_ok_900_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp408 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2232#64) s
      (v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag10_words21At_entails_memRegion_168 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  conv => arg 4; rw [v1Tag10_memRegion_168_eq_words21 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag10_copy_err_900_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp408 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 956#64) s
      (v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 168 ∗
          v1Tag10_words21At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          ((fsp + 408#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := v1Tag10_words21At_entails_memRegion_168 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  conv => arg 4; rw [v1Tag10_memRegion_168_eq_words21 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag10_pre_drop_2232_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2232#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2284#64) s
      (v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 480#64) 168 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 168 ∗
          v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧ sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧ sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧ sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧ sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag10_words21At_entails_memRegion_168 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  conv => arg 4; rw [v1Tag10_memRegion_168_eq_words21 (fsp + 480#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1; apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3; apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15; apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11; apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19; apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17
  apply SepWP.exists_elim; intro u16
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag10_post_drop_2284_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec A))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (mPtr ↦₆₄ 0x8000000000000009#64) ∗
          v1Tag10_words21At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 ∗
          memRegion (mPtr + 176#64) 48 ∗
          memRegion (fsp + 480#64) 168 ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧ sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag10_words21At_entails_memRegion_168 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps; wp_apply; dsimp only [optProtoInnerStateSize]
  conv => arg 4; rw [v1Tag10_memRegion_224_split_ok mPtr]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1; apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3; apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15; apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11; apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19; apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17
  apply SepWP.exists_elim; intro d16
  dsimp only [v1Tag10_words21At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done


private theorem v1Tag10_inplace_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307)
      (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {ca : V1State.Chunked.Ct1Acknowledged} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct1Acknowledged ca))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 380#64)
    (hcont : V1StateTagContPlaced A H s0 x R 10 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000009#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000009#64) = false := by rw [hx9_eq]; decide
  have hpd : OptPolyDecoderBound ca.receivingEk rest.length := by
    simpa only [hm_is, OptInnerStatePolyBound, InnerStatePolyBound] using hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 307) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, ca, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 420#64) hCaCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt1AcknowledgedMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, (optPolyDecoderBound_iff _ _).mp hpd⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        optPolyDecoderPtsLen ca.receivingEk + rest.length < 2 ^ 56)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1AcknowledgedMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag10 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hca_res : (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) ca rest 99).toOption with
  | none =>
    rw [hca_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, hca_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro ca'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000009#64) ∗
        chunkedCt1AcknowledgedPBAt A (x.msgPtr + 8#64) ca' ∗ memRegion (x.msgPtr + 176#64) 48 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt1AcknowledgedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct1Acknowledged ca'))
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
    rcases p with ⟨ca', rest'⟩
    rw [hca_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hca_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Acknowledged ca')) :=
      innerStatePolyBound_of_ct1Acknowledged hpd hca_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1AcknowledgedMergeSpec, hca_res, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Acknowledged ca') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ct1Acknowledged ca') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1Tag10_at_880_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 880#64)
    (hcont : V1StateTagContPlaced A H s0 x R 10 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.Ct1Acknowledged).receivingEk rest.length := optPolyDecoderBound_none h56
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 307) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag10_memRegion_split_temp fsp, v1Tag10_memRegion_168_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp408; apply SepWP.exists_elim; intro w_sp144; apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗
        memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
        memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1Tag10_setup_880_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 900#64) hCaCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedCt1AcknowledgedMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpd0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyDecoderBound (default : V1State.Chunked.Ct1Acknowledged).receivingEk rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1AcknowledgedMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 10) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Acknowledged v') }, rest')) := by
    rw [v1State_mergeField_tag10]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct1Acknowledged ca => exact absurd h (hm_not ca)
      | _ => rfl
  cases hca_res : (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hca_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv => arg 4; simp only [chunkedCt1AcknowledgedMergeSpec, hca_res, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro ca'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hca_words : chunkedCt1AcknowledgedPBAt A (fsp + 16#64) ca' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64,
        ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64,
          v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
          v1Tag10_capHeap A 0 ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 :=
      Entails.trans (v1Tag10_chunkedCt1AcknowledgedPBAt_entails_cap_zero A (fsp + 16#64) ca') (v1Tag10_extract_words A (fsp + 16#64) 0 ca')
    apply SepWP.fold hca_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    let Frame_err : SepProp :=
      v1Tag10_capHeap A 0 ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
      memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
      memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_copy_err_900_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2; dsimp only [Frame_err]
    apply SepWP.fold (v1Tag10_words_entails_protoChunkedCt1Acknowledged A (fsp + 240#64) ca'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedCt1AcknowledgedAt A (fsp + 240#64) ca' ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗
          memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 480#64) 168 ∗
          memRegion (fsp + 648#64) 72 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_err_956_placed hDropUc hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
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
    rcases p with ⟨ca', rest'⟩
    rw [hca_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hca_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Acknowledged ca')) :=
      innerStatePolyBound_of_ct1Acknowledged hpd0 hca_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv => arg 4; simp only [chunkedCt1AcknowledgedMergeSpec, hca_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag10_extract_words A (fsp + 16#64) rest'.length ca') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20
    rw [← hfsp720] at hfp_m; dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag10_capHeap A rest'.length ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
      (v1StateBelowRest fsp dropStack96 ∗ stackAt fsp dropStack96) ∗
      memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 648#64) 72 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ w_sp408) ∗ (memRegion (fsp + 480#64) 168 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; rw [← v1StateBelow_dropStack96 fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_copy_ok_900_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, _hx22_2, _hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ (memRegion (fsp + 480#64) 168 ∗ Frame_ok) =
      v1Tag10_words21At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        memRegion (fsp + 480#64) 168 ∗ (memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1Tag10_pre_drop_2232_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, _hx22_3, _hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3; dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag10_words21At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
        (memRegion (fsp + 16#64) 168 ∗ memRegion (fsp + 240#64) 168 ∗ ((fsp + 408#64) ↦₆₄ x.msgPtr) ∗
          v1Tag10_capHeap A rest'.length ca' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 184#64) 56 ∗ memRegion (fsp + 416#64) 64 ∗ memRegion (fsp + 648#64) 72 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag10_post_drop_2284_placed hDropInner hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag10_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag10_reconstruct_innerState A x.msgPtr rest'.length ca'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Acknowledged ca') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct1Acknowledged ca') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4, hx22_4, hx23_4,
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)), hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)), hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)), hx29_4.trans hfsp720⟩ hinv4

private theorem v1Tag10_branch_880_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 380#64)
    (hcont : ∀ s' : State, V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 880#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 880#64) hinv ?_
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
    have hne : ∀ ca, is ≠ .ct1Acknowledged ca := fun ca h => hm_not ca (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000009#64) = true := v1Tag10_discrFull_other hne hx9_s
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

theorem v1State_tag10_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCaCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 380#64)
    (hcont : V1StateTagContPlaced A H s0 x R 10 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ ca, m.innerState = some (.ct1Acknowledged ca)
  · rcases hex with ⟨ca, hm_is⟩
    exact v1Tag10_inplace_placed hCaCall hm_is hentry hpc hcont
  · have hm_not : ∀ ca, m.innerState ≠ some (.ct1Acknowledged ca) := fun ca h => hex ⟨ca, h⟩
    refine v1Tag10_branch_880_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag10_at_880_placed hCaCall hDropUc hDealloc hDropInner hm_not hentry' hpc' hcont


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
