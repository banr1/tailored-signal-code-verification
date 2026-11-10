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
# Tag Arm 11 (`Ct2Sampled`) for `V1State::merge` (`0x4e7e8`)

Verifies tag arm 11 (`Ct2Sampled`, entry `+700`, fresh-init `+1800`) from its jump-table entry to
the shared loop latch at `entry + 2700#64` (`0x4f274`), both at fixed offset and under
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

/-! ## 1. 14-Word Layout Helpers (`112` bytes) for `Chunked.Ct2Sampled` -/

def v1Tag11_words14At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64) : SepProp :=
  words7At a w0 w1 w2 w3 w4 w5 w6 ∗
    words7At (a + 56#64) w7 w8 w9 w10 w11 w12 w13

def v1Tag11_capHeap (A : RustAlloc) (bsLen : Nat) (c2 : V1State.Chunked.Ct2Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64) : SepProp :=
  optPolyEncoderHeap A c2.sendingCt2 w0 w1 w2 w3 w4 w5 w6 ∗
    optUnchunked2CapHeap A bsLen (c2.uc.map fun u => (u.epoch, u.auth)) w7 w8 w9 w10 w11 w12 w13

theorem v1Tag11_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (c2 : V1State.Chunked.Ct2Sampled) :
    chunkedCt2SampledPBCapAt A a bsLen c2 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64,
        v1Tag11_words14At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        v1Tag11_capHeap A bsLen c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 := by
  dsimp only [chunkedCt2SampledPBCapAt]
  have h56 : a + 0x38#64 = a + 56#64 := rfl
  rw [h56, optCt2SentPBCapAt_eq_optUnchunked2]
  refine Entails.trans (sepConj_mono
    (optPolynomialEncoderPBAt_extract_words A a c2.sendingCt2)
    (optUnchunked2CapAt_extract_words A (a + 56#64) bsLen (c2.uc.map fun u => (u.epoch, u.auth)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w8 =>
    ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w10 =>
    ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w12 =>
    ProofLib.Entails.sepExists_elim fun w13 => ProofLib.Entails.sepExists_elim fun w0 =>
    ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 =>
    ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
    ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w6 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  dsimp only [v1Tag11_words14At, v1Tag11_capHeap]; exact Entails.of_eq (by ac_rfl)

theorem v1Tag11_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (c2 : V1State.Chunked.Ct2Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64) :
    v1Tag11_words14At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      v1Tag11_capHeap A bsLen c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ⊢
      chunkedCt2SampledPBCapAt A a bsLen c2 := by
  dsimp only [chunkedCt2SampledPBCapAt, v1Tag11_words14At, v1Tag11_capHeap]
  have h56 : a + 0x38#64 = a + 56#64 := rfl
  rw [h56, optCt2SentPBCapAt_eq_optUnchunked2]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono
      (optPolynomialEncoderPBAt_of_words A a c2.sendingCt2 w0 w1 w2 w3 w4 w5 w6)
      (optUnchunked2CapAt_of_words A (a + 56#64) bsLen (c2.uc.map fun u => (u.epoch, u.auth))
        w7 w8 w9 w10 w11 w12 w13))

theorem v1Tag11_pb_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (c2 : V1State.Chunked.Ct2Sampled) :
    chunkedCt2SampledPBAt A a c2 ⊢ chunkedCt2SampledPBCapAt A a 0 c2 :=
  sepConj_mono_right (optCt2SentPBAt_entails_cap_zero A (a + 0x38#64) c2.uc)

theorem v1Tag11_reconstruct_innerState (A : RustAlloc) (mPtr : BitVec 64) (bsLen : Nat)
    (c2 : V1State.Chunked.Ct2Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64) :
    (mPtr ↦₆₄ 0x800000000000000a#64) ∗
      v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      v1Tag11_capHeap A bsLen c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      memRegion (mPtr + 120#64) 104 ⊢
      optProtoInnerStateCapAt A mPtr bsLen (some (.ct2Sampled c2)) := by
  dsimp only [optProtoInnerStateCapAt, protoInnerStateCapAt]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    (mPtr ↦₆₄ 0x800000000000000a#64) ∗
      v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      v1Tag11_capHeap A bsLen c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      memRegion (mPtr + 120#64) 104 =
    (mPtr ↦₆₄ 0x800000000000000a#64) ∗
      (v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        v1Tag11_capHeap A bsLen c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) ∗
      memRegion (mPtr + 120#64) 104)) ?_
  exact sepConj_mono_right (sepConj_mono_left
    (v1Tag11_of_words A (mPtr + 8#64) bsLen c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13))

theorem v1Tag11_memRegion_112_eq_words14 (a : BitVec 64) :
    memRegion a 112 =
      ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ w13 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64,
        v1Tag11_words14At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 := by
  have s1 := memRegion_split' (b := a) (b' := a + 56#64) (n := 56) (k := 56) (N := 112) rfl (by bv_lin) (by decide)
  rw [s1, memRegion_56_eq_words7 a]
  simp only [sepExists_sepConj_left]
  rw [memRegion_56_eq_words7 (a + 56#64)]
  simp only [sepExists_sepConj_right]; rfl

theorem v1Tag11_words14At_entails_memRegion_112 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64) :
    v1Tag11_words14At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ⊢ memRegion a 112 := by
  rw [v1Tag11_memRegion_112_eq_words14 a]
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  exact Entails.refl _

theorem v1Tag11_memRegion_224_split_ok (a : BitVec 64) :
    memRegion a 224 =
      ∃∗ vd : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64,
        (a ↦₆₄ vd) ∗
        v1Tag11_words14At (a + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (a + 120#64) 104 := by
  have s1 := memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 216) (N := 224) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 8#64) (b' := a + 120#64) (n := 112) (k := 104) (N := 216) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_eight a, sepExists_sepConj_left, v1Tag11_memRegion_112_eq_words14 (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem v1Tag11_memRegion_split_temp (fsp : BitVec 64) :
    memRegion fsp 720 =
      memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 112 ∗
      memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 240#64) 112 ∗
      (∃∗ w_sp352 : BitVec 64, ((fsp + 352#64) ↦₆₄ w_sp352)) ∗
      memRegion (fsp + 360#64) 120 ∗
      memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 := by
  have s1 := memRegion_split' (b := fsp) (b' := fsp + 16#64) (n := 16) (k := 704) (N := 720) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 128#64) (n := 112) (k := 592) (N := 704) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 128#64) (b' := fsp + 240#64) (n := 112) (k := 480) (N := 592) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 352#64) (n := 112) (k := 368) (N := 480) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := fsp + 352#64) (b' := fsp + 360#64) (n := 8) (k := 360) (N := 368) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := fsp + 360#64) (b' := fsp + 480#64) (n := 120) (k := 240) (N := 360) rfl (by bv_lin) (by decide)
  have s7 := memRegion_split' (b := fsp + 480#64) (b' := fsp + 592#64) (n := 112) (k := 128) (N := 240) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (fsp + 352#64)]

theorem v1Tag11_memRegion_fold_temp (fsp w_sp352 : BitVec 64) :
    memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 112 ∗
      memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 240#64) 112 ∗
      ((fsp + 352#64) ↦₆₄ w_sp352) ∗
      memRegion (fsp + 360#64) 120 ∗
      memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ⊢
      memRegion fsp 720 := by
  rw [v1Tag11_memRegion_split_temp fsp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (Entails.sepExists_intro w_sp352)))))

theorem v1Tag11_memRegion_112_split_init (fsp : BitVec 64) :
    memRegion (fsp + 16#64) 112 =
      (∃∗ w_sp16 : BitVec 64, ((fsp + 16#64) ↦₆₄ w_sp16)) ∗
      memRegion (fsp + 24#64) 48 ∗
      (∃∗ w_sp72 : BitVec 64, ((fsp + 72#64) ↦₆₄ w_sp72)) ∗
      memRegion (fsp + 80#64) 48 := by
  have s1 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 24#64) (n := 8) (k := 104) (N := 112) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 24#64) (b' := fsp + 72#64) (n := 48) (k := 56) (N := 104) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 72#64) (b' := fsp + 80#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, ProofLib.memRegion_eight (fsp + 16#64), ProofLib.memRegion_eight (fsp + 72#64)]

/-! ## 2. Error-Path Heap Deallocation (`+1864..+1944`) -/

theorem v1Tag11_uc_err_heap_dealloc (A : RustAlloc) (c2 : V1State.Chunked.Ct2Sampled)
    (w7 w8 w9 w10 w11 w12 w13 : BitVec 64) :
    optUnchunked2CapHeap A 0 (c2.uc.map fun u => (u.epoch, u.auth)) w7 w8 w9 w10 w11 w12 w13 ⊢
      if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
      else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11 := by
  rcases h_uc : c2.uc with _ | u
  · dsimp only [Option.map, optUnchunked2CapHeap]
    rw [← sepConj_emp ⌜w7 = noneCap2⌝]
    refine Entails.pure_left fun hw7 => ?_; subst hw7
    have h2 : (noneCap2 + 2#64 == 0#64) = true := rfl
    simp only [h2, Bool.true_or, ↓reduceIte]; exact Entails.refl _
  · rcases h_auth : u.auth with _ | auth
    · dsimp only [Option.map, optUnchunked2CapHeap, unchunked2CapHeap, optAuthCapHeap]
      rw [h_auth]; dsimp only
      refine Entails.pure_left fun hw7 => ?_; subst hw7
      rw [← sepConj_emp ⌜w13 = u.epoch⌝]
      refine Entails.pure_left fun _ => ?_
      have h1 : (noneCap + 1#64 == 0#64) = true := rfl
      simp only [h1, Bool.or_true, ↓reduceIte]; exact Entails.refl _
    · dsimp only [Option.map, optUnchunked2CapHeap, unchunked2CapHeap, optAuthCapHeap]
      rw [h_auth]; dsimp only
      refine Entails.trans (sepConj_mono_left (sepConj_mono
        (vecU8CapHeap_entails_dealloc A 0 auth.rootKey w7 w8 w9)
        (vecU8CapHeap_entails_dealloc A 0 auth.macKey w10 w11 w12))) ?_
      refine Entails.trans (Entails.of_eq (by ac_rfl :
        ((⌜w7.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A w7 w8) ∗
          (⌜w10.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A w10 w11)) ∗ ⌜w13 = u.epoch⌝ =
        ⌜w7.toNat < 2 ^ 63⌝ ∗ ⌜w10.toNat < 2 ^ 63⌝ ∗ ⌜w13 = u.epoch⌝ ∗
          (vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11))) ?_
      refine Entails.pure_left fun hw7 => Entails.pure_left fun _ => Entails.pure_left fun _ => ?_
      have hne2 : (w7 + 2#64 == 0#64) = false := cap_lt_add2_beq_zero_false hw7
      have hne1 : (w7 + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hw7
      simp only [hne2, hne1, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      exact Entails.refl _

theorem v1Tag11_words_entails_err_dealloc (A : RustAlloc) (a : BitVec 64)
    (c2 : V1State.Chunked.Ct2Sampled)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64) :
    v1Tag11_words14At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      v1Tag11_capHeap A 0 c2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ⊢
      optProtoPolynomialEncoderAt A a (c2.sendingCt2.map pbToProtoPolyEncoder) ∗
      words7At (a + 56#64) w7 w8 w9 w10 w11 w12 w13 ∗
      (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
       else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) := by
  dsimp only [v1Tag11_words14At, v1Tag11_capHeap]
  rw [← optPolynomialEncoderPBAt_eq_proto]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    (words7At a w0 w1 w2 w3 w4 w5 w6 ∗ words7At (a + 56#64) w7 w8 w9 w10 w11 w12 w13) ∗
      (optPolyEncoderHeap A c2.sendingCt2 w0 w1 w2 w3 w4 w5 w6 ∗
        optUnchunked2CapHeap A 0 (c2.uc.map fun u => (u.epoch, u.auth)) w7 w8 w9 w10 w11 w12 w13) =
    (words7At a w0 w1 w2 w3 w4 w5 w6 ∗ optPolyEncoderHeap A c2.sendingCt2 w0 w1 w2 w3 w4 w5 w6) ∗
      words7At (a + 56#64) w7 w8 w9 w10 w11 w12 w13 ∗
      optUnchunked2CapHeap A 0 (c2.uc.map fun u => (u.epoch, u.auth)) w7 w8 w9 w10 w11 w12 w13)) ?_
  exact sepConj_mono (optPolynomialEncoderPBAt_of_words A a c2.sendingCt2 w0 w1 w2 w3 w4 w5 w6)
    (sepConj_mono_right (v1Tag11_uc_err_heap_dealloc A c2 w7 w8 w9 w10 w11 w12 w13))

private theorem v1Tag11_err_dealloc_w7_1884 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = w7) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1900#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A w7 w8 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  v1StateMerge_fetches b H 1884 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw7 : (w7 == 0#64) = true <;>
    simp only [hw7, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = true := by rw [hx1]; exact hw7
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = false := by
      rw [hx1]; exact Bool.eq_false_iff.mpr hw7
    wp_steps; wp_apply
    refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

private theorem v1Tag11_err_dealloc_w10_1900 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A w10 w11 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  v1StateMerge_fetches b H 1900 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw10 : (w10 == 0#64) = true <;>
    simp only [hw10, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · have hbr : (w10 == 0#64) = false := Bool.eq_false_iff.mpr hw10
    wp_steps; wp_apply
    refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

private theorem v1Tag11_err_uc_1864 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 296#64) 56 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hfold56 : words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ⊢ memRegion (fsp + 296#64) 56 := by
    rw [memRegion_56_eq_words7 (fsp + 296#64)]
    refine Entails.trans ?_ (Entails.sepExists_intro w13); refine Entails.trans ?_ (Entails.sepExists_intro w12)
    refine Entails.trans ?_ (Entails.sepExists_intro w11); refine Entails.trans ?_ (Entails.sepExists_intro w10)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); exact Entails.refl _
  by_cases h2 : (w7 + 2#64 == 0#64) = true
  · simp only [h2, Bool.true_or, ↓reduceIte, emp_sepConj]
    v1StateMerge_fetches b H 1864 20
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
    examples_hide_fetches
    dsimp only [words7At] at hfold56 ⊢
    wp_steps; apply SepWP.fold hfold56 (by sep_focus); wp_done
  · have h2f : (w7 + 2#64 == 0#64) = false := Bool.eq_false_iff.mpr h2
    by_cases h1 : (w7 + 1#64 == 0#64) = true
    · simp only [h2f, h1, Bool.or_true, ↓reduceIte, emp_sepConj]
      v1StateMerge_fetches b H 1864 20
      generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
      examples_hide_fetches
      dsimp only [words7At] at hfold56 ⊢
      wp_steps; apply SepWP.fold hfold56 (by sep_focus); wp_done
    · have h1f : (w7 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr h1
      simp only [h2f, h1f, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      have hstep1 : SepWP (libsignalSessionCode.rebase b H)
          ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1884#64) s
          (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
            (vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun s1 P1 =>
            (P1 ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
              vecCapPtrDealloc A w7 w8 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              (vecCapPtrDealloc A w10 w11 ∗ Frame)) ∧
            s1.sp = s.sp ∧ s1.v1TraceEq s ∧
            s1.readReg64 (Reg.gpr 1#5) = w7 ∧
            s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
        v1StateMerge_fetches b H 1864 20
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
        examples_hide_fetches
        dsimp only [words7At]
        wp_steps; wp_done
      refine SepWP.seq hstep1 ?_
      rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx1_1, hx21_1⟩
      refine SepWP.weaken_pre hP1 ?_
      refine SepWP.seq (v1Tag11_err_dealloc_w7_1884 hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx1_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
      refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w10 w11 ∗ Frame) =
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ vecCapPtrDealloc A w10 w11 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ?_
      refine SepWP.mono (v1Tag11_err_dealloc_w10_1900 hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))) ?_
      rintro s3 P3 _ _ ⟨hP3, hsp3, htr3, hx21_3⟩
      exact ⟨Entails.trans hP3 (sepConj_mono_left hfold56),
        hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1),
        hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1Tag11_err_enc_1920 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1920#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoPolynomialEncoderAt A (fsp + 240#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 56 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoPolyEncoderSpec] at hDropEnc
  v1StateMerge_fetches b H 1920 24; v1StateMerge_fetches b H 2692 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 48 ⊢ memRegion (fsp + 240#64) 56 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 240#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none', show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A (fsp + 240#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A (fsp + 240#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    wp_apply; dsimp only [protoPolynomialEncoderSize]; wp_steps; wp_done

/-! ## 3. Setup, Copy & Post-Drop Lemmas for Tag 11 (`+1800..+1864`, `+3040..+3144`) -/

private theorem v1Tag11_setup_1800 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp72 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1208#64) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt2SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1820#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      chunkedCt2SampledPBCapAt A (fsp + 16#64) restLen default := by
    change ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      (((fsp + 16#64) ↦₆₄ noneCap) ∗ memRegion ((fsp + 16#64) + 8#64) 48) ∗
      (((fsp + 16#64) + 0x38#64) ↦₆₄ noneCap2 ∗ memRegion (((fsp + 16#64) + 0x38#64) + 8#64) 48)
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h72 : (fsp + 16#64) + 0x38#64 = fsp + 72#64 := by bv_lin
    have h80 : (fsp + 72#64) + 8#64 = fsp + 80#64 := by bv_lin
    rw [h24, h72, h80]; exact Entails.of_eq (by unfold noneCap noneCap2; ac_rfl)
  v1StateMerge_fetches b H 1800 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag11_copy_ok_1820 {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3040#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ mPtr) ∗ Frame) ∧
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
  have hfold240 := v1Tag11_words14At_entails_memRegion_112 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  conv =>
    arg 4
    rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  v1StateMerge_fetches b H 1820 44
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag11_words14At, words7At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag11_copy_err_1820 {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1864#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          ((fsp + 352#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  v1StateMerge_fetches b H 1820 44
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag11_pre_drop_3040 {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3040#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3076#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗ Frame) ∧
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
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  v1StateMerge_fetches b H 3040 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag11_post_drop_3076 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true) (hb_align : b &&& 4095#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 3076#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 480#64) 112 ∗
          (mPtr ↦₆₄ 0x800000000000000a#64) ∗
          v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (mPtr + 120#64) 104 ∗
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
  have hfold480 := v1Tag11_words14At_entails_memRegion_112 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  simp only [dropOptProtoInnerStateSpec] at hDropInner
  v1StateMerge_fetches b H 3076 68
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [v1Tag11_memRegion_224_split_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done

theorem v1Tag11_discrFull_other {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .ct2Sampled v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d != 0x800000000000000a#64) = true := by
  cases is with
  | ct2Sampled v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    rcases s with ⟨_ | u, _, _⟩
    · change d = noneCap at hd; subst hd; decide
    · rw [bne_iff_ne]; intro heq; subst heq; exact absurd hd.1 (by decide)
  | _ => subst hd; decide

/-! ## 4. Top-Level `v1State_tag11_step` (`Ct2Sampled`, entry `+700`) -/

theorem v1Tag11_inplace {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1208#64)
      ((chunkedCt2SampledMergeSpec A).inImage img))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {c2 : V1State.Chunked.Ct2Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 700#64)
    (hcont : V1StateTagCont img b A H s0 x R 11 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x800000000000000a#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x800000000000000a#64) = false := by
    rw [hx9_eq]; decide
  have hpe_bound : OptPolyEncoderBound c2.sendingCt2 rest.length := by
    simpa only [hm_is, OptInnerStatePolyBound, InnerStatePolyBound] using hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  v1StateMerge_fetches b H 700 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0x1208#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, c2, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 740#64) hC2Call
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt2SampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound c2.sendingCt2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt2SampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag11 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hc2_res : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) c2 rest 99).toOption with
  | none =>
    rw [hc2_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := entry + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro c2'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x800000000000000a#64) ∗
        chunkedCt2SampledPBAt A (x.msgPtr + 8#64) c2' ∗ memRegion (x.msgPtr + 120#64) 104 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt2SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct2Sampled c2'))
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
    rcases p with ⟨c2', rest'⟩
    rw [hc2_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hc2_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct2Sampled c2')) :=
      innerStatePolyBound_of_ct2Sampled hpe_bound hc2_res
    refine SepWPp.of_sepWP_img (mid := entry + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct2Sampled c2') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ct2Sampled c2') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1Tag11_at_1800 {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1208#64)
      ((chunkedCt2SampledMergeSpec A).inImage img))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1800#64)
    (hcont : V1StateTagCont img b A H s0 x R 11 m rest iwt limit) :
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
  refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1208#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      v1Tag11_memRegion_split_temp fsp, v1Tag11_memRegion_112_split_init fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp352
  apply SepWP.exists_elim; intro w_sp72
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗
      (optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        v1StateJumpTablesAt b ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗
        memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
        memRegion (fsp + 592#64) 128 ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag11_setup_1800 (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23 hx27) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr_1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  apply SepWP.weaken_pre hP1
  refine SepWP.done hpc1 hrun1 (fun hinv1 => ?_)
  rw [hsp] at hsp1
  rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest.length :=
    optPolyEncoderBound_none h56
  refine SepWPp.call_frame_inImage (hinv := hinv1)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1820#64) hC2Call
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr_1
    (by dsimp only [chunkedCt2SampledMergeSpec]; rw [hx0_1, hx0, hx1_1, hx2_1, hsp1])
    (⟨rfl, rfl, rfl, hpe0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt2SampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 11) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct2Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag11]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct2Sampled c2 => exact absurd h (hm_not c2)
      | _ => rfl
  cases hc2_res : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hc2_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro c2'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hc2_words : chunkedCt2SampledPBAt A (fsp + 16#64) c2' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64,
          v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          v1Tag11_capHeap A 0 c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 :=
      Entails.trans (v1Tag11_pb_entails_cap_zero A (fsp + 16#64) c2')
        (v1Tag11_extract_words A (fsp + 16#64) 0 c2')
    apply SepWP.fold hc2_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    let Frame_err : SepProp :=
      v1Tag11_capHeap A 0 c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_copy_err_1820 hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (v1Tag11_words_entails_err_dealloc A (fsp + 240#64) c2'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
    rw [v1StateBelow_allocHook fsp]
    have h296 : (fsp + 240#64) + 56#64 = fsp + 296#64 := by bv_lin
    rw [h296]
    let Frame_uc : SepProp :=
      optProtoPolynomialEncoderAt A (fsp + 240#64) (c2'.sendingCt2.map pbToProtoPolyEncoder) ∗
      v1StateBelowRest fsp allocHookStack ∗
      memRegion (fsp + 16#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame_uc)
      (Entails.of_eq (by dsimp only [Frame_uc]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_err_uc_1864 hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_uc]
    apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
    rw [v1StateBelow_dropStack48 fsp]
    let Frame_enc : SepProp :=
      v1StateBelowRest fsp dropStack48 ∗
      memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 296#64) 56 ∗
      ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      optProtoPolynomialEncoderAt A (fsp + 240#64) (c2'.sendingCt2.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame_enc)
      (Entails.of_eq (by dsimp only [Frame_enc]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_err_enc_1920 hDropEnc hfsp_align hpc3 hrun3 (hsp3.trans (hsp2.trans hspm))) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx21_4⟩
    apply SepWP.weaken_pre hP4
    dsimp only [Frame_enc]
    have hjoin240 : memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 56 ⊢ memRegion (fsp + 240#64) 112 := by
      have s1 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 296#64) (n := 56) (k := 56) (N := 112) rfl (by bv_lin) (by decide)
      rw [s1]; exact Entails.refl _
    apply SepWP.fold hjoin240 (by sep_focus)
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc4 hrun4 ?_
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFrame, fsp]; ac_rfl))
    exact hcont.onErr hm_field s4 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc4 hrun4
      (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2)) hsm0 hn_err
  | some p =>
    rcases p with ⟨c2', rest'⟩
    rw [hc2_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hc2_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct2Sampled c2')) :=
      innerStatePolyBound_of_ct2Sampled hpe0 hc2_res
    refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag11_extract_words A (fsp + 16#64) rest'.length c2') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    rw [v1StateBelow_dropStack96 fsp]
    rw [← hfsp720] at hfp_m
    dsimp only [v1StateJumpTablesAt]
    let Frame_ok : SepProp :=
      v1Tag11_capHeap A rest'.length c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
      v1StateMergeJumpTableExpanded b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        (memRegion (fsp + 480#64) 112 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_copy_ok_1820 hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 112 ∗ Frame_ok) =
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗
        (memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1Tag11_pre_drop_3040 hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        (memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
          v1Tag11_capHeap A rest'.length c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
          memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
          v1StateMergeJumpTableExpanded b ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_post_drop_3076 hDropInner hfsp_align hb_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag11_reconstruct_innerState A x.msgPtr rest'.length c2'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct2Sampled c2') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct2Sampled c2') } rest' s4 hm_field hpoly' hrest'_le
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

private theorem v1Tag11_branch_1800 {img : Obj.Image} {b : BitVec 64}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 700#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1800#64 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  v1StateMerge_fetches b H 700 28
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 1800#64) hinv ?_
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
    have hne : ∀ c2, is ≠ .ct2Sampled c2 := fun c2 h => hm_not c2 (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x800000000000000a#64) = true :=
      v1Tag11_discrFull_other hne hx9_s
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

theorem v1State_tag11_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x1208#64)
      ((chunkedCt2SampledMergeSpec A).inImage img))
    (hDropEnc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffdd18#64)
      (dropProtoPolyEncoderSpec A))
    (hDealloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x493f0))
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 700#64)
    (hcont : V1StateTagCont img b A H s0 x R 11 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ c2, m.innerState = some (.ct2Sampled c2)
  · rcases hex with ⟨c2, hm_is⟩
    exact v1Tag11_inplace hC2Call hm_is hentry hpc hcont
  · have hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2) := fun c2 h => hex ⟨c2, h⟩
    refine v1Tag11_branch_1800 hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag11_at_1800 hC2Call hDropEnc hDealloc hDropInner hm_not hentry' hpc' hcont

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

private theorem v1Tag11_err_dealloc_w7_1884_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = w7) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1900#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A w7 w8 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw7 : (w7 == 0#64) = true <;>
    simp only [hw7, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = true := by rw [hx1]; exact hw7
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = false := by
      rw [hx1]; exact Bool.eq_false_iff.mpr hw7
    wp_steps; wp_apply
    refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

private theorem v1Tag11_err_dealloc_w10_1900_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A w10 w11 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw10 : (w10 == 0#64) = true <;>
    simp only [hw10, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · have hbr : (w10 == 0#64) = false := Bool.eq_false_iff.mpr hw10
    wp_steps; wp_apply
    refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

private theorem v1Tag11_err_uc_1864_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 296#64) 56 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hfold56 : words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ⊢ memRegion (fsp + 296#64) 56 := by
    rw [memRegion_56_eq_words7 (fsp + 296#64)]
    refine Entails.trans ?_ (Entails.sepExists_intro w13); refine Entails.trans ?_ (Entails.sepExists_intro w12)
    refine Entails.trans ?_ (Entails.sepExists_intro w11); refine Entails.trans ?_ (Entails.sepExists_intro w10)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); exact Entails.refl _
  by_cases h2 : (w7 + 2#64 == 0#64) = true
  · simp only [h2, Bool.true_or, ↓reduceIte, emp_sepConj]
    dsimp only [words7At] at hfold56 ⊢
    wp_steps; apply SepWP.fold hfold56 (by sep_focus); wp_done
  · have h2f : (w7 + 2#64 == 0#64) = false := Bool.eq_false_iff.mpr h2
    by_cases h1 : (w7 + 1#64 == 0#64) = true
    · simp only [h2f, h1, Bool.or_true, ↓reduceIte, emp_sepConj]
      dsimp only [words7At] at hfold56 ⊢
      wp_steps; apply SepWP.fold hfold56 (by sep_focus); wp_done
    · have h1f : (w7 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr h1
      simp only [h2f, h1f, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      have hstep1 : SepWP ((blkPC_298).rebase (blkPl_298).base H)
          ((blkPl_298).base + 1884#64) s
          (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
            (vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun s1 P1 =>
            (P1 ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
              vecCapPtrDealloc A w7 w8 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              (vecCapPtrDealloc A w10 w11 ∗ Frame)) ∧
            s1.sp = s.sp ∧ s1.v1TraceEq s ∧
            s1.readReg64 (Reg.gpr 1#5) = w7 ∧
            s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
        dsimp only [words7At]
        wp_steps; wp_done
      refine SepWP.seq hstep1 ?_
      rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx1_1, hx21_1⟩
      refine SepWP.weaken_pre hP1 ?_
      refine SepWP.seq (v1Tag11_err_dealloc_w7_1884_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx1_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
      refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w10 w11 ∗ Frame) =
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ vecCapPtrDealloc A w10 w11 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ?_
      refine SepWP.mono (v1Tag11_err_dealloc_w10_1900_placed hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))) ?_
      rintro s3 P3 _ _ ⟨hP3, hsp3, htr3, hx21_3⟩
      exact ⟨Entails.trans hP3 (sepConj_mono_left hfold56),
        hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1),
        hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1Tag11_err_enc_1920_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1920#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialEncoderAt A (fsp + 240#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 56 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoPolyEncoderSpec] at hDropEnc
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 48 ⊢ memRegion (fsp + 240#64) 56 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 240#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none', show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A (fsp + 240#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A (fsp + 240#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    wp_apply; dsimp only [protoPolynomialEncoderSize]; wp_steps; wp_done

/-! ## 5. Placed (`[LibsignalPlacement]`) Setup, Copy, Post-Drop & Step Lemmas -/

private theorem v1Tag11_setup_1800_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp72 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt2SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1820#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      chunkedCt2SampledPBCapAt A (fsp + 16#64) restLen default := by
    change ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      (((fsp + 16#64) ↦₆₄ noneCap) ∗ memRegion ((fsp + 16#64) + 8#64) 48) ∗
      (((fsp + 16#64) + 0x38#64) ↦₆₄ noneCap2 ∗ memRegion (((fsp + 16#64) + 0x38#64) + 8#64) 48)
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h72 : (fsp + 16#64) + 0x38#64 = fsp + 72#64 := by bv_lin
    have h80 : (fsp + 72#64) + 8#64 = fsp + 80#64 := by bv_lin
    rw [h24, h72, h80]; exact Entails.of_eq (by unfold noneCap noneCap2; ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag11_copy_ok_1820_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3040#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ mPtr) ∗ Frame) ∧
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
  have hfold240 := v1Tag11_words14At_entails_memRegion_112 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  conv =>
    arg 4
    rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag11_words14At, words7At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag11_copy_err_1820_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1864#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          ((fsp + 352#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag11_pre_drop_3040_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3040#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3076#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗ Frame) ∧
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
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag11_post_drop_3076_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3076#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 480#64) 112 ∗
          (mPtr ↦₆₄ 0x800000000000000a#64) ∗
          v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (mPtr + 120#64) 104 ∗
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
  have hfold480 := v1Tag11_words14At_entails_memRegion_112 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [v1Tag11_memRegion_224_split_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done


theorem v1Tag11_inplace_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {c2 : V1State.Chunked.Ct2Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 700#64)
    (hcont : V1StateTagContPlaced A H s0 x R 11 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x800000000000000a#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x800000000000000a#64) = false := by
    rw [hx9_eq]; decide
  have hpe_bound : OptPolyEncoderBound c2.sendingCt2 rest.length := by
    simpa only [hm_is, OptInnerStatePolyBound, InnerStatePolyBound] using hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 301) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, c2, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 740#64) hC2Call
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt2SampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound c2.sendingCt2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt2SampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag11 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hc2_res : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) c2 rest 99).toOption with
  | none =>
    rw [hc2_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro c2'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x800000000000000a#64) ∗
        chunkedCt2SampledPBAt A (x.msgPtr + 8#64) c2' ∗ memRegion (x.msgPtr + 120#64) 104 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt2SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct2Sampled c2'))
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
    rcases p with ⟨c2', rest'⟩
    rw [hc2_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hc2_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct2Sampled c2')) :=
      innerStatePolyBound_of_ct2Sampled hpe_bound hc2_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct2Sampled c2') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ct2Sampled c2') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1Tag11_at_1800_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1800#64)
    (hcont : V1StateTagContPlaced A H s0 x R 11 m rest iwt limit) :
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
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 301) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_le hrest_suf,
      v1Tag11_memRegion_split_temp fsp, v1Tag11_memRegion_112_split_init fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp352
  apply SepWP.exists_elim; intro w_sp72
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗
      (optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗
        memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
        memRegion (fsp + 592#64) 128 ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag11_setup_1800_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23 hx27) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr_1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  apply SepWP.weaken_pre hP1
  refine SepWP.done hpc1 hrun1 (fun hinv1 => ?_)
  rw [hsp] at hsp1
  rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest.length :=
    optPolyEncoderBound_none h56
  refine SepWPp.call_frame_lscro (hinv := hinv1)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1820#64) hC2Call
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr_1
    (by dsimp only [chunkedCt2SampledMergeSpec]; rw [hx0_1, hx0, hx1_1, hx2_1, hsp1])
    (⟨rfl, rfl, rfl, hpe0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt2SampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 11) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct2Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag11]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct2Sampled c2 => exact absurd h (hm_not c2)
      | _ => rfl
  cases hc2_res : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hc2_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro c2'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hc2_words : chunkedCt2SampledPBAt A (fsp + 16#64) c2' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64,
          v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          v1Tag11_capHeap A 0 c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 :=
      Entails.trans (v1Tag11_pb_entails_cap_zero A (fsp + 16#64) c2')
        (v1Tag11_extract_words A (fsp + 16#64) 0 c2')
    apply SepWP.fold hc2_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    let Frame_err : SepProp :=
      v1Tag11_capHeap A 0 c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_copy_err_1820_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (v1Tag11_words_entails_err_dealloc A (fsp + 240#64) c2'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
    rw [v1StateBelow_allocHook fsp]
    have h296 : (fsp + 240#64) + 56#64 = fsp + 296#64 := by bv_lin
    rw [h296]
    let Frame_uc : SepProp :=
      optProtoPolynomialEncoderAt A (fsp + 240#64) (c2'.sendingCt2.map pbToProtoPolyEncoder) ∗
      v1StateBelowRest fsp allocHookStack ∗
      memRegion (fsp + 16#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame_uc)
      (Entails.of_eq (by dsimp only [Frame_uc]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_err_uc_1864_placed hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_uc]
    apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
    rw [v1StateBelow_dropStack48 fsp]
    let Frame_enc : SepProp :=
      v1StateBelowRest fsp dropStack48 ∗
      memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 296#64) 56 ∗
      ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      optProtoPolynomialEncoderAt A (fsp + 240#64) (c2'.sendingCt2.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame_enc)
      (Entails.of_eq (by dsimp only [Frame_enc]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_err_enc_1920_placed hDropEnc hfsp_align hpc3 hrun3 (hsp3.trans (hsp2.trans hspm))) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx21_4⟩
    apply SepWP.weaken_pre hP4
    dsimp only [Frame_enc]
    have hjoin240 : memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 56 ⊢ memRegion (fsp + 240#64) 112 := by
      have s1 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 296#64) (n := 56) (k := 56) (N := 112) rfl (by bv_lin) (by decide)
      rw [s1]; exact Entails.refl _
    apply SepWP.fold hjoin240 (by sep_focus)
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc4 hrun4 ?_
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field s4 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc4 hrun4
      (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2)) hsm0 hn_err
  | some p =>
    rcases p with ⟨c2', rest'⟩
    rw [hc2_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hc2_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct2Sampled c2')) :=
      innerStatePolyBound_of_ct2Sampled hpe0 hc2_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag11_extract_words A (fsp + 16#64) rest'.length c2') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    rw [v1StateBelow_dropStack96 fsp]
    rw [← hfsp720] at hfp_m
    dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag11_capHeap A rest'.length c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        (memRegion (fsp + 480#64) 112 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_copy_ok_1820_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 112 ∗ Frame_ok) =
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗
        (memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1Tag11_pre_drop_3040_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        (memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
          v1Tag11_capHeap A rest'.length c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
          memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_post_drop_3076_placed hDropInner hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag11_reconstruct_innerState A x.msgPtr rest'.length c2'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct2Sampled c2') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct2Sampled c2') } rest' s4 hm_field hpoly' hrest'_le
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

private theorem v1Tag11_branch_1800_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 700#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1800#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1800#64) hinv ?_
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
    have hne : ∀ c2, is ≠ .ct2Sampled c2 := fun c2 h => hm_not c2 (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x800000000000000a#64) = true :=
      v1Tag11_discrFull_other hne hx9_s
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

theorem v1State_tag11_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (dropProtoPolyEncoderSpec A))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 700#64)
    (hcont : V1StateTagContPlaced A H s0 x R 11 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ c2, m.innerState = some (.ct2Sampled c2)
  · rcases hex with ⟨c2, hm_is⟩
    exact v1Tag11_inplace_placed hC2Call hm_is hentry hpc hcont
  · have hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2) := fun c2 h => hex ⟨c2, h⟩
    refine v1Tag11_branch_1800_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag11_at_1800_placed hC2Call hDropEnc hDealloc hDropInner hm_not hentry' hpc' hcont


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
