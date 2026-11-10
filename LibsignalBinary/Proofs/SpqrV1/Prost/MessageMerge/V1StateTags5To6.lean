/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag5
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Tag Arms 5–6 (`EkSentCt1Received`, `NoHeaderReceived`) for `V1State::merge` (`0x4e7e8`)

Imports `V1StateTag5` (tag 5 `EkSentCt1Received`) and verifies 12-word (`96` B) stack relocation
and symbolic execution of tag arm 6 (`NoHeaderReceived`, entry `+604`, non-inplace `+1652`) to
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
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local instance] Classical.propDecidable

/-! ## 1. 12-Word (`96`B) Layout & Relocation Helpers for Tag 6 (`NoHeaderReceived`) -/

def words12At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) : SepProp :=
  words5At a w0 w1 w2 w3 w4 ∗
    words7At (a + 40#64) w5 w6 w7 w8 w9 w10 w11

def tag6CapHeap (A : RustAlloc) (bsLen : Nat)
    (optDec : Option PolynomialDecoder)
    (optUc : Option (BitVec 64 × Option ProtoAuthenticator))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) : SepProp :=
  optPolyDecoderHeap A optDec w0 w1 w2 w3 w4 ∗
    optUnchunked2CapHeap A bsLen optUc w5 w6 w7 w8 w9 w10 w11

theorem tag6_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (optDec : Option PolynomialDecoder)
    (optUc : Option (BitVec 64 × Option ProtoAuthenticator)) :
    optPolynomialDecoderPBAt A a optDec ∗ optUnchunked2CapAt A (a + 40#64) bsLen optUc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        words12At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        tag6CapHeap A bsLen optDec optUc w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
  refine Entails.trans (sepConj_mono
    (optPolynomialDecoderPBAt_extract_words A a optDec)
    (optUnchunked2CapAt_extract_words A (a + 40#64) bsLen optUc)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w6 =>
    ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w8 =>
    ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w10 =>
    ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w0 =>
    ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 =>
    ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  dsimp only [words12At, tag6CapHeap]; exact Entails.of_eq (by ac_rfl)

theorem tag6_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (optDec : Option PolynomialDecoder)
    (optUc : Option (BitVec 64 × Option ProtoAuthenticator))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    words12At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      tag6CapHeap A bsLen optDec optUc w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ⊢
      optPolynomialDecoderPBAt A a optDec ∗ optUnchunked2CapAt A (a + 40#64) bsLen optUc := by
  dsimp only [words12At, tag6CapHeap]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono
      (optPolynomialDecoderPBAt_of_words A a optDec w0 w1 w2 w3 w4)
      (optUnchunked2CapAt_of_words A (a + 40#64) bsLen optUc w5 w6 w7 w8 w9 w10 w11))

theorem chunkedNoHeaderReceivedPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (nh : V1State.Chunked.NoHeaderReceived) :
    chunkedNoHeaderReceivedPBAt A a nh ⊢ chunkedNoHeaderReceivedPBCapAt A a 0 nh :=
  sepConj_mono_right (optNoHeaderReceivedPBAt_entails_cap_zero A (a + 40#64) nh.uc)

theorem tag6_words_entails_protoChunkedNoHeaderReceived (A : RustAlloc) (a : BitVec 64)
    (nh : V1State.Chunked.NoHeaderReceived)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    words12At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      tag6CapHeap A 0 nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ⊢
      protoChunkedNoHeaderReceivedAt A a nh := by
  rw [← chunkedNoHeaderReceivedPBAt_eq_proto A a nh]
  refine Entails.trans ?_ (chunkedNoHeaderReceivedPBCapAt_entails_pb A a 0 nh)
  dsimp only [chunkedNoHeaderReceivedPBCapAt]
  rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
  exact tag6_of_words A a 0 nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11

theorem memRegion_96_eq_words12 (a : BitVec 64) :
    memRegion a 96 =
      ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64,
        words12At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
  have s1 := memRegion_split' (b := a) (b' := a + 40#64) (n := 40) (k := 56) (N := 96) rfl (by bv_lin) (by decide)
  rw [s1, memRegion_40_eq_words5_at a]
  simp only [sepExists_sepConj_left]
  rw [memRegion_56_eq_words7 (a + 40#64)]
  simp only [sepExists_sepConj_right]; rfl

theorem words12At_entails_memRegion_96 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    words12At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ⊢
      memRegion a 96 := by
  rw [memRegion_96_eq_words12 a]
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  exact Entails.refl _

theorem memRegion_224_split_tag6_ok (a : BitVec 64) :
    memRegion a 224 =
      ∃∗ vd : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64,
        (a ↦₆₄ vd) ∗
        words12At (a + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (a + 104#64) 120 := by
  have s1 := memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 216) (N := 224) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 8#64) (b' := a + 104#64) (n := 96) (k := 120) (N := 216) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_eight a, sepExists_sepConj_left, memRegion_96_eq_words12 (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_split_tag6_temp (fsp : BitVec 64) :
    memRegion fsp 720 =
      memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 96 ∗
      memRegion (fsp + 112#64) 128 ∗
      memRegion (fsp + 240#64) 96 ∗
      (∃∗ w_sp336 : BitVec 64, ((fsp + 336#64) ↦₆₄ w_sp336)) ∗
      memRegion (fsp + 344#64) 136 ∗
      memRegion (fsp + 480#64) 96 ∗
      memRegion (fsp + 576#64) 144 := by
  have s1 := memRegion_split' (b := fsp) (b' := fsp + 16#64) (n := 16) (k := 704) (N := 720) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 112#64) (n := 96) (k := 608) (N := 704) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 112#64) (b' := fsp + 240#64) (n := 128) (k := 480) (N := 608) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 336#64) (n := 96) (k := 384) (N := 480) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := fsp + 336#64) (b' := fsp + 344#64) (n := 8) (k := 376) (N := 384) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := fsp + 344#64) (b' := fsp + 480#64) (n := 136) (k := 240) (N := 376) rfl (by bv_lin) (by decide)
  have s7 := memRegion_split' (b := fsp + 480#64) (b' := fsp + 576#64) (n := 96) (k := 144) (N := 240) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (fsp + 336#64)]

theorem memRegion_fold_tag6_temp (fsp w_sp336 : BitVec 64) :
    memRegion fsp 16 ∗
      memRegion (fsp + 16#64) 96 ∗
      memRegion (fsp + 112#64) 128 ∗
      memRegion (fsp + 240#64) 96 ∗
      ((fsp + 336#64) ↦₆₄ w_sp336) ∗
      memRegion (fsp + 344#64) 136 ∗
      memRegion (fsp + 480#64) 96 ∗
      memRegion (fsp + 576#64) 144 ⊢
      memRegion fsp 720 := by
  rw [memRegion_split_tag6_temp fsp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (Entails.sepExists_intro w_sp336)))))

theorem memRegion_96_split_tag6_init (fsp : BitVec 64) :
    memRegion (fsp + 16#64) 96 =
      (∃∗ w_sp16 : BitVec 64, ((fsp + 16#64) ↦₆₄ w_sp16)) ∗
      memRegion (fsp + 24#64) 32 ∗
      (∃∗ w_sp56 : BitVec 64, ((fsp + 56#64) ↦₆₄ w_sp56)) ∗
      memRegion (fsp + 64#64) 48 := by
  have s1 := memRegion_split' (b := fsp + 16#64) (b' := fsp + 24#64) (n := 8) (k := 88) (N := 96) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := fsp + 24#64) (b' := fsp + 56#64) (n := 32) (k := 56) (N := 88) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := fsp + 56#64) (b' := fsp + 64#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, ProofLib.memRegion_eight (fsp + 16#64), ProofLib.memRegion_eight (fsp + 56#64)]

theorem tag6_reconstruct_innerState (A : RustAlloc) (mPtr : BitVec 64) (bsLen : Nat)
    (nh : V1State.Chunked.NoHeaderReceived)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    (mPtr ↦₆₄ 0x8000000000000005#64) ∗
      words12At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      tag6CapHeap A bsLen nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      memRegion (mPtr + 104#64) 120 ⊢
      optProtoInnerStateCapAt A mPtr bsLen (some (.noHeaderReceived nh)) := by
  dsimp only [optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedNoHeaderReceivedPBCapAt]
  rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    (mPtr ↦₆₄ 0x8000000000000005#64) ∗
      words12At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      tag6CapHeap A bsLen nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      memRegion (mPtr + 104#64) 120 =
    (mPtr ↦₆₄ 0x8000000000000005#64) ∗
      (words12At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        tag6CapHeap A bsLen nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) ∗
      memRegion (mPtr + 104#64) 120)) ?_
  exact sepConj_mono_right (sepConj_mono_left (tag6_of_words A (mPtr + 8#64) bsLen
    nh.receivingHdr (nh.uc.map fun u => (u.epoch, u.auth))
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11))

/-! ## 2. Stepping Lemmas for Tag 6 (`NoHeaderReceived`, entry `+604`, non-inplace `+1652`, ok `+2832..+2916`) -/

theorem discrFull_other_tag6 {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .noHeaderReceived v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    (d - 0x8000000000000005#64 != 0#64) = true ∧ (d != 0x8000000000000005#64) = true := by
  cases is with
  | noHeaderReceived v => exact absurd rfl (hne v)
  | ct1Sampled s =>
    have hsub := (discrFull_ct1Sampled_sub_ne (c := 0x8000000000000005#64) hd (by decide) (by decide)).2
    refine ⟨hsub, ?_⟩
    rw [bne_iff_ne]; intro heq; subst heq; exact absurd hsub (by decide)
  | _ => subst hd; decide

theorem v1State_tag6_err_1708 {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropNh : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe4fc#64)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    {s : State} {fsp : BitVec 64} {nh : V1State.Chunked.NoHeaderReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1708#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (protoChunkedNoHeaderReceivedAt A (fsp + 240#64) nh ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 96 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoChunkedNoHeaderReceivedSpec] at hDropNh
  v1StateMerge_fetches b H 1708 12
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply
  dsimp only [protoChunkedNoHeaderReceivedSize]
  wp_steps; wp_done

theorem v1State_tag6_setup {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp56 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1652#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x29cc#64) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 32 ∗
        ((fsp + 56#64) ↦₆₄ w_sp56) ∗ memRegion (fsp + 64#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedNoHeaderReceivedPBCapAt A (fsp + 16#64) restLen
          ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1672#64 ∧
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
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 32 ∗
      ((fsp + 56#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 64#64) 48 ⊢
      chunkedNoHeaderReceivedPBCapAt A (fsp + 16#64) restLen
        ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) := by
    dsimp only [chunkedNoHeaderReceivedPBCapAt, optPolynomialDecoderPBAt,
      optNoHeaderReceivedPBCapAt, noneCap, noneCap2]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h56 : (fsp + 16#64) + 40#64 = fsp + 56#64 := by bv_lin
    have h64 : (fsp + 56#64) + 8#64 = fsp + 64#64 := by bv_lin
    rw [h24, h56, h64]; exact Entails.of_eq (by ac_rfl)
  v1StateMerge_fetches b H 1652 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

theorem v1State_tag6_copy_err {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp336 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1672#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_ne : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1708#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ memRegion (fsp + 16#64) 96 ∗
          words12At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          ((fsp + 336#64) ↦₆₄ mPtr) ∗ Frame) ∧
        s2.sp = s.sp ∧ s2.v1TraceEq s ∧
        s2.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := words12At_entails_memRegion_96 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  have hcbz : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
  rw [memRegion_96_eq_words12 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  v1StateMerge_fetches b H 1672 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words12At, words5At, words7At] at hfold16 ⊢
  wp_steps
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag6_copy_ok {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp336 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1672#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_eq : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2832#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ mPtr) ∗ Frame) ∧
        s2.sp = s.sp ∧ s2.v1TraceEq s ∧
        s2.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s2.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s2.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        s2.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s2.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s2.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s2.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s2.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s2.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s2.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s2.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := words12At_entails_memRegion_96 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  conv =>
    arg 4
    rw [memRegion_96_eq_words12 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  v1StateMerge_fetches b H 1672 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words12At, words5At, words7At] at hfold240 ⊢
  wp_steps
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

theorem v1State_tag6_pre_drop {b : BitVec 64}
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2832#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2860#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 480#64) 96 ∗ Frame)
      (fun s3 P3 =>
        (P3 ⊢ memRegion (fsp + 16#64) 96 ∗
          words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗ Frame) ∧
        s3.sp = s.sp ∧ s3.v1TraceEq s ∧
        s3.readReg64 (Reg.gpr 0#5) = mPtr ∧
        s3.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s3.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s3.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        s3.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s3.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s3.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s3.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s3.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s3.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s3.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s3.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := words12At_entails_memRegion_96 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  rw [memRegion_96_eq_words12 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  v1StateMerge_fetches b H 2832 28
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  dsimp only [words12At, words5At, words7At] at hfold16 ⊢
  wp_steps
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag6_post_drop {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s : State} {fsp mPtr : BitVec 64} {is_old : Option V1State.InnerState}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hb_align : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2860#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) s
      (optProtoInnerStateAt A mPtr is_old ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        Frame)
      (fun s4 P4 =>
        (P4 ⊢ (mPtr ↦₆₄ 0x8000000000000005#64) ∗
          words12At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          memRegion (mPtr + 104#64) 120 ∗
          memRegion (fsp + 480#64) 96 ∗
          A.pool ∗ optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        s4.sp = s.sp ∧ s4.v1TraceEq s ∧
        s4.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s4.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s4.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        s4.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s4.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s4.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s4.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s4.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s4.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s4.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s4.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := words12At_entails_memRegion_96 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  simp only [dropOptProtoInnerStateSpec] at hDropInner
  v1StateMerge_fetches b H 2860 60
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag6_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done

theorem v1State_tag6_inplace {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hNhCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x29cc#64)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {nh : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.noHeaderReceived nh))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 604#64)
    (hcont : V1StateTagCont img b A H s0 x R 6 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000005#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) - 0x8000000000000005#64 != 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2' : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000005#64) = false := by
    rw [hx9_eq]; decide
  have hpd_bound : OptPolyDecoderBound nh.receivingHdr rest.length := by
    simpa only [hm_is] using noHeaderReceived_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  v1StateMerge_fetches b H 604 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0x29cc#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, nh, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 644#64) hNhCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedNoHeaderReceivedMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpd_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyDecoderBound nh.receivingHdr rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedNoHeaderReceivedMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag6 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hnh_res : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) nh rest 99).toOption with
  | none =>
    rw [hnh_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := entry + 2700#64)
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro nh'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000005#64) ∗
        chunkedNoHeaderReceivedPBAt A (x.msgPtr + 8#64) nh' ∗ memRegion (x.msgPtr + 104#64) 120 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedNoHeaderReceivedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.noHeaderReceived nh'))
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
    rcases p with ⟨nh', rest'⟩
    rw [hnh_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hnh_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.noHeaderReceived nh')) :=
      innerStatePolyBound_of_noHeaderReceived hpd_bound hnh_res
    refine SepWPp.of_sepWP_img (mid := entry + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.noHeaderReceived nh') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.noHeaderReceived nh') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1State_tag6_at_1652 {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hNhCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x29cc#64)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img))
    (hDropNh : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe4fc#64)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ nh, m.innerState ≠ some (.noHeaderReceived nh))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1652#64)
    (hcont : V1StateTagCont img b A H s0 x R 6 m rest iwt limit) :
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
  have hpd_none : OptPolyDecoderBound
      ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived).receivingHdr rest.length :=
    optPolyDecoderBound_none h56
  refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x29cc#64) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPre, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag6_temp fsp, memRegion_96_split_tag6_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp336
  apply SepWP.exists_elim; intro w_sp56
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 32 ∗
      ((fsp + 56#64) ↦₆₄ w_sp56) ∗ memRegion (fsp + 64#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗
        memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
        memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesAt b ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag6_setup (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23 hx27) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_inImage (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived), x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1672#64) hNhCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedNoHeaderReceivedMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpd_none⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyDecoderBound ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived).receivingHdr rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedNoHeaderReceivedMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 6) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt)
        ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.noHeaderReceived v') }, rest')) := by
    rw [v1State_mergeField_tag6]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | noHeaderReceived nh => exact absurd h (hm_not nh)
      | _ => rfl
  cases hnh_res : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt)
      ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) rest 99).toOption with
  | none =>
    rw [hnh_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64)
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro nh'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hnh_words : chunkedNoHeaderReceivedPBAt A (fsp + 16#64) nh' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
          words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          tag6CapHeap A 0 nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
      refine Entails.trans (chunkedNoHeaderReceivedPBAt_entails_cap_zero A (fsp + 16#64) nh') ?_
      dsimp only [chunkedNoHeaderReceivedPBCapAt]
      rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
      exact tag6_extract_words A (fsp + 16#64) 0 nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hnh_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_dropStack48 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag6CapHeap A 0 nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      A.pool ∗ stackAt fsp dropStack48 ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack48 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
      memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
      memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesAt b ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_copy_err hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (tag6_words_entails_protoChunkedNoHeaderReceived A (fsp + 240#64) nh'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedNoHeaderReceivedAt A (fsp + 240#64) nh' ∗
        A.pool ∗ stackAt fsp dropStack48 ∗
        (memRegion (fsp + 16#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack48 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
          memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
          memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesAt b ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_err_1708 hDropNh hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag6_temp fsp x.msgPtr) (by sep_focus)
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
    rcases p with ⟨nh', rest'⟩
    rw [hnh_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hnh_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.noHeaderReceived nh')) :=
      innerStatePolyBound_of_noHeaderReceived (bs := rest)
        (m := ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived))
        (optPolyDecoderBound_none h56) hnh_res
    refine SepWPp.of_sepWP_img (mid := (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    have hnh_words : chunkedNoHeaderReceivedPBCapAt A (fsp + 16#64) rest'.length nh' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
          words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          tag6CapHeap A rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
      dsimp only [chunkedNoHeaderReceivedPBCapAt]
      rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
      exact tag6_extract_words A (fsp + 16#64) rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hnh_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag6CapHeap A rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTableAt b ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
      memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 576#64) 144 ∗
      v1StateMergeJumpTableExpanded b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗
        (memRegion (fsp + 480#64) 96 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesAt, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_copy_ok hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 96 ∗ Frame_ok) =
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 480#64) 96 ∗
        (memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1State_tag6_pre_drop hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTableAt b ∗
        stackAt fsp dropStack96 ∗
        words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        (memRegion (fsp + 16#64) 96 ∗ memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
          tag6CapHeap A rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
          memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 576#64) 144 ∗
          v1StateMergeJumpTableExpanded b ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_post_drop hDropInner hfsp_align hb_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag6_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (tag6_reconstruct_innerState A x.msgPtr rest'.length nh'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.noHeaderReceived nh') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPre, v1StateJumpTablesAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.noHeaderReceived nh') } rest' s4 hm_field hpoly' hrest'_le
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
       hx29_4.trans hfsp720⟩ hinv4

private theorem v1State_tag6_branch_1652 {img : Obj.Image} {b : BitVec 64}
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ nh, m.innerState ≠ some (.noHeaderReceived nh))
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 604#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHyp img b H s0 x m rest iwt limit s' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 1652#64 →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hb_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  v1StateMerge_fetches b H 604 28
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 1652#64) hinv ?_
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
  | some st =>
    have hst_ne : ∀ nh, st ≠ .noHeaderReceived nh := fun nh h => hm_not nh (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some st) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have ⟨hbr2, hbr2'⟩ := discrFull_other_tag6 hst_ne hx9_s
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

/-- Combined step theorem for Tag 6 (`NoHeaderReceived`, `tag = 6`, entry `+604`). -/
theorem v1State_tag6_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hNhCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0x29cc#64)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img))
    (hDropNh : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffe4fc#64)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropInner : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 0xffffffffffffd8ec#64)
      (dropOptProtoInnerStateSpec A b))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHyp img b H s0 x m rest iwt limit s)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr v1StateMergeName + 604#64)
    (hcont : V1StateTagCont img b A H s0 x R 6 m rest iwt limit) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergeSpec A b) x R s0) (WppPanic R s0) := by
  by_cases hm : ∃ nh, m.innerState = some (.noHeaderReceived nh)
  · obtain ⟨nh, hm_is⟩ := hm
    exact v1State_tag6_inplace hNhCall hm_is hentry hpc hcont
  · refine v1State_tag6_branch_1652 (fun nh h => hm ⟨nh, h⟩) hentry hpc (fun s' hentry' hpc' => ?_)
    exact v1State_tag6_at_1652 hNhCall hDropNh hDropInner (fun nh h => hm ⟨nh, h⟩) hentry' hpc' hcont

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

theorem v1State_tag6_err_1708_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    {s : State} {fsp : BitVec 64} {nh : V1State.Chunked.NoHeaderReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1708#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedNoHeaderReceivedAt A (fsp + 240#64) nh ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 96 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [dropProtoChunkedNoHeaderReceivedSpec] at hDropNh
  wp_steps; wp_apply
  dsimp only [protoChunkedNoHeaderReceivedSize]
  wp_steps; wp_done

theorem v1State_tag6_setup_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp56 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1652#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 32 ∗
        ((fsp + 56#64) ↦₆₄ w_sp56) ∗ memRegion (fsp + 64#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedNoHeaderReceivedPBCapAt A (fsp + 16#64) restLen
          ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1672#64 ∧
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
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 32 ∗
      ((fsp + 56#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 64#64) 48 ⊢
      chunkedNoHeaderReceivedPBCapAt A (fsp + 16#64) restLen
        ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) := by
    dsimp only [chunkedNoHeaderReceivedPBCapAt, optPolynomialDecoderPBAt,
      optNoHeaderReceivedPBCapAt, noneCap, noneCap2]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h56 : (fsp + 16#64) + 40#64 = fsp + 56#64 := by bv_lin
    have h64 : (fsp + 56#64) + 8#64 = fsp + 64#64 := by bv_lin
    rw [h24, h56, h64]; exact Entails.of_eq (by ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

theorem v1State_tag6_copy_err_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp336 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1672#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_ne : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1708#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ memRegion (fsp + 16#64) 96 ∗
          words12At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          ((fsp + 336#64) ↦₆₄ mPtr) ∗ Frame) ∧
        s2.sp = s.sp ∧ s2.v1TraceEq s ∧
        s2.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := words12At_entails_memRegion_96 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  have hcbz : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
  rw [memRegion_96_eq_words12 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold16 ⊢
  wp_steps
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag6_copy_ok_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp336 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1672#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0_eq : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2832#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ Frame)
      (fun s2 P2 =>
        (P2 ⊢ words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ mPtr) ∗ Frame) ∧
        s2.sp = s.sp ∧ s2.v1TraceEq s ∧
        s2.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s2.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s2.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        s2.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s2.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s2.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s2.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s2.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s2.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s2.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s2.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := words12At_entails_memRegion_96 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  conv =>
    arg 4
    rw [memRegion_96_eq_words12 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold240 ⊢
  wp_steps
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

theorem v1State_tag6_pre_drop_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2832#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2860#64) s
      (words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 480#64) 96 ∗ Frame)
      (fun s3 P3 =>
        (P3 ⊢ memRegion (fsp + 16#64) 96 ∗
          words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗ Frame) ∧
        s3.sp = s.sp ∧ s3.v1TraceEq s ∧
        s3.readReg64 (Reg.gpr 0#5) = mPtr ∧
        s3.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s3.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s3.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        s3.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s3.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s3.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s3.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s3.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s3.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s3.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s3.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := words12At_entails_memRegion_96 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  rw [memRegion_96_eq_words12 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold16 ⊢
  wp_steps
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1State_tag6_post_drop_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s : State} {fsp mPtr : BitVec 64} {is_old : Option V1State.InnerState}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
   
    (hpc : s.pc = (blkPl_298).base + 2860#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is_old ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        Frame)
      (fun s4 P4 =>
        (P4 ⊢ (mPtr ↦₆₄ 0x8000000000000005#64) ∗
          words12At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          memRegion (mPtr + 104#64) 120 ∗
          memRegion (fsp + 480#64) 96 ∗
          A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        s4.sp = s.sp ∧ s4.v1TraceEq s ∧
        s4.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s4.readReg64 (Reg.gpr 20#5) = mPtr ∧
        s4.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        s4.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s4.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        s4.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s4.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s4.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s4.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s4.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s4.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := words12At_entails_memRegion_96 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps; wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [memRegion_224_split_tag6_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d11
  apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d5
  dsimp only [words12At, words5At, words7At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done

theorem v1State_tag6_inplace_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {nh : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.noHeaderReceived nh))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 604#64)
    (hcont : V1StateTagContPlaced A H s0 x R 6 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000005#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) - 0x8000000000000005#64 != 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2' : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000005#64) = false := by
    rw [hx9_eq]; decide
  have hpd_bound : OptPolyDecoderBound nh.receivingHdr rest.length := by
    simpa only [hm_is] using noHeaderReceived_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 308) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, nh, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 644#64) hNhCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedNoHeaderReceivedMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpd_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyDecoderBound nh.receivingHdr rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedNoHeaderReceivedMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag6 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hnh_res : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) nh rest 99).toOption with
  | none =>
    rw [hnh_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro nh'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000005#64) ∗
        chunkedNoHeaderReceivedPBAt A (x.msgPtr + 8#64) nh' ∗ memRegion (x.msgPtr + 104#64) 120 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedNoHeaderReceivedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.noHeaderReceived nh'))
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
    rcases p with ⟨nh', rest'⟩
    rw [hnh_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hnh_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.noHeaderReceived nh')) :=
      innerStatePolyBound_of_noHeaderReceived hpd_bound hnh_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.noHeaderReceived nh') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.noHeaderReceived nh') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1State_tag6_at_1652_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A)))
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ nh, m.innerState ≠ some (.noHeaderReceived nh))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1652#64)
    (hcont : V1StateTagContPlaced A H s0 x R 6 m rest iwt limit) :
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
  have hpd_none : OptPolyDecoderBound
      ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived).receivingHdr rest.length :=
    optPolyDecoderBound_none h56
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 308) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag6_temp fsp, memRegion_96_split_tag6_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp336
  apply SepWP.exists_elim; intro w_sp56
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 32 ∗
      ((fsp + 56#64) ↦₆₄ w_sp56) ∗ memRegion (fsp + 64#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗
        memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
        memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag6_setup_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23 hx27) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived), x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1672#64) hNhCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedNoHeaderReceivedMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hpd_none⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        OptPolyDecoderBound ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived).receivingHdr rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedNoHeaderReceivedMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 6) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt)
        ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.noHeaderReceived v') }, rest')) := by
    rw [v1State_mergeField_tag6]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | noHeaderReceived nh => exact absurd h (hm_not nh)
      | _ => rfl
  cases hnh_res : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt)
      ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived) rest 99).toOption with
  | none =>
    rw [hnh_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro nh'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hnh_words : chunkedNoHeaderReceivedPBAt A (fsp + 16#64) nh' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
          words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          tag6CapHeap A 0 nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
      refine Entails.trans (chunkedNoHeaderReceivedPBAt_entails_cap_zero A (fsp + 16#64) nh') ?_
      dsimp only [chunkedNoHeaderReceivedPBCapAt]
      rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
      exact tag6_extract_words A (fsp + 16#64) 0 nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hnh_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_dropStack48 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag6CapHeap A 0 nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      A.pool ∗ stackAt fsp dropStack48 ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack48 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
      memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
      memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_copy_err_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (tag6_words_entails_protoChunkedNoHeaderReceived A (fsp + 240#64) nh'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedNoHeaderReceivedAt A (fsp + 240#64) nh' ∗
        A.pool ∗ stackAt fsp dropStack48 ∗
        (memRegion (fsp + 16#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack48 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
          memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 480#64) 96 ∗
          memRegion (fsp + 576#64) 144 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_err_1708_placed hDropNh hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag6_temp fsp x.msgPtr) (by sep_focus)
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
    rcases p with ⟨nh', rest'⟩
    rw [hnh_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hnh_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.noHeaderReceived nh')) :=
      innerStatePolyBound_of_noHeaderReceived (bs := rest)
        (m := ({ uc := none, receivingHdr := none } : V1State.Chunked.NoHeaderReceived))
        (optPolyDecoderBound_none h56) hnh_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedNoHeaderReceivedMergeSpec, hnh_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    have hnh_words : chunkedNoHeaderReceivedPBCapAt A (fsp + 16#64) rest'.length nh' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
          words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          tag6CapHeap A rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 := by
      dsimp only [chunkedNoHeaderReceivedPBCapAt]
      rw [optNoHeaderReceivedPBCapAt_eq_optUnchunked2]
      exact tag6_extract_words A (fsp + 16#64) rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
    apply SepWP.fold hnh_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag6CapHeap A rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
      memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 576#64) 144 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ w_sp336) ∗
        (memRegion (fsp + 480#64) 96 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_copy_ok_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 96 ∗ Frame_ok) =
      words12At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        memRegion (fsp + 480#64) 96 ∗
        (memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1State_tag6_pre_drop_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        words12At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
        (memRegion (fsp + 16#64) 96 ∗ memRegion (fsp + 240#64) 96 ∗ ((fsp + 336#64) ↦₆₄ x.msgPtr) ∗
          tag6CapHeap A rest'.length nh'.receivingHdr (nh'.uc.map fun u => (u.epoch, u.auth))
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 112#64) 128 ∗
          memRegion (fsp + 344#64) 136 ∗ memRegion (fsp + 576#64) 144 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag6_post_drop_placed hDropInner hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag6_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (tag6_reconstruct_innerState A x.msgPtr rest'.length nh'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.noHeaderReceived nh') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.noHeaderReceived nh') } rest' s4 hm_field hpoly' hrest'_le
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
       hx29_4.trans hfsp720⟩ hinv4

private theorem v1State_tag6_branch_1652_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ nh, m.innerState ≠ some (.noHeaderReceived nh))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 604#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1652#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1652#64) hinv ?_
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
  | some st =>
    have hst_ne : ∀ nh, st ≠ .noHeaderReceived nh := fun nh h => hm_not nh (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some st) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have ⟨hbr2, hbr2'⟩ := discrFull_other_tag6 hst_ne hx9_s
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

/-- Combined step theorem for Tag 6 (`NoHeaderReceived`, `tag = 6`, entry `+604`). -/
theorem v1State_tag6_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hNhCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 308)
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A)))
    (hDropNh : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 284)
      (dropProtoChunkedNoHeaderReceivedSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec A))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 604#64)
    (hcont : V1StateTagContPlaced A H s0 x R 6 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hm : ∃ nh, m.innerState = some (.noHeaderReceived nh)
  · obtain ⟨nh, hm_is⟩ := hm
    exact v1State_tag6_inplace_placed hNhCall hm_is hentry hpc hcont
  · refine v1State_tag6_branch_1652_placed (fun nh h => hm ⟨nh, h⟩) hentry hpc (fun s' hentry' hpc' => ?_)
    exact v1State_tag6_at_1652_placed hNhCall hDropNh hDropInner (fun nh h => hm ⟨nh, h⟩) hentry' hpc' hcont


end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
