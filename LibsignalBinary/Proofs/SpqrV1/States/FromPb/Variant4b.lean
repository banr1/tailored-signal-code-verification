/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`) — Part B

Header unpacking and straight-line branches at `+248`, `+2228`, and `+2308`.
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

theorem v4b_stackAt_encoderFromPbStack_to_ekSent (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp ekSentCt1ReceivedFromPbStack ∗ memRegion (fsp - 5152#64) 848 := by
  have h := ProofLib.stackAt_split_bottom fsp ekSentCt1ReceivedFromPbStack 848 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 848 ∗ stackAt fsp ekSentCt1ReceivedFromPbStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v4b_stackAt_ekSent_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp ekSentCt1ReceivedFromPbStack ∗ memRegion (fsp - 5152#64) 848 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp ekSentCt1ReceivedFromPbStack 848 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 848 ∗ stackAt fsp ekSentCt1ReceivedFromPbStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v4b_optProtoInnerStateAt_ekSentCt1Received_eq (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.EkSentCt1Received) :
    optProtoInnerStateAt A pbA (some (.ekSentCt1Received s)) =
      (pbA ↦₆₄ 0x8000000000000004#64) ∗
      optProtoUnchunkedEkSentCt1ReceivedAt A (pbA + 8#64) s.uc ∗
      optProtoPolynomialDecoderAt A (pbA + 112#64) (s.receivingCt2.map pbToProtoPolyDecoder) ∗
      memRegion (pbA + 152#64) 72 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkSentCt1ReceivedAt]
  have h112 : (pbA + 8#64) + 104#64 = pbA + 112#64 := by bv_omega
  rw [h112]
  ac_rfl

theorem v4b_states_from_pb_ekSentCt1Received_ptsNeeded_ne (F : ShaCompress)
    (uc : Option V1State.Unchunked.EkSentCt1Received) (d : PolynomialDecoder)
    (hne : d.ptsNeeded ≠ 80#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekSentCt1Received { uc := uc, receivingCt2 := some d }) } =
      .error (.err .msgDecode) := by
  have hsub : Chunked.SendEk.EkSentCt1Received.from_pb spqrPolyApi (spqrAuthApi F)
      { uc := uc, receivingCt2 := some d } = .error (.err .msgDecode) := by
    simp [Chunked.SendEk.EkSentCt1Received.from_pb,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    intro h
    have h80 : d.ptsNeeded.toNat = 80 := h
    exact absurd (BitVec.eq_of_toNat_eq h80) hne
  simp [States.from_pb, hsub, Functor.map, Except.map]

theorem v4b_states_from_pb_ekSentCt1Received_none_uc_none_dec (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekSentCt1Received { uc := none, receivingCt2 := none }) } =
      .error (.err .stateDecode) := rfl

theorem v4b_states_from_pb_ekSentCt1Received_none_uc_some_dec (F : ShaCompress)
    (d : PolynomialDecoder) (heq : d.ptsNeeded = 80#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekSentCt1Received { uc := none, receivingCt2 := some d }) } =
      .error (.err .stateDecode) := by
  simp [States.from_pb, Chunked.SendEk.EkSentCt1Received.from_pb, heq,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  rfl

theorem v4b_states_from_pb_ekSentCt1Received_some_uc_none_dec (F : ShaCompress)
    (u : V1State.Unchunked.EkSentCt1Received) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekSentCt1Received { uc := some u, receivingCt2 := none }) } =
      match Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u with
      | .error e => .error e
      | .ok _ => .error (.err .stateDecode) := by
  simp [States.from_pb, Chunked.SendEk.EkSentCt1Received.from_pb,
    decoderFromPbStateDecode_none, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u <;> rfl

theorem v4b_states_from_pb_ekSentCt1Received_some_uc_some_dec (F : ShaCompress)
    (u : V1State.Unchunked.EkSentCt1Received) (d : PolynomialDecoder)
    (heq : d.ptsNeeded = 80#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ekSentCt1Received { uc := some u, receivingCt2 := some d }) } =
      match Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u with
      | .error e => .error e
      | .ok uc =>
        match decoderFromPbResult (pbToProtoPolyDecoder d) with
        | .error _ => .error (.err .stateDecode)
        | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec }) := by
  simp [States.from_pb, Chunked.SendEk.EkSentCt1Received.from_pb, heq,
    decoderFromPbStateDecode_some,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u with
  | error e => rfl
  | ok uc =>
    cases decoderFromPbResult (pbToProtoPolyDecoder d) <;> rfl

/-- Header cells of a 40-byte `Option<ProtoPolynomialDecoder>` at `a`, matching the exact access widths
    at `+248..+288` and `+2420..+2464` (`64`-bit at `+0, +8, +16, +32`, `32`-bit at `+24, +28`). -/
def v4b_optProtoPolyDecoderWordsAt (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗ ((a + 32#64) ↦₆₄ w32)

/-- Address-independent heap and pure constraints for `Option<ProtoPolynomialDecoder>`. -/
def v4b_optProtoPolyDecoderHeap (A : RustAlloc) :
    Option ProtoPolynomialDecoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 32 → BitVec 32 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, d24, d28, w32 =>
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 w32)⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w8 (w0.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
       memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))

theorem v4b_optProtoPolyDecoderWordsAt_entails_40
    (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v4b_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ⊢ memRegion a 40 := by
  unfold v4b_optProtoPolyDecoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v4b_optProtoPolyDecoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A a optDec ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ d24 : BitVec 32, ∃∗ d28 : BitVec 32, ∃∗ w32 : BitVec 64,
        v4b_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
        v4b_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 := by
  cases optDec with
  | none =>
    dsimp only [optProtoPolynomialDecoderAt, optProtoPolynomialDecoderNoneTailSize,
      v4b_optProtoPolyDecoderHeap]
    have hsplit : memRegion (a + 8#64) 32 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ d24 : BitVec 32, (a + 24#64) ↦₃₂ d24) ∗
        (∃∗ d28 : BitVec 32, (a + 28#64) ↦₃₂ d28) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem32_entails _) <| split_step (mem32_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro d28
    apply Entails.sepExists_elim; intro d24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right d24
        (Entails.sepExists_right d28 (Entails.sepExists_right w32 ?_)))))
    unfold v4b_optProtoPolyDecoderWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    unfold optProtoPolynomialDecoderAt protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
      vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
      protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
      protoPolynomialDecoderPadSize Poly.vecHeaderBytes
    rw [ProofLib.memRegion_eq_exists_bytes (a + 0x21#64) 7 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      Nat.reducePow, Nat.reduceLeDiff, true_and]
    apply Entails.sepExists_elim; intro bs
    apply Entails.sepExists_elim; intro c1
    apply Entails.sepExists_elim; intro p1
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜bs.length = 7⌝ ∗
      ⌜pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
      ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
       (((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 33#64) ↦ₛ bs)) ∗
       (if c1 = 0#64 then emp
        else A.live p1 (c1.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 p1 pb.pts ∗
          memRegion (p1 + BitVec.ofNat 64 (pb.pts.length * 24)) ((c1.toNat - pb.pts.length) * 24))) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    apply Entails.pure_left; rintro ⟨hle, hcap, hp_ne⟩
    have h8 : (boolByte pb.isComplete :: bs).length = 8 := by simp [hlen]
    obtain ⟨w32, hw32⟩ := ProofLib.exists_unpack64_of_length_8 h8
    have hcell32 : ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 33#64) ↦ₛ bs) =
        ((a + 32#64) ↦₆₄ w32) := by
      have h := ProofLib.pointsToBytes_cons (a + 32#64) (boolByte pb.isComplete) bs
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
      rw [← h, hw32, ← ProofLib.pointsTo64_eq_pointsToBytes]
    rw [hcell32]
    refine Entails.sepExists_right c1 (Entails.sepExists_right p1
      (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
        (Entails.sepExists_right pb.ptsNeeded
          (Entails.sepExists_right pb.polys
            (Entails.sepExists_right w32 ?_)))))
    dsimp only [v4b_optProtoPolyDecoderWordsAt, v4b_optProtoPolyDecoderHeap]
    have hpure :
        BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
        pb.ptsNeeded = pb.ptsNeeded ∧ pb.polys = pb.polys ∧
        pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧
        p1 ≠ 0#64 ∧
        (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 w32) :=
      ⟨rfl, rfl, rfl, hle, hcap, hp_ne, ⟨bs, hlen, hw32⟩⟩
    exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v4b_protoPolyDecoderAt_pack (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v4b_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
      v4b_optProtoPolyDecoderHeap A (some pb) w0 w8 w16 d24 d28 w32 ⊢
    protoPolynomialDecoderAt A a pb := by
  dsimp only [v4b_optProtoPolyDecoderWordsAt, v4b_optProtoPolyDecoderHeap]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 w32)⌝ ∗
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗ ((a + 32#64) ↦₆₄ w32) ∗
     (if w0 = 0#64 then emp
      else A.live w8 (w0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, ⟨bs, hlen, hw32⟩⟩
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize Poly.vecHeaderBytes
  have hcell32 : ((a + 32#64) ↦₆₄ w32) =
      ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ ((a + 0x21#64) ↦ₛ bs) := by
    have h := ProofLib.pointsToBytes_cons (a + 32#64) (boolByte pb.isComplete) bs
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    rw [ProofLib.pointsTo64_eq_pointsToBytes, ← hw32, h]
  rw [hcell32]
  have hpad : ((a + 0x21#64) ↦ₛ bs) ⊢ memRegion (a + 0x21#64) 7 := by
    rw [← hlen]; exact ProofLib.pointsToBytes_entails_memRegion (a + 0x21#64) bs
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right hpad))))))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
     (if w0 = 0#64 then emp
      else A.live w8 (w0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))) ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (a + 0x21#64) 7 by ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8 ?_)
  have hpure : pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0#64 := ⟨hle, hcap, hp_ne⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

/-- 13 64-bit words (`104` bytes) of `Option<ProtoUnchunkedEkSentCt1Received>` at `a`. -/
def v4b_optProtoUcWordsAt
    (a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48) ∗ ((a + 56#64) ↦₆₄ w56) ∗ ((a + 64#64) ↦₆₄ w64) ∗
  ((a + 72#64) ↦₆₄ w72) ∗ ((a + 80#64) ↦₆₄ w80) ∗ ((a + 88#64) ↦₆₄ w88) ∗
  ((a + 96#64) ↦₆₄ w96)

theorem v4b_optProtoUcWordsAt_entails_104
    (a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v4b_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ⊢
      memRegion a 104 := by
  unfold v4b_optProtoUcWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
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
    Drop.pointsTo64_entails_memRegion _ _

def v4b_vecU8Heap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63⌝ ∗
  vecU8Payload A cap ptr bs

theorem v4b_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v4b_vecU8Heap A bs cap ptr len := by
  refine Entails.trans (vecU8_unpack A a bs) ?_
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; rintro ⟨_, hcap⟩
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  unfold v4b_vecU8Heap
  have hpure : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63 :=
    ⟨rfl, hcap⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v4b_vecU8_pack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
      v4b_vecU8Heap A bs cap ptr len ⊢
    vecU8 A a bs := by
  unfold v4b_vecU8Heap
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜len = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63⌝ ∗
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
     vecU8Payload A cap ptr bs) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨rfl, _⟩
  exact vecU8_of_header_payload A a cap ptr bs

theorem v4b_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v4b_vecU8Heap A bs cap ptr len ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  unfold v4b_vecU8Heap
  apply Entails.pure_left; rintro ⟨_, hcap⟩
  exact Entails.pure_right hcap (vecU8Payload_entails_dealloc A cap ptr bs)

def v4b_optProtoAuthHeap (A : RustAlloc) :
    Option ProtoAuthenticator →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w48, _, _, _, _, _ => ⌜w48 = noneCap⌝
  | some auth, w48, w56, w64, w72, w80, w88 =>
    v4b_vecU8Heap A auth.rootKey w48 w56 w64 ∗
    v4b_vecU8Heap A auth.macKey w72 w80 w88

def v4b_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.EkSentCt1Received →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some u, w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96 =>
    v4b_vecU8Heap A u.dk w0 w8 w16 ∗
    v4b_vecU8Heap A u.ct1 w24 w32 w40 ∗
    v4b_optProtoAuthHeap A u.auth w48 w56 w64 w72 w80 w88 ∗
    ⌜w96 = u.epoch⌝

theorem v4b_optProtoAuthAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
         ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
        v4b_optProtoAuthHeap A optAuth w0 w8 w16 w24 w32 w40 := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v4b_optProtoAuthHeap]
    have hsplit : memRegion (a + 8#64) 40 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40 ?_)))))
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v4b_optProtoAuthHeap]
    refine Entails.trans
      (sepConj_mono (v4b_vecU8_unpack A a auth.rootKey)
        (v4b_vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40 ?_)))))
    exact Entails.of_eq (by ac_rfl)

theorem v4b_optProtoAuthAt_pack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (w0 w8 w16 w24 w32 w40 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
     ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
      v4b_optProtoAuthHeap A optAuth w0 w8 w16 w24 w32 w40 ⊢
    optProtoAuthenticatorAt A a optAuth := by
  cases optAuth with
  | none =>
    dsimp only [optProtoAuthenticatorAt, v4b_optProtoAuthHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜w0 = noneCap⌝ ∗
      ((a ↦₆₄ w0) ∗
       (((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40))) by ac_rfl)) ?_
    apply Entails.pure_left; rintro rfl
    refine sepConj_mono_right ?_
    rw [ProofLib.memRegion_cells (a + 8#64) 5 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w8 (Entails.sepExists_right w16
      (Entails.sepExists_right w24 (Entails.sepExists_right w32
        (Entails.sepExists_right w40 (Entails.refl _)))))
  | some auth =>
    dsimp only [optProtoAuthenticatorAt, protoAuthenticatorAt, v4b_optProtoAuthHeap]
    have hmk := v4b_vecU8_pack A (a + 24#64) auth.macKey w24 w32 w40
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmk
    refine Entails.trans (Entails.of_eq (show _ =
      (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16)) ∗
       v4b_vecU8Heap A auth.rootKey w0 w8 w16) ∗
      ((((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
       v4b_vecU8Heap A auth.macKey w24 w32 w40) by ac_rfl)) ?_
    exact sepConj_mono (v4b_vecU8_pack A a auth.rootKey w0 w8 w16) hmk

theorem v4b_optProtoUcAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received) :
    optProtoUnchunkedEkSentCt1ReceivedAt A a optUc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64,
      ∃∗ w96 : BitVec 64,
        v4b_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        v4b_optProtoUcHeap A optUc w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 := by
  cases optUc with
  | none =>
    dsimp only [optProtoUnchunkedEkSentCt1ReceivedAt, v4b_optProtoUcHeap]
    have hsplit : memRegion (a + 8#64) 96 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) ∗
        (∃∗ w48 : BitVec 64, (a + 48#64) ↦₆₄ w48) ∗
        (∃∗ w56 : BitVec 64, (a + 56#64) ↦₆₄ w56) ∗
        (∃∗ w64 : BitVec 64, (a + 64#64) ↦₆₄ w64) ∗
        (∃∗ w72 : BitVec 64, (a + 72#64) ↦₆₄ w72) ∗
        (∃∗ w80 : BitVec 64, (a + 80#64) ↦₆₄ w80) ∗
        (∃∗ w88 : BitVec 64, (a + 88#64) ↦₆₄ w88) ∗
        (∃∗ w96 : BitVec 64, (a + 96#64) ↦₆₄ w96) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w96
    apply Entails.sepExists_elim; intro w88
    apply Entails.sepExists_elim; intro w80
    apply Entails.sepExists_elim; intro w72
    apply Entails.sepExists_elim; intro w64
    apply Entails.sepExists_elim; intro w56
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 (Entails.sepExists_right w56
            (Entails.sepExists_right w64 (Entails.sepExists_right w72
              (Entails.sepExists_right w80 (Entails.sepExists_right w88
                (Entails.sepExists_right w96 ?_))))))))))))
    unfold v4b_optProtoUcWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some u =>
    dsimp only [optProtoUnchunkedEkSentCt1ReceivedAt, protoUnchunkedEkSentCt1ReceivedAt,
      v4b_optProtoUcHeap]
    refine Entails.trans
      (sepConj_mono (v4b_vecU8_unpack A a u.dk)
        (sepConj_mono (v4b_vecU8_unpack A (a + 24#64) u.ct1)
          (sepConj_mono_left (v4b_optProtoAuthAt_unpack A (a + 48#64) u.auth)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w56
    apply Entails.sepExists_elim; intro w64
    apply Entails.sepExists_elim; intro w72
    apply Entails.sepExists_elim; intro w80
    apply Entails.sepExists_elim; intro w88
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 (Entails.sepExists_right w56
            (Entails.sepExists_right w64 (Entails.sepExists_right w72
              (Entails.sepExists_right w80 (Entails.sepExists_right w88
                (Entails.sepExists_right u.epoch ?_))))))))))))
    dsimp only [v4b_optProtoUcWordsAt]
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v4b_protoUcAt_pack (A : RustAlloc) (a : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v4b_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ∗
      v4b_optProtoUcHeap A (some u) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ⊢
    protoUnchunkedEkSentCt1ReceivedAt A a u := by
  dsimp only [v4b_optProtoUcWordsAt, v4b_optProtoUcHeap, protoUnchunkedEkSentCt1ReceivedAt]
  have hct1 := v4b_vecU8_pack A (a + 24#64) u.ct1 w24 w32 w40
  have hauth := v4b_optProtoAuthAt_pack A (a + 48#64) u.auth w48 w56 w64 w72 w80 w88
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hct1 hauth
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w96 = u.epoch⌝ ∗
    ((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16)) ∗
      v4b_vecU8Heap A u.dk w0 w8 w16) ∗
     ((((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40)) ∗
      v4b_vecU8Heap A u.ct1 w24 w32 w40) ∗
     ((((a + 48#64) ↦₆₄ w48) ∗ ((a + 56#64) ↦₆₄ w56) ∗ ((a + 64#64) ↦₆₄ w64) ∗
       ((a + 72#64) ↦₆₄ w72) ∗ ((a + 80#64) ↦₆₄ w80) ∗ ((a + 88#64) ↦₆₄ w88)) ∗
      v4b_optProtoAuthHeap A u.auth w48 w56 w64 w72 w80 w88) ∗
     ((a + 96#64) ↦₆₄ w96)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro rfl
  exact sepConj_mono (v4b_vecU8_pack A a u.dk w0 w8 w16)
    (sepConj_mono hct1 (sepConj_mono_left hauth))
/-- Collapse all `pbA` header cells (`224` bytes total) back into `memRegion pbA optProtoInnerStateSize`. -/
theorem v4b_pbA_all_words_entails_memRegion (pbA tag : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64) :
    (pbA ↦₆₄ tag) ∗
      v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
      v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
      memRegion (pbA + 152#64) 72 ⊢
    memRegion pbA optProtoInnerStateSize := by
  dsimp only [optProtoInnerStateSize]
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (v4b_optProtoUcWordsAt_entails_104 _ _ _ _ _ _ _ _ _ _ _ _ _ _) <|
    collapse_step (v4b_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    Entails.refl _

/-- Entry loads at `+248..+292 -> +2228` when `d0 = noneCap` (`receivingCt2 = none`). -/
theorem v4b_step_248_none_to_2228
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2228#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
          Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = noneCap ∧
        TraceCalleeSaved s' s) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 248 48
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat, noneCap] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [v4b_optProtoUcWordsAt, v4b_optProtoPolyDecoderWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Branch at `+2228 -> +4364 -> +5264` when `x22 = noneCap` (`uc = none`). -/
theorem v4b_step_2228_none_to_5264
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2228#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = noneCap) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5264#64) s
      Frame
      (fun s' P' =>
        (P' ⊢ Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧
        s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x26 = 0#64 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s' s) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 2228 8
  states_from_pb_fetches_range b (Rust.withPanics ext) 4364 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat, noneCap] at hpc hx22 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem v4b_ptsNeeded_sub_80_beq_zero_false {d24 : BitVec 32} (hne : d24 ≠ 80#32) :
    (d24 + 0xffffffb0#32 == 0#32) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  apply hne
  bv_omega

/-- Entry loads at `+248..+300 -> +2228` when `d0.toNat < 2^63` and `d24 = 80#32`. -/
theorem v4b_step_248_some_eq_to_2228
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2228#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
          Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = 80#64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  have hd0_ne := cap_add_one_beq_zero_false hd0_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 248 56
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [v4b_optProtoUcWordsAt, v4b_optProtoPolyDecoderWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Entry loads at `+248..+300 -> +304` when `d0.toNat < 2^63` and `d24 ≠ 80#32`. -/
theorem v4b_step_248_some_ne_to_304
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hd24_ne : d24 ≠ 80#32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 304#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
          Frame) ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  have hd0_ne := cap_add_one_beq_zero_false hd0_lt
  have hd24_f := v4b_ptsNeeded_sub_80_beq_zero_false hd24_ne
  states_from_pb_fetches_range b (Rust.withPanics ext) 248 56
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [v4b_optProtoUcWordsAt, v4b_optProtoPolyDecoderWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Copy `uc` words to `fsp + 1392..1496`, spill `d32, d28` to `fsp + 224..236`,
    and branch-with-link at `+2228..+2304 -> +18368` (`ekSentCt1ReceivedFromPb`). -/
theorem v4b_step_2228_some_to_18368
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp pbA out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u : BitVec 64)
    (v224 : BitVec 64) (v232 : BitVec 32)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u56)
    (hx1 : s.readReg64 .x1 = u48)
    (hx8 : s.readReg64 .x8 = u16)
    (hx9 : s.readReg64 .x9 = u40)
    (hx10 : s.readReg64 .x10 = u64)
    (hx11 : s.readReg64 .x11 = u8)
    (hx12 : s.readReg64 .x12 = u32)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx14 : s.readReg64 .x14 = d28.zeroExtend 64)
    (hx15 : s.readReg64 .x15 = d32)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx21 : s.readReg64 .x21 = u24)
    (hx22 : s.readReg64 .x22 = u0)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx25 : s.readReg64 .x25 = u80)
    (hx26 : s.readReg64 .x26 = u72)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 18368#64) s
      (((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
        ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 232#64) ↦₃₂ v232) ∗
        v4b_optProtoUcWordsAt (fsp + 1392#64)
          s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
          v4b_optProtoUcWordsAt (fsp + 1392#64)
            u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = fsp + 1888#64 ∧
        s'.readReg64 .x1 = fsp + 1392#64 ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64 ∧
        TraceCalleeSaved s' s) := by
  have hu0_ne := cap_add_one_beq_zero_false hu0_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 2228 80
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [v4b_optProtoUcWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-- Split `memRegion base 104` into 13 64-bit words `v4b_optProtoUcWordsAt`. -/
theorem v4b_memRegion_104_to_ucWordsAt (base : BitVec 64) :
    memRegion base 104 ⊢
      ∃∗ s0 : BitVec 64, ∃∗ s8 : BitVec 64, ∃∗ s16 : BitVec 64,
      ∃∗ s24 : BitVec 64, ∃∗ s32 : BitVec 64, ∃∗ s40 : BitVec 64,
      ∃∗ s48 : BitVec 64, ∃∗ s56 : BitVec 64, ∃∗ s64 : BitVec 64,
      ∃∗ s72 : BitVec 64, ∃∗ s80 : BitVec 64, ∃∗ s88 : BitVec 64,
      ∃∗ s96 : BitVec 64,
        v4b_optProtoUcWordsAt base s0 s8 s16 s24 s32 s40 s48 s56 s64 s72 s80 s88 s96 := by
  have hsplit : memRegion base 104 ⊢
      (∃∗ s0 : BitVec 64, base ↦₆₄ s0) ∗
      (∃∗ s8 : BitVec 64, (base + 8#64) ↦₆₄ s8) ∗
      (∃∗ s16 : BitVec 64, (base + 16#64) ↦₆₄ s16) ∗
      (∃∗ s24 : BitVec 64, (base + 24#64) ↦₆₄ s24) ∗
      (∃∗ s32 : BitVec 64, (base + 32#64) ↦₆₄ s32) ∗
      (∃∗ s40 : BitVec 64, (base + 40#64) ↦₆₄ s40) ∗
      (∃∗ s48 : BitVec 64, (base + 48#64) ↦₆₄ s48) ∗
      (∃∗ s56 : BitVec 64, (base + 56#64) ↦₆₄ s56) ∗
      (∃∗ s64 : BitVec 64, (base + 64#64) ↦₆₄ s64) ∗
      (∃∗ s72 : BitVec 64, (base + 72#64) ↦₆₄ s72) ∗
      (∃∗ s80 : BitVec 64, (base + 80#64) ↦₆₄ s80) ∗
      (∃∗ s88 : BitVec 64, (base + 88#64) ↦₆₄ s88) ∗
      (∃∗ s96 : BitVec 64, (base + 96#64) ↦₆₄ s96) := by
    exact split_top <|
      split_step0 (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      split_step (mem64_entails _) <| split_step (mem64_entails _) <|
      mem64_entails _
  refine Entails.trans hsplit ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro s96
  apply Entails.sepExists_elim; intro s88
  apply Entails.sepExists_elim; intro s80
  apply Entails.sepExists_elim; intro s72
  apply Entails.sepExists_elim; intro s64
  apply Entails.sepExists_elim; intro s56
  apply Entails.sepExists_elim; intro s48
  apply Entails.sepExists_elim; intro s40
  apply Entails.sepExists_elim; intro s32
  apply Entails.sepExists_elim; intro s24
  apply Entails.sepExists_elim; intro s16
  apply Entails.sepExists_elim; intro s8
  apply Entails.sepExists_elim; intro s0
  refine Entails.sepExists_right s0 (Entails.sepExists_right s8
    (Entails.sepExists_right s16 (Entails.sepExists_right s24
      (Entails.sepExists_right s32 (Entails.sepExists_right s40
        (Entails.sepExists_right s48 (Entails.sepExists_right s56
          (Entails.sepExists_right s64 (Entails.sepExists_right s72
            (Entails.sepExists_right s80 (Entails.sepExists_right s88
              (Entails.sepExists_right s96 ?_))))))))))))
  unfold v4b_optProtoUcWordsAt
  exact Entails.of_eq (by ac_rfl)

/-- Unpack `ekSentCt1ReceivedAt A base uc` into 13 64-bit words plus the heap pieces
    for `uc.auth.rootKey`, `uc.auth.macKey`, `uc.dk`, and `uc.ct1`. -/
def v4b_ekSentCt1ReceivedHeap (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) : SepProp :=
  v4b_vecU8Heap A uc.auth.rootKey rkCap rkPtr rkLen ∗
  v4b_vecU8Heap A uc.auth.macKey mkCap mkPtr mkLen ∗
  v4b_vecU8Heap A uc.dk dkCap dkPtr dkLen ∗
  v4b_vecU8Heap A uc.ct1 ct1Cap ct1Ptr ct1Len

theorem v4b_ekSentCt1ReceivedAt_unpack (A : RustAlloc) {F : ShaCompress} (base : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    ekSentCt1ReceivedAt A base uc ⊢
      ∃∗ rkCap : BitVec 64, ∃∗ rkPtr : BitVec 64, ∃∗ rkLen : BitVec 64,
      ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ∃∗ mkLen : BitVec 64,
      ∃∗ dkCap : BitVec 64, ∃∗ dkPtr : BitVec 64, ∃∗ dkLen : BitVec 64,
      ∃∗ ct1Cap : BitVec 64, ∃∗ ct1Ptr : BitVec 64, ∃∗ ct1Len : BitVec 64,
        v4b_optProtoUcWordsAt base
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
        v4b_ekSentCt1ReceivedHeap A
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc := by
  dsimp only [ekSentCt1ReceivedAt, authenticatorAt]
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono (v4b_vecU8_unpack A base uc.auth.rootKey)
        (v4b_vecU8_unpack A (base + 24#64) uc.auth.macKey))
      (sepConj_mono (v4b_vecU8_unpack A (base + 48#64) uc.dk)
        (sepConj_mono_left (v4b_vecU8_unpack A (base + 72#64) uc.ct1)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro ct1Cap
  apply Entails.sepExists_elim; intro ct1Ptr
  apply Entails.sepExists_elim; intro ct1Len
  apply Entails.sepExists_elim; intro dkCap
  apply Entails.sepExists_elim; intro dkPtr
  apply Entails.sepExists_elim; intro dkLen
  apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr
  apply Entails.sepExists_elim; intro mkLen
  apply Entails.sepExists_elim; intro rkCap
  apply Entails.sepExists_elim; intro rkPtr
  apply Entails.sepExists_elim; intro rkLen
  refine Entails.sepExists_right rkCap (Entails.sepExists_right rkPtr
    (Entails.sepExists_right rkLen (Entails.sepExists_right mkCap
      (Entails.sepExists_right mkPtr (Entails.sepExists_right mkLen
        (Entails.sepExists_right dkCap (Entails.sepExists_right dkPtr
          (Entails.sepExists_right dkLen (Entails.sepExists_right ct1Cap
            (Entails.sepExists_right ct1Ptr (Entails.sepExists_right ct1Len ?_)))))))))))
  unfold v4b_optProtoUcWordsAt v4b_ekSentCt1ReceivedHeap
  exact Entails.of_eq (by ac_rfl)

theorem v4b_ekSentCt1ReceivedHeap_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ⊢
      ⌜rkCap.toNat < 2 ^ 63⌝ ∗
      vecCapPtrDealloc A rkCap rkPtr ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A dkCap dkPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr := by
  unfold v4b_ekSentCt1ReceivedHeap
  refine Entails.trans
    (sepConj_mono (v4b_vecU8Heap_entails_dealloc A uc.auth.rootKey rkCap rkPtr rkLen)
      (sepConj_mono (v4b_vecU8Heap_entails_dealloc A uc.auth.macKey mkCap mkPtr mkLen)
        (sepConj_mono (v4b_vecU8Heap_entails_dealloc A uc.dk dkCap dkPtr dkLen)
          (v4b_vecU8Heap_entails_dealloc A uc.ct1 ct1Cap ct1Ptr ct1Len)))) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hrk
  refine Entails.pure_right hrk ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜mkCap.toNat < 2 ^ 63⌝ ∗
    ⌜dkCap.toNat < 2 ^ 63⌝ ∗
    ⌜ct1Cap.toNat < 2 ^ 63⌝ ∗
    (vecCapPtrDealloc A rkCap rkPtr ∗
     vecCapPtrDealloc A mkCap mkPtr ∗
     vecCapPtrDealloc A dkCap dkPtr ∗
     vecCapPtrDealloc A ct1Cap ct1Ptr) by ac_rfl)) ?_
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.refl _

theorem v4b_byte_word_eq_word_byte (a : BitVec 64) (b0 : BitVec 8) (u : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u)) =
      ((a ↦₆₄ ((u <<< 8) ||| b0.zeroExtend 64)) ∗ ((a + 8#64) ↦₈ EncoderFromPb.hiByte u)) := by
  let w : BitVec 64 := (u <<< 8) ||| b0.zeroExtend 64
  have hlo : EncoderFromPb.loByte w = b0 := by
    simp only [EncoderFromPb.loByte, w]
    bv_kernel
  have hun : EncoderFromPb.unshiftWord w (EncoderFromPb.hiByte u) = u := by
    simp only [EncoderFromPb.unshiftWord, EncoderFromPb.hiByte, w]
    bv_kernel
  conv_lhs => rw [← hlo, ← hun]
  rw [pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w (EncoderFromPb.hiByte u),
      ProofLib.pointsToBytes_append a (unpack64 w) [EncoderFromPb.hiByte u],
      unpack64_length,
      ← pointsTo64_eq_pointsToBytes a w]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp, w]

theorem v4b_byte_region95_to_words (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 95 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
        ⌜w0.extractLsb' 0 8 = b0⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
        memRegion (a + 24#64) 72 := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 8) (k := 87)
        (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 1#64),
      sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u
  rw [← sepConj_assoc, v4b_byte_word_eq_word_byte a b0 u, sepConj_assoc]
  have h88 : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 87 ⊢
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      memRegion (a + 24#64) 72 := by
    have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.hiByte u) ∗ memRegion (a + 9#64) 87 ⊢
        memRegion (a + 8#64) 88 := by
      rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 87)
            (b' := a + 9#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
    refine Entails.trans hjoin ?_
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 80)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 72)
          (b' := a + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64),
        ProofLib.memRegion_eight (a + 16#64)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right h88) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w8
  have hlo : (((u <<< 8) ||| b0.zeroExtend 64).extractLsb' 0 8) = b0 := by bv_kernel
  refine Entails.sepExists_right ((u <<< 8) ||| b0.zeroExtend 64)
    (Entails.sepExists_right w8 (Entails.sepExists_right w16 ?_))
  exact Entails.pure_right hlo (Entails.refl _)

theorem v4b_words4_region72_entails_104 (base w0 w8 w16 w24 : BitVec 64) :
    (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w8) ∗ ((base + 16#64) ↦₆₄ w16) ∗
      ((base + 24#64) ↦₆₄ w24) ∗ memRegion (base + 32#64) 72 ⊢
      memRegion base 104 := by
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

/-- Error branch after `ekSentCt1ReceivedFromPb` (`+2308..+2328 -> +5260 -> +5264`):
    when `[fsp + 1888] = noneCap`, loads `x26 = w1896` and jumps to `+5264`. -/
theorem v4b_step_2308_err_to_5264
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 : BitVec 64) (d28 : BitVec 32)
    (w1896 w1904 w1912 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5264#64) s
      (((fsp + 232#64) ↦₃₂ d28) ∗
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗
        ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗
        ((fsp + 1912#64) ↦₆₄ w1912) ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 232#64) ↦₃₂ d28) ∗
          ((fsp + 1888#64) ↦₆₄ noneCap) ∗
          ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗
          ((fsp + 1912#64) ↦₆₄ w1912) ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x26 = w1896 ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 2308 24
  states_from_pb_fetches_range b (Rust.withPanics ext) 5260 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `Ok(uc)` followed by `receivingCt2 = none` (`x28 = noneCap`) at `+2308..+2368 -> +6860`:
    loads `uc` fields and branches to `+6860` (`v4_states_from_pb_drop_uc_6860`). -/
theorem v4b_step_2308_ok_none_to_6860
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v72 v128 v144 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = noneCap) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6860#64) s
      (((fsp + 72#64) ↦₆₄ v72) ∗
        ((fsp + 128#64) ↦₆₄ v128) ∗
        ((fsp + 144#64) ↦₆₄ v144) ∗
        v4b_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          v4b_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
          Frame) ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = mkPtr ∧
        s'.readReg64 .x1 = mkCap ∧
        s'.readReg64 .x9 = rkCap ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  have hrk_ne := cap_add_one_beq_zero_false hrk_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 2308 64
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc hx28 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [v4b_optProtoUcWordsAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.FromPb

