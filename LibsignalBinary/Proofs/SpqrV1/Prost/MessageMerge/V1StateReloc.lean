/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefs

/-!
# Discriminant and Word-Level Relocation Infrastructure for `V1State::merge`

Discriminant extraction/reconstruction for `optProtoInnerStateCapAt`, word-level (`Q128`)
stack-to-destination relocation lemmas for `Polynomial{Decoder,Encoder}` and `Unchunked*`
sub-structures, `*PBAt ⊢ *PBCapAt 0` bridges for error paths, and the shared post-tag latch state
`v1StateAfterTagPre` at `entry + 2700#64`.
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

/-! ## 1. Discriminant Extraction for `optProtoInnerStateCapAt` -/

def InnerStateDiscr (bsLen : Nat) : Option V1State.InnerState → BitVec 64 → Prop
  | none, d => d = none2Cap
  | some (.keysUnsampled _), d => d = 0x8000000000000000#64
  | some (.keysSampled _), d => d = 0x8000000000000001#64
  | some (.headerSent _), d => d = 0x8000000000000002#64
  | some (.ct1Received _), d => d = 0x8000000000000003#64
  | some (.ekSentCt1Received _), d => d = 0x8000000000000004#64
  | some (.noHeaderReceived _), d => d = 0x8000000000000005#64
  | some (.headerReceived _), d => d = 0x8000000000000006#64
  | some (.ct1Sampled s), d =>
      match s.uc with
      | none => d = noneCap
      | some _ => BytesMergeCapOk d bsLen
  | some (.ekReceivedCt1Sampled _), d => d = 0x8000000000000008#64
  | some (.ct1Acknowledged _), d => d = 0x8000000000000009#64
  | some (.ct2Sampled _), d => d = 0x800000000000000a#64

def optProtoInnerStateCapTailAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (is : Option V1State.InnerState) (d : BitVec 64) : SepProp :=
  match is with
  | none => memRegion (a + 8#64) 216
  | some (.keysUnsampled s) => chunkedKeysUnsampledPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 64#64) 160
  | some (.keysSampled s) => chunkedKeysSampledPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 168#64) 56
  | some (.headerSent s) => chunkedHeaderSentPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 184#64) 40
  | some (.ct1Received s) => chunkedCt1ReceivedPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 168#64) 56
  | some (.ekSentCt1Received s) => chunkedEkSentCt1ReceivedPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 152#64) 72
  | some (.noHeaderReceived s) => chunkedNoHeaderReceivedPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 104#64) 120
  | some (.headerReceived s) => chunkedHeaderReceivedPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 128#64) 96
  | some (.ct1Sampled s) =>
      match s.uc with
      | none => memRegion (a + 8#64) 120 ∗
          optPolynomialEncoderPBAt A (a + 128#64) s.sendingCt1 ∗
          optPolynomialDecoderPBAt A (a + 184#64) s.receivingEk
      | some u =>
          (∃∗ ptr : BitVec 64, ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗ EncodedLen.vecU8Buf A d ptr u.hdr) ∗
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.es) ∗
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
          optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
          ((a + 0x78#64) ↦₆₄ u.epoch) ∗
          optPolynomialEncoderPBAt A (a + 128#64) s.sendingCt1 ∗
          optPolynomialDecoderPBAt A (a + 184#64) s.receivingEk
  | some (.ekReceivedCt1Sampled s) => chunkedEkReceivedCt1SampledPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 192#64) 32
  | some (.ct1Acknowledged s) => chunkedCt1AcknowledgedPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 176#64) 48
  | some (.ct2Sampled s) => chunkedCt2SampledPBCapAt A (a + 8#64) bsLen s ∗ memRegion (a + 120#64) 104

theorem vecU8CapAt_entails_discr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (v : List (BitVec 8)) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v) ⊢
      ∃∗ d : BitVec 64, ⌜BytesMergeCapOk d bsLen⌝ ∗ (a ↦₆₄ d) ∗
        (∃∗ ptr : BitVec 64, ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ EncodedLen.vecU8Buf A d ptr v) := by
  refine ProofLib.Entails.sepExists_elim fun d => ProofLib.Entails.sepExists_elim fun ptr => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro d)
  rw [EncodedLen.vecU8At_eq_header_sep_buf]
  refine Entails.pure_left fun hcap => Entails.pure_right hcap ?_
  dsimp only [vecHeader]; simp only [sepConj_assoc]
  exact sepConj_mono_right (Entails.sepExists_intro (P := fun ptr => ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ EncodedLen.vecU8Buf A d ptr v) ptr)

theorem discr_entails_vecU8CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (v : List (BitVec 8))
    (d : BitVec 64) (hd : BytesMergeCapOk d bsLen) :
    ((a ↦₆₄ d) ∗ (∃∗ ptr : BitVec 64, ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ EncodedLen.vecU8Buf A d ptr v)) ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v) := by
  simp only [sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun ptr => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro d); refine Entails.trans ?_ (Entails.sepExists_intro ptr)
  rw [EncodedLen.vecU8At_eq_header_sep_buf]; dsimp only [vecHeader]; simp only [sepConj_assoc]
  exact Entails.pure_right hd (Entails.refl _)

theorem optProtoInnerStateCapAt_entails_discr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (is : Option V1State.InnerState) :
    optProtoInnerStateCapAt A a bsLen is ⊢
      ∃∗ d : BitVec 64, ⌜InnerStateDiscr bsLen is d⌝ ∗ (a ↦₆₄ d) ∗ optProtoInnerStateCapTailAt A a bsLen is d := by
  rcases is with _ | st
  · refine Entails.trans ?_ (Entails.sepExists_intro none2Cap)
    dsimp [optProtoInnerStateCapAt, optProtoInnerStateCapTailAt, InnerStateDiscr]
    exact Entails.pure_right rfl (Entails.refl _)
  · cases st with
    | keysUnsampled s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000000#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | keysSampled s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000001#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | headerSent s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000002#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | ct1Received s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000003#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | ekSentCt1Received s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000004#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | noHeaderReceived s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000005#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | headerReceived s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000006#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | ct1Sampled s =>
      rcases s with ⟨_ | u, sendingCt1, receivingEk⟩
      · refine Entails.trans ?_ (Entails.sepExists_intro noneCap)
        dsimp [optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, optProtoInnerStateCapTailAt, InnerStateDiscr]
        exact Entails.pure_right rfl (Entails.of_eq (by ac_rfl))
      · dsimp [optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, unchunkedCt1SentPBCapAt, optProtoInnerStateCapTailAt, InnerStateDiscr]
        simp only [sepConj_assoc]
        refine Entails.trans (sepConj_mono_left (vecU8CapAt_entails_discr A a bsLen u.hdr)) ?_
        simp only [sepExists_sepConj_left, sepConj_assoc]; exact Entails.refl _
    | ekReceivedCt1Sampled s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000008#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | ct1Acknowledged s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x8000000000000009#64)
      exact Entails.pure_right rfl (Entails.refl _)
    | ct2Sampled s =>
      refine Entails.trans ?_ (Entails.sepExists_intro 0x800000000000000a#64)
      exact Entails.pure_right rfl (Entails.refl _)

theorem discr_entails_optProtoInnerStateCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (is : Option V1State.InnerState) (d : BitVec 64) (hd : InnerStateDiscr bsLen is d) :
    (a ↦₆₄ d) ∗ optProtoInnerStateCapTailAt A a bsLen is d ⊢ optProtoInnerStateCapAt A a bsLen is := by
  rcases is with _ | st
  · subst hd; exact Entails.refl _
  · cases st with
    | keysUnsampled s => subst hd; exact Entails.refl _
    | keysSampled s => subst hd; exact Entails.refl _
    | headerSent s => subst hd; exact Entails.refl _
    | ct1Received s => subst hd; exact Entails.refl _
    | ekSentCt1Received s => subst hd; exact Entails.refl _
    | noHeaderReceived s => subst hd; exact Entails.refl _
    | headerReceived s => subst hd; exact Entails.refl _
    | ct1Sampled s =>
      rcases s with ⟨_ | u, sendingCt1, receivingEk⟩
      · change d = noneCap at hd; subst hd
        dsimp [optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, optProtoInnerStateCapTailAt]
        exact Entails.of_eq (by ac_rfl)
      · change BytesMergeCapOk d bsLen at hd
        dsimp [optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, unchunkedCt1SentPBCapAt, optProtoInnerStateCapTailAt]
        simp only [sepConj_assoc]; rw [← sepConj_assoc]
        exact sepConj_mono_left (discr_entails_vecU8CapAt A a bsLen u.hdr d hd)
    | ekReceivedCt1Sampled s => subst hd; exact Entails.refl _
    | ct1Acknowledged s => subst hd; exact Entails.refl _
    | ct2Sampled s => subst hd; exact Entails.refl _

/-! ## 2. Word-Level Relocation Helpers for Stack-Temp Copies -/

/-- Address-independent heap part of a capacity-bounded `Vec<u8>` with header words `(w0, w1, w2)`. -/
def vecU8CapHeap (A : RustAlloc) (bsLen : Nat) (v : List (BitVec 8)) (w0 w1 w2 : BitVec 64) : SepProp :=
  ⌜BytesMergeCapOk w0 bsLen ∧ w2 = BitVec.ofNat 64 v.length⌝ ∗ EncodedLen.vecU8Buf A w0 w1 v

theorem vecU8CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (v : List (BitVec 8)) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        vecU8CapHeap A bsLen v w0 w1 w2 := by
  refine ProofLib.Entails.sepExists_elim fun w0 => ProofLib.Entails.sepExists_elim fun w1 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 v.length))
  rw [EncodedLen.vecU8At_eq_header_sep_buf]; refine Entails.pure_left fun hcap => ?_
  dsimp only [vecHeader, vecU8CapHeap]; simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (Entails.pure_right ⟨hcap, trivial⟩ (Entails.refl _))))

theorem vecU8CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (v : List (BitVec 8))
    (w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ vecU8CapHeap A bsLen v w0 w1 w2 ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v) := by
  dsimp only [vecU8CapHeap]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ (⌜BytesMergeCapOk w0 bsLen ∧ w2 = BitVec.ofNat 64 v.length⌝ ∗ EncodedLen.vecU8Buf A w0 w1 v) =
    ⌜BytesMergeCapOk w0 bsLen ∧ w2 = BitVec.ofNat 64 v.length⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ EncodedLen.vecU8Buf A w0 w1 v)) ?_
  refine Entails.pure_left fun ⟨hcap, hw2⟩ => ?_; subst hw2
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  rw [EncodedLen.vecU8At_eq_header_sep_buf]; dsimp only [vecHeader]; simp only [sepConj_assoc]
  exact Entails.pure_right hcap (Entails.refl _)

def words3At (a : BitVec 64) (w0 w1 w2 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)

def words5At (a : BitVec 64) (w0 w1 w2 w3 w4 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)

def words6At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

def words7At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
  ((a + 48#64) ↦₆₄ w6)

def words10At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) : SepProp :=
  words3At a w0 w1 w2 ∗ words7At (a + 24#64) w3 w4 w5 w6 w7 w8 w9

def words13At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) : SepProp :=
  words3At a w0 w1 w2 ∗ words10At (a + 24#64) w3 w4 w5 w6 w7 w8 w9 w10 w11 w12

def words16At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) : SepProp :=
  words3At a w0 w1 w2 ∗ words13At (a + 24#64) w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

def optAuthCapHeap (A : RustAlloc) (bsLen : Nat) :
    Option ProtoAuthenticator → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some auth, w0, w1, w2, w3, w4, w5 =>
      vecU8CapHeap A bsLen auth.rootKey w0 w1 w2 ∗ vecU8CapHeap A bsLen auth.macKey w3 w4 w5

theorem memRegion_40_eq_words5 (a : BitVec 64) :
    memRegion (a + 8#64) 40 =
      ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64), ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem optAuthenticatorPBCapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBCapAt A a bsLen opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        words6At a w0 w1 w2 w3 w4 w5 ∗ optAuthCapHeap A bsLen opt w0 w1 w2 w3 w4 w5 := by
  cases opt with
  | none =>
    dsimp only [optAuthenticatorPBCapAt, optAuthCapHeap, words6At]
    rw [memRegion_40_eq_words5]; simp only [sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w4 =>
      ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w2 =>
      ProofLib.Entails.sepExists_elim fun w1 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    simp only [pure_true, sepConj_emp, sepConj_assoc]; exact Entails.refl _
  | some auth =>
    dsimp only [optAuthenticatorPBCapAt, authenticatorPBCapAt, optAuthCapHeap, words6At]
    refine Entails.trans (sepConj_mono (vecU8CapAt_extract_words A a bsLen auth.rootKey)
      (vecU8CapAt_extract_words A (a + 0x18#64) bsLen auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
      ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w0 =>
      ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    have h24 : a + 0x18#64 = a + 24#64 := rfl
    have h32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_lin
    have h40 : a + 0x18#64 + 16#64 = a + 40#64 := by bv_lin
    rw [h24, h32, h40]; exact Entails.of_eq (by ac_rfl)

theorem optAuthenticatorPBCapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option ProtoAuthenticator) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    words6At a w0 w1 w2 w3 w4 w5 ∗ optAuthCapHeap A bsLen opt w0 w1 w2 w3 w4 w5 ⊢
      optAuthenticatorPBCapAt A a bsLen opt := by
  cases opt with
  | none =>
    dsimp only [optAuthenticatorPBCapAt, optAuthCapHeap, words6At]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_40_eq_words5]
    refine sepConj_mono_right ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w5); refine Entails.trans ?_ (Entails.sepExists_intro w4)
    refine Entails.trans ?_ (Entails.sepExists_intro w3); refine Entails.trans ?_ (Entails.sepExists_intro w2)
    refine Entails.trans ?_ (Entails.sepExists_intro w1); exact Entails.refl _
  | some auth =>
    dsimp only [optAuthenticatorPBCapAt, authenticatorPBCapAt, optAuthCapHeap, words6At]
    have h24 : a + 0x18#64 = a + 24#64 := rfl
    have h32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_lin
    have h40 : a + 0x18#64 + 16#64 = a + 40#64 := by bv_lin
    have hb := vecU8CapAt_of_words A (a + 0x18#64) bsLen auth.macKey w3 w4 w5
    rw [h24, h32, h40] at hb
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono (vecU8CapAt_of_words A a bsLen auth.rootKey w0 w1 w2) hb)

def vecVecU8Heap (A : RustAlloc) (v : List (List (BitVec 8))) (w0 w1 w2 : BitVec 64) : SepProp :=
  ⌜w2 = BitVec.ofNat 64 v.length⌝ ∗ vecVecU8Buf A w0 w1 v

theorem vecVecU8At_extract_words (A : RustAlloc) (a : BitVec 64) (v : List (List (BitVec 8))) :
    ProtoRepr.vecVecU8At A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        words3At a w0 w1 w2 ∗ vecVecU8Heap A v w0 w1 w2 := by
  rw [vecVecU8At_eq_exists_pin]; refine ProofLib.Entails.sepExists_elim fun pin => ?_
  rw [vecVecU8PinnedAt_eq_header_buf]
  refine Entails.trans ?_ (Entails.sepExists_intro pin.cap); refine Entails.trans ?_ (Entails.sepExists_intro pin.ptr)
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 v.length))
  dsimp only [words3At, vecVecU8Heap]; simp only [pure_true, emp_sepConj, sepConj_assoc]; exact Entails.refl _

theorem vecVecU8At_of_words (A : RustAlloc) (a : BitVec 64) (v : List (List (BitVec 8)))
    (w0 w1 w2 : BitVec 64) :
    words3At a w0 w1 w2 ∗ vecVecU8Heap A v w0 w1 w2 ⊢ ProtoRepr.vecVecU8At A a v := by
  dsimp only [words3At, vecVecU8Heap]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ∗
      (⌜w2 = BitVec.ofNat 64 v.length⌝ ∗ vecVecU8Buf A w0 w1 v) =
    ⌜w2 = BitVec.ofNat 64 v.length⌝ ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ vecVecU8Buf A w0 w1 v)) ?_
  refine Entails.pure_left fun hw2 => ?_; subst hw2
  rw [vecVecU8At_eq_exists_pin]; refine Entails.trans ?_ (Entails.sepExists_intro (VecPin.mk w0 w1))
  rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by ac_rfl)

theorem memRegion_32_eq_words4 (a : BitVec 64) :
    memRegion (a + 8#64) 32 =
      ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64), ProofLib.memRegion_eight (a + 32#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem byte_pad7_extract_word (a : BitVec 64) (b0 : BitVec 8) :
    ((a + 32#64) ↦₈ b0) ∗ memRegion (a + 33#64) 7 ⊢
      ∃∗ w4 : BitVec 64, ⌜∃ bs7 : List (BitVec 8), bs7.length = 7 ∧ unpack64 w4 = b0 :: bs7⌝ ∗
        ((a + 32#64) ↦₆₄ w4) := by
  rw [ProofLib.memRegion_eq_exists_bytes (a + 33#64) 7 (by decide)]; simp only [sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun bs7 => ?_
  refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_; rw [sepConj_assoc]
  refine Entails.pure_left fun hbs7 => ?_
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 (bs := b0 :: bs7) (by simp [hbs7])
  have haddr : a + 32#64 + 1#64 = a + 33#64 := by bv_lin
  have hcons : (((a + 32#64) ↦₈ b0) ∗ ((a + 33#64) ↦ₛ bs7)) = ((a + 32#64) ↦₆₄ w4) := by
    rw [← haddr, ← pointsToBytes_cons, hw4, ← pointsTo64_eq_pointsToBytes]
  rw [sepConj_comm, hcons]
  exact Entails.sepExists_right w4 (Entails.pure_right ⟨bs7, hbs7, hw4.symm⟩ (Entails.refl _))

theorem byte_pad7_of_word (a : BitVec 64) (b0 : BitVec 8) (w4 : BitVec 64) :
    ⌜∃ bs7 : List (BitVec 8), bs7.length = 7 ∧ unpack64 w4 = b0 :: bs7⌝ ∗ ((a + 32#64) ↦₆₄ w4) ⊢
      ((a + 32#64) ↦₈ b0) ∗ memRegion (a + 33#64) 7 := by
  refine Entails.pure_left fun ⟨bs7, hbs7, hw4⟩ => ?_
  have haddr : a + 32#64 + 1#64 = a + 33#64 := by bv_lin
  rw [pointsTo64_eq_pointsToBytes, hw4, pointsToBytes_cons, haddr]
  refine sepConj_mono_right ?_
  rw [ProofLib.memRegion_eq_exists_bytes (a + 33#64) 7 (by decide)]
  exact Entails.sepExists_right bs7 (Entails.pure_right hbs7 (Entails.refl _))

theorem u32_pair_of_word (a : BitVec 64) (lo hi : BitVec 32) (w3 : BitVec 64) :
    ⌜w3 = hi ++ lo⌝ ∗ ((a + 24#64) ↦₆₄ w3) ⊢ ((a + 24#64) ↦₃₂ lo) ∗ ((a + 28#64) ↦₃₂ hi) := by
  refine Entails.pure_left fun hw3 => ?_; subst hw3
  have hp := (pointsTo32_pair (a + 24#64) lo hi).symm
  have h28 : a + 24#64 + 4#64 = a + 28#64 := by bv_lin
  rw [h28] at hp; exact Entails.of_eq hp

def optPolyDecoderHeap (A : RustAlloc) :
    Option PolynomialDecoder → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _ => ⌜w0 = noneCap⌝
  | some d, w0, w1, w2, w3, w4 =>
      vecVecU8Heap A d.pts w0 w1 w2 ∗
        ⌜w3 = d.polys ++ d.ptsNeeded⌝ ∗
        ⌜∃ bs7 : List (BitVec 8), bs7.length = 7 ∧ unpack64 w4 = boolByte d.isComplete :: bs7⌝

theorem optPolynomialDecoderPBAt_extract_words (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBAt A a opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        words5At a w0 w1 w2 w3 w4 ∗ optPolyDecoderHeap A opt w0 w1 w2 w3 w4 := by
  cases opt with
  | none =>
    dsimp only [optPolynomialDecoderPBAt, optPolyDecoderHeap, words5At]
    rw [memRegion_32_eq_words4]; simp only [sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w3 =>
      ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w1 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4)
    simp only [pure_true, sepConj_emp, sepConj_assoc]; exact Entails.refl _
  | some d =>
    dsimp only [optPolynomialDecoderPBAt, polynomialDecoderPBAt, optPolyDecoderHeap, words5At]
    have h24 : (((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys)) = ((a + 24#64) ↦₆₄ (d.polys ++ d.ptsNeeded)) := by
      have hp := pointsTo32_pair (a + 24#64) d.ptsNeeded d.polys
      have h28 : a + 24#64 + 4#64 = a + 28#64 := by bv_lin
      rwa [h28] at hp
    refine Entails.trans (Entails.of_eq (by
      rw [← sepConj_assoc ((a + 24#64) ↦₃₂ d.ptsNeeded), h24] :
      ProtoRepr.vecVecU8At A a d.pts ∗ ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗
        ((a + 32#64) ↦₈ boolByte d.isComplete) ∗ memRegion (a + 33#64) 7 =
      ProtoRepr.vecVecU8At A a d.pts ∗ ((a + 24#64) ↦₆₄ (d.polys ++ d.ptsNeeded)) ∗
        (((a + 32#64) ↦₈ boolByte d.isComplete) ∗ memRegion (a + 33#64) 7))) ?_
    refine Entails.trans (sepConj_mono (vecVecU8At_extract_words A a d.pts)
      (sepConj_mono_right (byte_pad7_extract_word a (boolByte d.isComplete)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w0 =>
      ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro (d.polys ++ d.ptsNeeded))
    refine Entails.trans ?_ (Entails.sepExists_intro w4); dsimp only [words3At]
    refine Entails.trans (Entails.of_eq (by ac_rfl)) ?_
    simp only [pure_true, emp_sepConj]; exact Entails.of_eq (by ac_rfl)

theorem optPolynomialDecoderPBAt_of_words (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialDecoder) (w0 w1 w2 w3 w4 : BitVec 64) :
    words5At a w0 w1 w2 w3 w4 ∗ optPolyDecoderHeap A opt w0 w1 w2 w3 w4 ⊢
      optPolynomialDecoderPBAt A a opt := by
  cases opt with
  | none =>
    dsimp only [optPolynomialDecoderPBAt, optPolyDecoderHeap, words5At]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_32_eq_words4]
    refine sepConj_mono_right ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    exact Entails.refl _
  | some d =>
    dsimp only [optPolynomialDecoderPBAt, polynomialDecoderPBAt, optPolyDecoderHeap, words5At]
    rw [← sepConj_assoc ((a + 24#64) ↦₃₂ d.ptsNeeded)]
    refine Entails.trans (Entails.of_eq (by dsimp only [words3At]; ac_rfl))
      (sepConj_mono (vecVecU8At_of_words A a d.pts w0 w1 w2)
        (sepConj_mono (u32_pair_of_word a d.ptsNeeded d.polys w3)
          (byte_pad7_of_word a (boolByte d.isComplete) w4)))

theorem memRegion_48_eq_words6 (a : BitVec 64) :
    memRegion (a + 8#64) 48 =
      ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 48#64) (n := 40) (k := 8) (N := 48) rfl (by bv_lin) (by decide)
  rw [s1, memRegion_40_eq_words5 a, ProofLib.memRegion_eight (a + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem u32_pad4_extract_word (a : BitVec 64) (lo : BitVec 32) :
    ((a + 48#64) ↦₃₂ lo) ∗ memRegion (a + 52#64) 4 ⊢
      ∃∗ w6 : BitVec 64, ⌜∃ hi : BitVec 32, w6 = hi ++ lo⌝ ∗ ((a + 48#64) ↦₆₄ w6) := by
  rw [ProofLib.memRegion_four (a + 52#64)]; simp only [sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun hi => ?_
  have hp : (((a + 48#64) ↦₃₂ lo) ∗ ((a + 52#64) ↦₃₂ hi)) = ((a + 48#64) ↦₆₄ (hi ++ lo)) := by
    have h := pointsTo32_pair (a + 48#64) lo hi
    have h52 : a + 48#64 + 4#64 = a + 52#64 := by bv_lin
    rwa [h52] at h
  rw [hp]; exact Entails.sepExists_right (hi ++ lo) (Entails.pure_right ⟨hi, rfl⟩ (Entails.refl _))

theorem u32_pad4_of_word (a : BitVec 64) (lo : BitVec 32) (w6 : BitVec 64) :
    ⌜∃ hi : BitVec 32, w6 = hi ++ lo⌝ ∗ ((a + 48#64) ↦₆₄ w6) ⊢
      ((a + 48#64) ↦₃₂ lo) ∗ memRegion (a + 52#64) 4 := by
  refine Entails.pure_left fun ⟨hi, hw6⟩ => ?_; subst hw6
  have hp : ((a + 48#64) ↦₆₄ (hi ++ lo)) = (((a + 48#64) ↦₃₂ lo) ∗ ((a + 52#64) ↦₃₂ hi)) := by
    have h := (pointsTo32_pair (a + 48#64) lo hi).symm
    have h52 : a + 48#64 + 4#64 = a + 52#64 := by bv_lin
    rwa [h52] at h
  rw [hp, ProofLib.memRegion_four (a + 52#64)]
  exact sepConj_mono_right (Entails.sepExists_intro hi)

def optPolyEncoderHeap (A : RustAlloc) :
    Option PolynomialEncoder → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some e, w0, w1, w2, w3, w4, w5, w6 =>
      vecVecU8Heap A e.pts w0 w1 w2 ∗ vecVecU8Heap A e.polys w3 w4 w5 ∗ ⌜∃ hi : BitVec 32, w6 = hi ++ e.idx⌝

theorem optPolynomialEncoderPBAt_extract_words (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBAt A a opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        words7At a w0 w1 w2 w3 w4 w5 w6 ∗ optPolyEncoderHeap A opt w0 w1 w2 w3 w4 w5 w6 := by
  cases opt with
  | none =>
    dsimp only [optPolynomialEncoderPBAt, optPolyEncoderHeap, words7At]
    rw [memRegion_48_eq_words6]; simp only [sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w6 => ProofLib.Entails.sepExists_elim fun w5 =>
      ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w3 =>
      ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w1 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w6)
    simp only [pure_true, sepConj_emp, sepConj_assoc]; exact Entails.refl _
  | some e =>
    dsimp only [optPolynomialEncoderPBAt, polynomialEncoderPBAt, optPolyEncoderHeap, words7At]
    refine Entails.trans (sepConj_mono (vecVecU8At_extract_words A a e.pts)
      (sepConj_mono (vecVecU8At_extract_words A (a + 24#64) e.polys)
        (u32_pad4_extract_word a e.idx))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w6 =>
      ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
      ProofLib.Entails.sepExists_elim fun w5 =>
      ProofLib.Entails.sepExists_elim fun w0 => ProofLib.Entails.sepExists_elim fun w1 =>
      ProofLib.Entails.sepExists_elim fun w2 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w6); dsimp only [words3At]
    have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
    have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
    rw [h32, h40]; exact Entails.of_eq (by ac_rfl)

theorem optPolynomialEncoderPBAt_of_words (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialEncoder) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    words7At a w0 w1 w2 w3 w4 w5 w6 ∗ optPolyEncoderHeap A opt w0 w1 w2 w3 w4 w5 w6 ⊢
      optPolynomialEncoderPBAt A a opt := by
  cases opt with
  | none =>
    dsimp only [optPolynomialEncoderPBAt, optPolyEncoderHeap, words7At]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_48_eq_words6]
    refine sepConj_mono_right ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    exact Entails.refl _
  | some e =>
    dsimp only [optPolynomialEncoderPBAt, polynomialEncoderPBAt, optPolyEncoderHeap, words7At]
    have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
    have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
    have hpolys := vecVecU8At_of_words A (a + 24#64) e.polys w3 w4 w5
    dsimp only [words3At] at hpolys; rw [h32, h40] at hpolys
    refine Entails.trans (Entails.of_eq (by dsimp only [words3At]; ac_rfl))
      (sepConj_mono (vecVecU8At_of_words A a e.pts w0 w1 w2)
        (sepConj_mono hpolys (u32_pad4_of_word a e.idx w6)))

def unchunked2CapHeap (A : RustAlloc) (bsLen : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) : SepProp :=
  optAuthCapHeap A bsLen auth w0 w1 w2 w3 w4 w5 ∗ ⌜w6 = epoch⌝

theorem unchunked2CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) :
    unchunked2CapAt A a bsLen epoch auth ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        words7At a w0 w1 w2 w3 w4 w5 w6 ∗ unchunked2CapHeap A bsLen epoch auth w0 w1 w2 w3 w4 w5 w6 := by
  dsimp only [unchunked2CapAt, unchunked2CapHeap, words7At]
  refine Entails.trans (sepConj_mono_left (optAuthenticatorPBCapAt_extract_words A a bsLen auth)) ?_
  simp only [sepExists_sepConj_left]
  refine ProofLib.Entails.sepExists_elim fun w0 => ProofLib.Entails.sepExists_elim fun w1 =>
    ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w3 =>
    ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w5 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro epoch); dsimp only [words6At]
  have h48 : a + 0x30#64 = a + 48#64 := rfl
  rw [h48]; refine Entails.trans (Entails.of_eq (by ac_rfl)) ?_
  simp only [pure_true, sepConj_emp]; exact Entails.of_eq (by ac_rfl)

theorem unchunked2CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    words7At a w0 w1 w2 w3 w4 w5 w6 ∗ unchunked2CapHeap A bsLen epoch auth w0 w1 w2 w3 w4 w5 w6 ⊢
      unchunked2CapAt A a bsLen epoch auth := by
  dsimp only [unchunked2CapAt, unchunked2CapHeap, words7At]
  have h48 : a + 0x30#64 = a + 48#64 := rfl
  rw [h48]
  refine Entails.trans (Entails.of_eq (by dsimp only [words6At]; ac_rfl :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6)) ∗
      (optAuthCapHeap A bsLen auth w0 w1 w2 w3 w4 w5 ∗ ⌜w6 = epoch⌝) =
    ⌜w6 = epoch⌝ ∗ (words6At a w0 w1 w2 w3 w4 w5 ∗ optAuthCapHeap A bsLen auth w0 w1 w2 w3 w4 w5) ∗
      ((a + 48#64) ↦₆₄ w6))) ?_
  refine Entails.pure_left fun hw6 => ?_; subst hw6
  exact sepConj_mono_left (optAuthenticatorPBCapAt_of_words A a bsLen auth w0 w1 w2 w3 w4 w5)

theorem rustBytesVecAt_entails_vecU8CapAt_zero (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    rustBytesVecAt A a bs ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap 0⌝ ∗ vecU8At A a cap ptr bs) := by
  refine ProofLib.Entails.sepExists_elim fun cap => ProofLib.Entails.sepExists_elim fun ptr => ?_
  have hok : BytesMergeCapOk cap 0 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide : 0 < 2 ^ 32)))))
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.pure_right hok (Entails.refl _)))

theorem optAuthenticatorPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBAt A a opt ⊢ optAuthenticatorPBCapAt A a 0 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth =>
    exact sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A a auth.rootKey)
      (rustBytesVecAt_entails_vecU8CapAt_zero A (a + 0x18#64) auth.macKey)

theorem unchunked2At_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) :
    unchunked2At A a epoch auth ⊢ unchunked2CapAt A a 0 epoch auth :=
  sepConj_mono_left (optAuthenticatorPBAt_entails_cap_zero A a auth)

theorem unchunked3At_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3At A a epoch auth v3 ⊢ unchunked3CapAt A a 0 epoch auth v3 :=
  sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A a v3)
    (sepConj_mono_left (optAuthenticatorPBAt_entails_cap_zero A (a + 0x18#64) auth))

theorem unchunked4At_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8)) :
    unchunked4At A a epoch auth v3 v4 ⊢ unchunked4CapAt A a 0 epoch auth v3 v4 :=
  sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A a v3)
    (sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A (a + 0x18#64) v4)
      (sepConj_mono_left (optAuthenticatorPBAt_entails_cap_zero A (a + 0x30#64) auth)))

theorem unchunked5At_entails_cap_zero (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5At A a epoch auth v3 v4 v5 ⊢ unchunked5CapAt A a 0 epoch auth v3 v4 v5 :=
  sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A a v3)
    (sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A (a + 0x18#64) v4)
      (sepConj_mono (rustBytesVecAt_entails_vecU8CapAt_zero A (a + 0x30#64) v5)
        (sepConj_mono_left (optAuthenticatorPBAt_entails_cap_zero A (a + 0x48#64) auth))))

theorem optKeysUnsampledPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBAt A a opt ⊢ optKeysUnsampledPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked2At_entails_cap_zero A a u.epoch u.auth

theorem optNoHeaderReceivedPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBAt A a opt ⊢ optNoHeaderReceivedPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked2At_entails_cap_zero A a u.epoch u.auth

theorem optCt2SentPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBAt A a opt ⊢ optCt2SentPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked2At_entails_cap_zero A a u.epoch u.auth

theorem optHeaderReceivedPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBAt A a opt ⊢ optHeaderReceivedPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked3At_entails_cap_zero A a u.epoch u.auth u.hdr

theorem optEkSentPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBAt A a opt ⊢ optEkSentPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked3At_entails_cap_zero A a u.epoch u.auth u.dk

theorem optHeaderSentPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBAt A a opt ⊢ optHeaderSentPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked4At_entails_cap_zero A a u.epoch u.auth u.ek u.dk

theorem optCt1ReceivedPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optEkSentCt1ReceivedPBAt A a opt ⊢ optUnchunkedEkSentCt1ReceivedPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked4At_entails_cap_zero A a u.epoch u.auth u.dk u.ct1

theorem optCt1SentPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.Ct1Sent) :
    optCt1SentPBAt A a opt ⊢ optUnchunkedCt1SentPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked5At_entails_cap_zero A a u.epoch u.auth u.hdr u.es u.ct1

theorem optCt1SentEkReceivedPBAt_entails_cap_zero (A : RustAlloc) (a : BitVec 64) (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBAt A a opt ⊢ optCt1SentEkReceivedPBCapAt A a 0 opt := by
  cases opt with | none => exact Entails.refl _ | some u => exact unchunked5At_entails_cap_zero A a u.epoch u.auth u.es u.ek u.ct1

/-- Generic `Option` of `unchunked2CapAt` (`56` bytes = `7` words). -/
def optUnchunked2CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator) → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some (epoch, auth) => unchunked2CapAt A a bsLen epoch auth

def optUnchunked2CapHeap (A : RustAlloc) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator) →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _ => ⌜w0 = noneCap2⌝
  | some (epoch, auth), w0, w1, w2, w3, w4, w5, w6 =>
      unchunked2CapHeap A bsLen epoch auth w0 w1 w2 w3 w4 w5 w6

theorem optUnchunked2CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator)) :
    optUnchunked2CapAt A a bsLen opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        words7At a w0 w1 w2 w3 w4 w5 w6 ∗ optUnchunked2CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 := by
  cases opt with
  | none =>
    dsimp only [optUnchunked2CapAt, optUnchunked2CapHeap, words7At]
    rw [memRegion_48_eq_words6]; simp only [sepExists_sepConj_right]
    refine ProofLib.Entails.sepExists_elim fun w6 => ProofLib.Entails.sepExists_elim fun w5 =>
      ProofLib.Entails.sepExists_elim fun w4 => ProofLib.Entails.sepExists_elim fun w3 =>
      ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w1 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w6)
    simp only [pure_true, sepConj_emp, sepConj_assoc]; exact Entails.refl _
  | some p => exact unchunked2CapAt_extract_words A a bsLen p.1 p.2

theorem optUnchunked2CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator))
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    words7At a w0 w1 w2 w3 w4 w5 w6 ∗ optUnchunked2CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 ⊢
      optUnchunked2CapAt A a bsLen opt := by
  cases opt with
  | none =>
    dsimp only [optUnchunked2CapAt, optUnchunked2CapHeap, words7At]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_48_eq_words6]
    refine sepConj_mono_right ?_
    refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    exact Entails.refl _
  | some p => exact unchunked2CapAt_of_words A a bsLen p.1 p.2 w0 w1 w2 w3 w4 w5 w6

theorem optKeysUnsampledPBCapAt_eq_optUnchunked2 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBCapAt A a bsLen opt =
      optUnchunked2CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth)) := by cases opt <;> rfl

theorem optNoHeaderReceivedPBCapAt_eq_optUnchunked2 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBCapAt A a bsLen opt =
      optUnchunked2CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth)) := by cases opt <;> rfl

theorem optCt2SentPBCapAt_eq_optUnchunked2 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBCapAt A a bsLen opt =
      optUnchunked2CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth)) := by cases opt <;> rfl

theorem memRegion_16_eq_words2 (a : BitVec 64) :
    memRegion (a + 8#64) 16 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [s1, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem none_memRegion_step (a : BitVec 64) (k : Nat) (hk : 16 + k ≤ 2 ^ 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) (16 + k) =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, words3At a noneCap w1 w2 ∗ memRegion (a + 24#64) k) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 24#64) (n := 16) (k := k) (N := 16 + k) rfl (by bv_lin) hk
  rw [s1, memRegion_16_eq_words2 a]; dsimp only [words3At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_24_step (b : BitVec 64) (k : Nat) (hk : 24 + k ≤ 2 ^ 64) :
    memRegion b (24 + k) =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, words3At b w0 w1 w2 ∗ memRegion (b + 24#64) k) := by
  have s1 := memRegion_split' (b := b) (b' := b + 8#64) (n := 8) (k := 16 + k) (N := 24 + k) (by omega) (by bv_lin) hk
  have s2 := memRegion_split' (b := b + 8#64) (b' := b + 24#64) (n := 16) (k := k) (N := 16 + k) rfl (by bv_lin) (by omega)
  rw [s1, s2, ProofLib.memRegion_eight b, memRegion_16_eq_words2 b]; dsimp only [words3At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_56_eq_words7 (b : BitVec 64) :
    memRegion b 56 =
      ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        words7At b w0 w1 w2 w3 w4 w5 w6 := by
  have s1 := memRegion_split' (b := b) (b' := b + 8#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  rw [s1, ProofLib.memRegion_eight b, memRegion_48_eq_words6 b]; dsimp only [words7At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem unchunked3CapAt_eq_vec_unchunked2 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3CapAt A a bsLen epoch auth v3 =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v3) ∗
      unchunked2CapAt A (a + 24#64) bsLen epoch auth := by
  dsimp only [unchunked3CapAt, unchunked2CapAt]
  have h48 : a + 24#64 + 0x30#64 = a + 0x48#64 := by bv_lin
  have h24 : a + 0x18#64 = a + 24#64 := rfl
  rw [h48, h24]

def unchunked3CapHeap (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) : SepProp :=
  vecU8CapHeap A bsLen v3 w0 w1 w2 ∗ unchunked2CapHeap A bsLen epoch auth w3 w4 w5 w6 w7 w8 w9

theorem unchunked3CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3CapAt A a bsLen epoch auth v3 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
        words10At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ∗
        unchunked3CapHeap A bsLen epoch auth v3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 := by
  rw [unchunked3CapAt_eq_vec_unchunked2]
  refine Entails.trans (sepConj_mono (vecU8CapAt_extract_words A a bsLen v3)
    (unchunked2CapAt_extract_words A (a + 24#64) bsLen epoch auth)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
    ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w6 =>
    ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w8 =>
    ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w0 =>
    ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  dsimp only [words10At, words3At, unchunked3CapHeap]; exact Entails.of_eq (by ac_rfl)

theorem unchunked3CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    words10At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ∗
      unchunked3CapHeap A bsLen epoch auth v3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ⊢
      unchunked3CapAt A a bsLen epoch auth v3 := by
  rw [unchunked3CapAt_eq_vec_unchunked2]; dsimp only [words10At, words3At, unchunked3CapHeap]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (vecU8CapAt_of_words A a bsLen v3 w0 w1 w2)
      (unchunked2CapAt_of_words A (a + 24#64) bsLen epoch auth w3 w4 w5 w6 w7 w8 w9))

def optUnchunked3CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some (epoch, auth, v3) => unchunked3CapAt A a bsLen epoch auth v3

def optUnchunked3CapHeap (A : RustAlloc) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8)) →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some (epoch, auth, v3), w0, w1, w2, w3, w4, w5, w6, w7, w8, w9 =>
      unchunked3CapHeap A bsLen epoch auth v3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9

theorem memRegion_72_eq_words10_none (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
        words10At a noneCap w1 w2 w3 w4 w5 w6 w7 w8 w9 := by
  rw [none_memRegion_step a 56 (by decide), memRegion_56_eq_words7 (a + 24#64)]; dsimp only [words10At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem optUnchunked3CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8))) :
    optUnchunked3CapAt A a bsLen opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
        words10At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ∗
        optUnchunked3CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 := by
  cases opt with
  | none =>
    dsimp only [optUnchunked3CapAt, optUnchunked3CapHeap]; rw [memRegion_72_eq_words10_none]
    refine ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w1 =>
      ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w8 =>
      ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w6 =>
      ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w4 =>
      ProofLib.Entails.sepExists_elim fun w3 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
    refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
    simp only [pure_true, sepConj_emp]; exact Entails.refl _
  | some p => exact unchunked3CapAt_extract_words A a bsLen p.1 p.2.1 p.2.2

theorem optUnchunked3CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    words10At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ∗
      optUnchunked3CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 ⊢
      optUnchunked3CapAt A a bsLen opt := by
  cases opt with
  | none =>
    dsimp only [optUnchunked3CapAt, optUnchunked3CapHeap]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_72_eq_words10_none]
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); refine Entails.trans ?_ (Entails.sepExists_intro w6)
    refine Entails.trans ?_ (Entails.sepExists_intro w5); refine Entails.trans ?_ (Entails.sepExists_intro w4)
    refine Entails.trans ?_ (Entails.sepExists_intro w3); exact Entails.refl _
  | some p => exact unchunked3CapAt_of_words A a bsLen p.1 p.2.1 p.2.2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9

theorem optHeaderReceivedPBCapAt_eq_optUnchunked3 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBCapAt A a bsLen opt =
      optUnchunked3CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth, u.hdr)) := by cases opt <;> rfl

theorem optEkSentPBCapAt_eq_optUnchunked3 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBCapAt A a bsLen opt =
      optUnchunked3CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth, u.dk)) := by cases opt <;> rfl

theorem unchunked4CapAt_eq_vec_unchunked3 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8)) :
    unchunked4CapAt A a bsLen epoch auth v3 v4 =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v3) ∗
      unchunked3CapAt A (a + 24#64) bsLen epoch auth v4 := by
  dsimp only [unchunked4CapAt, unchunked3CapAt]
  have h24 : a + 0x18#64 = a + 24#64 := rfl
  have h48 : a + 24#64 + 0x18#64 = a + 0x30#64 := by bv_lin
  have h96 : a + 24#64 + 0x48#64 = a + 0x60#64 := by bv_lin
  rw [h24, h48, h96]

def unchunked4CapHeap (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) : SepProp :=
  vecU8CapHeap A bsLen v3 w0 w1 w2 ∗ unchunked3CapHeap A bsLen epoch auth v4 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12

theorem unchunked4CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8)) :
    unchunked4CapAt A a bsLen epoch auth v3 v4 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        words13At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ∗
        unchunked4CapHeap A bsLen epoch auth v3 v4 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 := by
  rw [unchunked4CapAt_eq_vec_unchunked3]
  refine Entails.trans (sepConj_mono (vecU8CapAt_extract_words A a bsLen v3)
    (unchunked3CapAt_extract_words A (a + 24#64) bsLen epoch auth v4)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
    ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w6 =>
    ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w8 =>
    ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w10 =>
    ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w12 =>
    ProofLib.Entails.sepExists_elim fun w0 => ProofLib.Entails.sepExists_elim fun w1 =>
    ProofLib.Entails.sepExists_elim fun w2 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w12)
  dsimp only [words13At, words3At, unchunked4CapHeap]; exact Entails.of_eq (by ac_rfl)

theorem unchunked4CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) :
    words13At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ∗
      unchunked4CapHeap A bsLen epoch auth v3 v4 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ⊢
      unchunked4CapAt A a bsLen epoch auth v3 v4 := by
  rw [unchunked4CapAt_eq_vec_unchunked3]; dsimp only [words13At, words3At, unchunked4CapHeap]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (vecU8CapAt_of_words A a bsLen v3 w0 w1 w2)
      (unchunked3CapAt_of_words A (a + 24#64) bsLen epoch auth v4 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12))

def optUnchunked4CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some (epoch, auth, v3, v4) => unchunked4CapAt A a bsLen epoch auth v3 v4

def optUnchunked4CapHeap (A : RustAlloc) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8)) →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some (epoch, auth, v3, v4), w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12 =>
      unchunked4CapHeap A bsLen epoch auth v3 v4 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12

theorem memRegion_80_eq_words10 (b : BitVec 64) :
    memRegion b 80 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
        words10At b w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 := by
  rw [memRegion_24_step b 56 (by decide), memRegion_56_eq_words7 (b + 24#64)]; dsimp only [words10At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_96_eq_words13_none (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
        words13At a noneCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 := by
  rw [none_memRegion_step a 80 (by decide), memRegion_80_eq_words10 (a + 24#64)]; dsimp only [words13At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem optUnchunked4CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8))) :
    optUnchunked4CapAt A a bsLen opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        words13At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ∗
        optUnchunked4CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 := by
  cases opt with
  | none =>
    dsimp only [optUnchunked4CapAt, optUnchunked4CapHeap]; rw [memRegion_96_eq_words13_none]
    refine ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w1 =>
      ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w4 =>
      ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w12 =>
      ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w10 =>
      ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w8 =>
      ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w6 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
    refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
    refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
    refine Entails.trans ?_ (Entails.sepExists_intro w12)
    simp only [pure_true, sepConj_emp]; exact Entails.refl _
  | some p => exact unchunked4CapAt_extract_words A a bsLen p.1 p.2.1 p.2.2.1 p.2.2.2

theorem optUnchunked4CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) :
    words13At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ∗
      optUnchunked4CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 ⊢
      optUnchunked4CapAt A a bsLen opt := by
  cases opt with
  | none =>
    dsimp only [optUnchunked4CapAt, optUnchunked4CapHeap]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_96_eq_words13_none]
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w5); refine Entails.trans ?_ (Entails.sepExists_intro w4)
    refine Entails.trans ?_ (Entails.sepExists_intro w3); refine Entails.trans ?_ (Entails.sepExists_intro w12)
    refine Entails.trans ?_ (Entails.sepExists_intro w11); refine Entails.trans ?_ (Entails.sepExists_intro w10)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); refine Entails.trans ?_ (Entails.sepExists_intro w6)
    exact Entails.refl _
  | some p => exact unchunked4CapAt_of_words A a bsLen p.1 p.2.1 p.2.2.1 p.2.2.2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12

theorem optHeaderSentPBCapAt_eq_optUnchunked4 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBCapAt A a bsLen opt =
      optUnchunked4CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth, u.ek, u.dk)) := by cases opt <;> rfl

theorem optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optUnchunkedEkSentCt1ReceivedPBCapAt A a bsLen opt =
      optUnchunked4CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) := by cases opt <;> rfl

theorem unchunked5CapAt_eq_vec_unchunked4 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a bsLen epoch auth v3 v4 v5 =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v3) ∗
      unchunked4CapAt A (a + 24#64) bsLen epoch auth v4 v5 := by
  dsimp only [unchunked5CapAt, unchunked4CapAt]
  have h24 : a + 0x18#64 = a + 24#64 := rfl
  have h48 : a + 24#64 + 0x18#64 = a + 0x30#64 := by bv_lin
  have h72 : a + 24#64 + 0x30#64 = a + 0x48#64 := by bv_lin
  have h120 : a + 24#64 + 0x60#64 = a + 0x78#64 := by bv_lin
  rw [h24, h48, h72, h120]

def unchunked5CapHeap (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) : SepProp :=
  vecU8CapHeap A bsLen v3 w0 w1 w2 ∗
  unchunked4CapHeap A bsLen epoch auth v4 v5 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

theorem unchunked5CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a bsLen epoch auth v3 v4 v5 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ w15 : BitVec 64,
        words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
        unchunked5CapHeap A bsLen epoch auth v3 v4 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 := by
  rw [unchunked5CapAt_eq_vec_unchunked4]
  refine Entails.trans (sepConj_mono (vecU8CapAt_extract_words A a bsLen v3)
    (unchunked4CapAt_extract_words A (a + 24#64) bsLen epoch auth v4 v5)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w4 =>
    ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w6 =>
    ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w8 =>
    ProofLib.Entails.sepExists_elim fun w9 => ProofLib.Entails.sepExists_elim fun w10 =>
    ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w12 =>
    ProofLib.Entails.sepExists_elim fun w13 => ProofLib.Entails.sepExists_elim fun w14 =>
    ProofLib.Entails.sepExists_elim fun w15 => ProofLib.Entails.sepExists_elim fun w0 =>
    ProofLib.Entails.sepExists_elim fun w1 => ProofLib.Entails.sepExists_elim fun w2 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0); refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
  refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
  refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
  refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
  refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
  refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w13)
  refine Entails.trans ?_ (Entails.sepExists_intro w14); refine Entails.trans ?_ (Entails.sepExists_intro w15)
  dsimp only [words16At, words3At, unchunked5CapHeap]; exact Entails.of_eq (by ac_rfl)

theorem unchunked5CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
      unchunked5CapHeap A bsLen epoch auth v3 v4 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
      unchunked5CapAt A a bsLen epoch auth v3 v4 v5 := by
  rw [unchunked5CapAt_eq_vec_unchunked4]; dsimp only [words16At, words3At, unchunked5CapHeap]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (vecU8CapAt_of_words A a bsLen v3 w0 w1 w2)
      (unchunked4CapAt_of_words A (a + 24#64) bsLen epoch auth v4 v5 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15))

def optUnchunked5CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some (epoch, auth, v3, v4, v5) => unchunked5CapAt A a bsLen epoch auth v3 v4 v5

def optUnchunked5CapHeap (A : RustAlloc) (bsLen : Nat) :
    Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some (epoch, auth, v3, v4, v5), w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 =>
      unchunked5CapHeap A bsLen epoch auth v3 v4 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

theorem memRegion_104_eq_words13 (b : BitVec 64) :
    memRegion b 104 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
        words13At b w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 := by
  rw [memRegion_24_step b 80 (by decide), memRegion_80_eq_words10 (b + 24#64)]; dsimp only [words13At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem memRegion_120_eq_words16_none (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64,
        words16At a noneCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 := by
  rw [none_memRegion_step a 104 (by decide), memRegion_104_eq_words13 (a + 24#64)]; dsimp only [words16At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem optUnchunked5CapAt_extract_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))) :
    optUnchunked5CapAt A a bsLen opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
      ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ w15 : BitVec 64,
        words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
        optUnchunked5CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 := by
  cases opt with
  | none =>
    dsimp only [optUnchunked5CapAt, optUnchunked5CapHeap]; rw [memRegion_120_eq_words16_none]
    refine ProofLib.Entails.sepExists_elim fun w2 => ProofLib.Entails.sepExists_elim fun w1 =>
      ProofLib.Entails.sepExists_elim fun w5 => ProofLib.Entails.sepExists_elim fun w4 =>
      ProofLib.Entails.sepExists_elim fun w3 => ProofLib.Entails.sepExists_elim fun w8 =>
      ProofLib.Entails.sepExists_elim fun w7 => ProofLib.Entails.sepExists_elim fun w6 =>
      ProofLib.Entails.sepExists_elim fun w15 => ProofLib.Entails.sepExists_elim fun w14 =>
      ProofLib.Entails.sepExists_elim fun w13 => ProofLib.Entails.sepExists_elim fun w12 =>
      ProofLib.Entails.sepExists_elim fun w11 => ProofLib.Entails.sepExists_elim fun w10 =>
      ProofLib.Entails.sepExists_elim fun w9 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w3)
    refine Entails.trans ?_ (Entails.sepExists_intro w4); refine Entails.trans ?_ (Entails.sepExists_intro w5)
    refine Entails.trans ?_ (Entails.sepExists_intro w6); refine Entails.trans ?_ (Entails.sepExists_intro w7)
    refine Entails.trans ?_ (Entails.sepExists_intro w8); refine Entails.trans ?_ (Entails.sepExists_intro w9)
    refine Entails.trans ?_ (Entails.sepExists_intro w10); refine Entails.trans ?_ (Entails.sepExists_intro w11)
    refine Entails.trans ?_ (Entails.sepExists_intro w12); refine Entails.trans ?_ (Entails.sepExists_intro w13)
    refine Entails.trans ?_ (Entails.sepExists_intro w14); refine Entails.trans ?_ (Entails.sepExists_intro w15)
    simp only [pure_true, sepConj_emp]; exact Entails.refl _
  | some p => exact unchunked5CapAt_extract_words A a bsLen p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

theorem optUnchunked5CapAt_of_words (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option (BitVec 64 × Option ProtoAuthenticator × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ∗
      optUnchunked5CapHeap A bsLen opt w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
      optUnchunked5CapAt A a bsLen opt := by
  cases opt with
  | none =>
    dsimp only [optUnchunked5CapAt, optUnchunked5CapHeap]
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) ?_
    refine Entails.pure_left fun hw0 => ?_; subst hw0; rw [memRegion_120_eq_words16_none]
    refine Entails.trans ?_ (Entails.sepExists_intro w2); refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w5); refine Entails.trans ?_ (Entails.sepExists_intro w4)
    refine Entails.trans ?_ (Entails.sepExists_intro w3); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); refine Entails.trans ?_ (Entails.sepExists_intro w6)
    refine Entails.trans ?_ (Entails.sepExists_intro w15); refine Entails.trans ?_ (Entails.sepExists_intro w14)
    refine Entails.trans ?_ (Entails.sepExists_intro w13); refine Entails.trans ?_ (Entails.sepExists_intro w12)
    refine Entails.trans ?_ (Entails.sepExists_intro w11); refine Entails.trans ?_ (Entails.sepExists_intro w10)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); exact Entails.refl _
  | some p =>
    exact unchunked5CapAt_of_words A a bsLen p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15

theorem optUnchunkedCt1SentPBCapAt_eq_optUnchunked5 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.Ct1Sent) :
    optUnchunkedCt1SentPBCapAt A a bsLen opt =
      optUnchunked5CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth, u.hdr, u.es, u.ct1)) := by cases opt <;> rfl

theorem optCt1SentEkReceivedPBCapAt_eq_optUnchunked5 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBCapAt A a bsLen opt =
      optUnchunked5CapAt A a bsLen (opt.map fun u => (u.epoch, u.auth, u.es, u.ek, u.ct1)) := by cases opt <;> rfl

/-- Common post-tag state at `entry + 2700#64` (`0x4f274`, `CBNZ X21, +676`). -/
def v1StateAfterTagPre (A : RustAlloc) (b : BitVec 64) (s0 : State)
    (x : V1StateMergeGhost) (m_res : Option (V1State × List (BitVec 8))) (s : State) : SepProp :=
  match m_res with
  | some (m', after) =>
    ⌜s.readReg64 (Reg.gpr 21#5) = 0#64 ∧ OptInnerStatePolyBound after.length m'.innerState⌝ ∗
      v1StateLoopPre A b s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs after
  | none =>
    ⌜s.readReg64 (Reg.gpr 21#5) ≠ 0#64⌝ ∗
      (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (s.readReg64 (Reg.gpr 21#5)) n) ∗
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗
      v1StateErrFrame A b s0 x.msgPtr x.bufRef x.slot x.ptr x.bs

def v1StateAfterTagPrePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (x : V1StateMergeGhost) (m_res : Option (V1State × List (BitVec 8))) (s : State) : SepProp :=
  match m_res with
  | some (m', after) =>
    ⌜s.readReg64 (Reg.gpr 21#5) = 0#64 ∧ OptInnerStatePolyBound after.length m'.innerState⌝ ∗
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m' x.bs after
  | none =>
    ⌜s.readReg64 (Reg.gpr 21#5) ≠ 0#64⌝ ∗
      (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (s.readReg64 (Reg.gpr 21#5)) n) ∗
      stackAt (s0.sp - 816#64) chunkedInlStack ∗
      memRegion (s0.sp - 816#64) 720 ∗
      v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs

end CryptoVerification.SpqrV1.Prost.MessageMerge
