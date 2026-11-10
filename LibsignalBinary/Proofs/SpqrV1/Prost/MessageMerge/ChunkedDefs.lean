/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBase
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1State
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# SPQR V1: Coordinated Definitions and Callee Specs for `V1State.Chunked.*` `prost::encoding::message::merge`

Provides coordinated callee `Spec` structures (`polyDecoderMergeSpec`, `polyEncoderMergeSpec`,
`unchunkedCt1SentMergeSpec`, `unchunkedEkSentCt1ReceivedMergeSpec`), representation predicates,
Hoare specifications, 128-byte stack-frame splits, and `Option` niche-initialization helpers for
the four `V1State.Chunked.*` `prost::encoding::message::merge` subroutines:
1. `V1State.Chunked.Ct1Received` (`0x4ae0c`)
2. `V1State.Chunked.Ct1Acknowledged` (`0x4bbb4`)
3. `V1State.Chunked.EkSentCt1Received` (`0x4c178`)
4. `V1State.Chunked.Ct1Sampled` (`0x4a390`)
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
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Coordinated Callee Specs (`PolyDecoder` / `PolyEncoder` / `Unchunked.{Ct1Sent,EkSentCt1Received}`) -/

def optAuthenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option ProtoAuthenticator → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => authenticatorPBCapAt A a bsLen auth

def unchunkedCt1SentPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (u : V1State.Unchunked.Ct1Sent) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr u.hdr) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.es) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
  optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
  ((a + 0x78#64) ↦₆₄ u.epoch)

def optUnchunkedCt1SentPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.Ct1Sent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some u => unchunkedCt1SentPBCapAt A a bsLen u

def unchunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (u : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr u.dk) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.ct1) ∗
  optAuthenticatorPBCapAt A (a + 0x30#64) bsLen u.auth ∗
  ((a + 0x60#64) ↦₆₄ u.epoch)

def optUnchunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some u => unchunkedEkSentCt1ReceivedPBCapAt A a bsLen u

namespace ChunkedMerge

abbrev unchunkedCt1SentMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, &mut &[u8]>"

abbrev unchunkedEkSentCt1ReceivedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, &mut &[u8]>"

abbrev unchunkedMergeStack : Nat := 160 + authMergeStack

structure UnchunkedCt1SentMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : V1State.Unchunked.Ct1Sent
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def unchunkedCt1SentMergeSpec (A : RustAlloc) : Spec UnchunkedCt1SentMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      unchunkedCt1SentPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp unchunkedMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp unchunkedMergeStack ∗
      match (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ unchunkedCt1SentPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.Ct1Sent, ct1SentPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure UnchunkedEkSentCt1ReceivedMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : V1State.Unchunked.EkSentCt1Received
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def unchunkedEkSentCt1ReceivedMergeSpec (A : RustAlloc) : Spec UnchunkedEkSentCt1ReceivedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      unchunkedEkSentCt1ReceivedPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp unchunkedMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp unchunkedMergeStack ∗
      match (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ unchunkedEkSentCt1ReceivedPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.EkSentCt1Received, ekSentCt1ReceivedPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem unchunkedCt1SentMerge_fnOff :
    libsignalSessionCode.fnOff unchunkedCt1SentMergeName = 0x4caa4 :=
  libsignalSessionCode_fnOff_0x4caa4

theorem unchunkedEkSentCt1ReceivedMerge_fnOff :
    libsignalSessionCode.fnOff unchunkedEkSentCt1ReceivedMergeName = 0x4c808 :=
  libsignalSessionCode_fnOff_0x4c808

end ChunkedMerge

open ChunkedMerge

/-! ## 2. Symbol Names and Offsets for `V1State.Chunked.*` `prost::encoding::message::merge` -/

abbrev chunkedCt1ReceivedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received, &mut &[u8]>"

abbrev chunkedCt1AcknowledgedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Acknowledged, &mut &[u8]>"

abbrev chunkedEkSentCt1ReceivedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received, &mut &[u8]>"

abbrev chunkedCt1SampledMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled, &mut &[u8]>"

theorem chunkedCt1ReceivedMerge_fnOff :
    libsignalSessionCode.fnOff chunkedCt1ReceivedMergeName = 0x4ae0c :=
  libsignalSessionCode_fnOff_0x4ae0c

theorem chunkedCt1AcknowledgedMerge_fnOff :
    libsignalSessionCode.fnOff chunkedCt1AcknowledgedMergeName = 0x4bbb4 :=
  libsignalSessionCode_fnOff_0x4bbb4

theorem chunkedEkSentCt1ReceivedMerge_fnOff :
    libsignalSessionCode.fnOff chunkedEkSentCt1ReceivedMergeName = 0x4c178 :=
  libsignalSessionCode_fnOff_0x4c178

theorem chunkedCt1SampledMerge_fnOff :
    libsignalSessionCode.fnOff chunkedCt1SampledMergeName = 0x4a390 :=
  libsignalSessionCode_fnOff_0x4a390

theorem protoPolynomialDecoderAt_eq_pb (A : RustAlloc) (a : BitVec 64) (m : PolynomialDecoder) :
    Poly.protoPolynomialDecoderAt A a (polyDecoderToProto m) =
      ProtoRepr.polynomialDecoderPBAt A a m := rfl

theorem protoPolynomialEncoderAt_eq_pb (A : RustAlloc) (a : BitVec 64) (m : PolynomialEncoder) :
    Poly.protoPolynomialEncoderAt A a (polyEncoderToProto m) =
      ProtoRepr.polynomialEncoderPBAt A a m := rfl

/-- Total stack budget for `V1State.Chunked.*::merge`:
    128-byte own stack frame + `unchunkedMergeStack` (`= polyMergeStack = 160 + skipField3Stack 97`). -/
abbrev chunkedMergeStack : Nat := 128 + unchunkedMergeStack

/-! ## 3. Monotonicity and Entailment Lemmas for `Unchunked` Cap Predicates -/

theorem optAuthenticatorPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) {m n : Nat} (hle : m ≤ n) :
    optAuthenticatorPBCapAt A a n opt ⊢ optAuthenticatorPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_mono A a auth hle

theorem optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBCapAt A a n opt ⊢ optAuthenticatorPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_entails_authenticatorPBAt A a n auth

theorem unchunkedCt1SentPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) {m n : Nat} (hle : m ≤ n) :
    unchunkedCt1SentPBCapAt A a n u ⊢ unchunkedCt1SentPBCapAt A a m u :=
  sepConj_mono (vecU8CapAt_mono A a u.hdr hle)
    (sepConj_mono (vecU8CapAt_mono A (a + 0x18#64) u.es hle)
      (sepConj_mono (vecU8CapAt_mono A (a + 0x30#64) u.ct1 hle)
        (sepConj_mono (optAuthenticatorPBCapAt_mono A (a + 0x48#64) u.auth hle)
          (Entails.refl _))))

theorem unchunkedCt1SentPBCapAt_entails_ct1SentPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (u : V1State.Unchunked.Ct1Sent) :
    unchunkedCt1SentPBCapAt A a n u ⊢ ct1SentPBAt A a u :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n u.hdr)
    (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n u.es)
      (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x30#64) n u.ct1)
        (sepConj_mono (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (a + 0x48#64) n u.auth)
          (Entails.refl _))))

theorem optUnchunkedCt1SentPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1Sent) {m n : Nat} (hle : m ≤ n) :
    optUnchunkedCt1SentPBCapAt A a n opt ⊢ optUnchunkedCt1SentPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunkedCt1SentPBCapAt_mono A a u hle

theorem optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.Ct1Sent) :
    optUnchunkedCt1SentPBCapAt A a n opt ⊢ optCt1SentPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunkedCt1SentPBCapAt_entails_ct1SentPBAt A a n u

theorem unchunkedEkSentCt1ReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received) {m n : Nat} (hle : m ≤ n) :
    unchunkedEkSentCt1ReceivedPBCapAt A a n u ⊢ unchunkedEkSentCt1ReceivedPBCapAt A a m u :=
  sepConj_mono (vecU8CapAt_mono A a u.dk hle)
    (sepConj_mono (vecU8CapAt_mono A (a + 0x18#64) u.ct1 hle)
      (sepConj_mono (optAuthenticatorPBCapAt_mono A (a + 0x30#64) u.auth hle)
        (Entails.refl _)))

theorem unchunkedEkSentCt1ReceivedPBCapAt_entails_ekSentCt1ReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (u : V1State.Unchunked.EkSentCt1Received) :
    unchunkedEkSentCt1ReceivedPBCapAt A a n u ⊢ ekSentCt1ReceivedPBAt A a u :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n u.dk)
    (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n u.ct1)
      (sepConj_mono (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (a + 0x30#64) n u.auth)
        (Entails.refl _)))

theorem optUnchunkedEkSentCt1ReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) {m n : Nat} (hle : m ≤ n) :
    optUnchunkedEkSentCt1ReceivedPBCapAt A a n opt ⊢ optUnchunkedEkSentCt1ReceivedPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunkedEkSentCt1ReceivedPBCapAt_mono A a u hle

theorem optUnchunkedEkSentCt1ReceivedPBCapAt_entails_optEkSentCt1ReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optUnchunkedEkSentCt1ReceivedPBCapAt A a n opt ⊢ optEkSentCt1ReceivedPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunkedEkSentCt1ReceivedPBCapAt_entails_ekSentCt1ReceivedPBAt A a n u

/-! ## 4. Pure `pts` / `polys` Length Growth Bounds for `PolynomialDecoder` and `PolynomialEncoder` -/

def optPolyDecoderPtsLen : Option PolynomialDecoder → Nat
  | none => 0
  | some d => d.pts.length

def optPolyEncoderPtsLen : Option PolynomialEncoder → Nat
  | none => 0
  | some e => e.pts.length

def optPolyEncoderPolysLen : Option PolynomialEncoder → Nat
  | none => 0
  | some e => e.polys.length

@[simp]
theorem optPolyDecoder_getD_default_pts_len (opt : Option PolynomialDecoder) :
    (opt.getD default).pts.length = optPolyDecoderPtsLen opt := by
  cases opt <;> rfl

@[simp]
theorem optPolyEncoder_getD_default_pts_len (opt : Option PolynomialEncoder) :
    (opt.getD default).pts.length = optPolyEncoderPtsLen opt := by
  cases opt <;> rfl

@[simp]
theorem optPolyEncoder_getD_default_polys_len (opt : Option PolynomialEncoder) :
    (opt.getD default).polys.length = optPolyEncoderPolysLen opt := by
  cases opt <;> rfl

theorem polyDecoder_mergeField_pts_len {m m' : PolynomialDecoder} {tag : BitVec 32}
    {wt : Proto.WireType} {rest rest' : List (BitVec 8)} {depth : Nat}
    (h : PolynomialDecoder.mergeField m tag wt rest depth = .ok (m', rest')) :
    m'.pts.length ≤ m.pts.length + 1 ∧ rest'.length ≤ rest.length := by
  have hle : rest'.length ≤ rest.length :=
    (protoPrefixStep_polynomialDecoder_mergeField m tag wt depth).length_le h
  refine ⟨?_, hle⟩
  unfold PolynomialDecoder.mergeField at h
  by_cases h1 : (tag == 1#32) = true
  · simp only [h1, ↓reduceIte] at h
    rcases hm : Proto.mergeUint32 wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨rfl, _⟩ := h; dsimp only; omega
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : (tag == 2#32) = true
    · simp only [h2, ↓reduceIte] at h
      rcases hm : Proto.mergeUint32 wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      obtain ⟨rfl, _⟩ := h; dsimp only; omega
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : (tag == 3#32) = true
      · simp only [h3, ↓reduceIte] at h
        unfold Proto.mergeRepeatedBytes at h
        rcases hm : Proto.mergeBytes wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        obtain ⟨rfl, _⟩ := h
        simp only [List.length_append, List.length_singleton]; omega
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : (tag == 4#32) = true
        · simp only [h4, ↓reduceIte] at h
          rcases hm : Proto.mergeBool wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          obtain ⟨rfl, _⟩ := h; dsimp only; omega
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          rcases hm : Proto.skipField wt tag rest depth with _ | r <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          obtain ⟨rfl, _⟩ := h; omega

theorem polyDecoder_mergeFieldsLoop_pts_len (fuel : Nat) :
    ∀ {m m' : PolynomialDecoder} {s : List (BitVec 8)} {depth : Nat},
      Proto.mergeFieldsLoop PolynomialDecoder.mergeField fuel m s depth = .ok m' →
      m'.pts.length ≤ m.pts.length + s.length := by
  induction fuel with
  | zero =>
    intro m m' s depth h
    cases s with
    | nil => cases h; omega
    | cons _ _ => nomatch h
  | succ fuel ih =>
    intro m m' s depth h
    cases s with
    | nil => cases h; omega
    | cons b tl =>
      simp only [Proto.mergeFieldsLoop, Bind.bind, Except.bind] at h
      rcases hdk : Proto.decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, r1⟩
      · rw [hdk] at h; nomatch h
      · rw [hdk] at h; dsimp only at h
        have hlt1 : r1.length < (b :: tl).length :=
          (proto_decodeKey_suffix (by rw [hdk]; rfl)).1
        rcases hmf : PolynomialDecoder.mergeField m tag wt r1 depth with _ | ⟨m1, r2⟩
        · rw [hmf] at h; nomatch h
        · rw [hmf] at h; dsimp only at h
          obtain ⟨hpts1, hr2⟩ := polyDecoder_mergeField_pts_len hmf
          have hih := ih h
          omega

theorem polyDecoder_mergeMessage_pts_len {wt : Proto.WireType}
    {m m' : PolynomialDecoder} {bs rest : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeMessage PolynomialDecoder.mergeField wt m bs depth).toOption = some (m', rest)) :
    m'.pts.length + rest.length < m.pts.length + bs.length := by
  cases depth with
  | zero =>
    rcases hcw : Proto.checkWireType .lengthDelimited wt with _ | ⟨⟩ <;>
      simp [Proto.mergeMessage, hcw, Bind.bind, Except.bind, Except.toOption] at h
  | succ depth' =>
    simp only [Proto.mergeMessage, Bind.bind, Except.bind] at h
    rcases hcw : Proto.checkWireType .lengthDelimited wt with _ | ⟨⟩
    · simp [hcw, Except.toOption] at h
    · simp only [hcw] at h
      rcases hdv : Proto.decodeVarint bs with _ | ⟨len, r0⟩
      · simp [hdv, Except.toOption] at h
      · simp only [hdv] at h
        have hlt0 : r0.length < bs.length := (proto_decodeVarint_suffix (by rw [hdv]; rfl)).1
        rcases hte : Proto.takeExact len.toNat r0 with _ | ⟨sub, after⟩
        · simp [hte, Except.toOption] at h
        · simp only [hte] at h
          rcases hloop : Proto.mergeFieldsLoop PolynomialDecoder.mergeField sub.length m sub depth' with _ | m2
          · simp [hloop, Except.toOption] at h
          · simp only [hloop, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hpts := polyDecoder_mergeFieldsLoop_pts_len _ hloop
            have hte' := hte
            rw [takeExact_eq_take_drop] at hte'
            split at hte'
            · rename_i hlen_le
              injection hte' with hpair; injection hpair with hsub hafter; subst hsub hafter
              rw [List.length_take_of_le hlen_le] at hpts
              rw [List.length_drop]
              omega
            · nomatch hte'

theorem polyEncoder_mergeField_pts_polys_len {m m' : PolynomialEncoder} {tag : BitVec 32}
    {wt : Proto.WireType} {rest rest' : List (BitVec 8)} {depth : Nat}
    (h : PolynomialEncoder.mergeField m tag wt rest depth = .ok (m', rest')) :
    m'.pts.length ≤ m.pts.length + 1 ∧ m'.polys.length ≤ m.polys.length + 1 ∧ rest'.length ≤ rest.length := by
  have hle : rest'.length ≤ rest.length :=
    (protoPrefixStep_polynomialEncoder_mergeField m tag wt depth).length_le h
  unfold PolynomialEncoder.mergeField at h
  by_cases h1 : (tag == 1#32) = true
  · simp only [h1, ↓reduceIte] at h
    rcases hm : Proto.mergeUint32 wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨rfl, _⟩ := h; dsimp only; exact ⟨by omega, by omega, hle⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : (tag == 2#32) = true
    · simp only [h2, ↓reduceIte] at h
      unfold Proto.mergeRepeatedBytes at h
      rcases hm : Proto.mergeBytes wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      obtain ⟨rfl, _⟩ := h
      simp only [List.length_append, List.length_singleton]; exact ⟨by omega, by omega, hle⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : (tag == 3#32) = true
      · simp only [h3, ↓reduceIte] at h
        unfold Proto.mergeRepeatedBytes at h
        rcases hm : Proto.mergeBytes wt rest with _ | ⟨v, r⟩ <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        obtain ⟨rfl, _⟩ := h
        simp only [List.length_append, List.length_singleton]; exact ⟨by omega, by omega, hle⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        rcases hm : Proto.skipField wt tag rest depth with _ | r <;> simp [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        obtain ⟨rfl, _⟩ := h; exact ⟨by omega, by omega, hle⟩

theorem polyEncoder_mergeFieldsLoop_pts_polys_len (fuel : Nat) :
    ∀ {m m' : PolynomialEncoder} {s : List (BitVec 8)} {depth : Nat},
      Proto.mergeFieldsLoop PolynomialEncoder.mergeField fuel m s depth = .ok m' →
      m'.pts.length ≤ m.pts.length + s.length ∧ m'.polys.length ≤ m.polys.length + s.length := by
  induction fuel with
  | zero =>
    intro m m' s depth h
    cases s with
    | nil => cases h; exact ⟨by omega, by omega⟩
    | cons _ _ => nomatch h
  | succ fuel ih =>
    intro m m' s depth h
    cases s with
    | nil => cases h; exact ⟨by omega, by omega⟩
    | cons b tl =>
      simp only [Proto.mergeFieldsLoop, Bind.bind, Except.bind] at h
      rcases hdk : Proto.decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, r1⟩
      · rw [hdk] at h; nomatch h
      · rw [hdk] at h; dsimp only at h
        have hlt1 : r1.length < (b :: tl).length :=
          (proto_decodeKey_suffix (by rw [hdk]; rfl)).1
        rcases hmf : PolynomialEncoder.mergeField m tag wt r1 depth with _ | ⟨m1, r2⟩
        · rw [hmf] at h; nomatch h
        · rw [hmf] at h; dsimp only at h
          obtain ⟨hpts1, hpolys1, hr2⟩ := polyEncoder_mergeField_pts_polys_len hmf
          obtain ⟨hih_pts, hih_polys⟩ := ih h
          exact ⟨by omega, by omega⟩

theorem polyEncoder_mergeMessage_pts_polys_len {wt : Proto.WireType}
    {m m' : PolynomialEncoder} {bs rest : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeMessage PolynomialEncoder.mergeField wt m bs depth).toOption = some (m', rest)) :
    m'.pts.length + rest.length < m.pts.length + bs.length ∧
      m'.polys.length + rest.length < m.polys.length + bs.length := by
  cases depth with
  | zero =>
    rcases hcw : Proto.checkWireType .lengthDelimited wt with _ | ⟨⟩ <;>
      simp [Proto.mergeMessage, hcw, Bind.bind, Except.bind, Except.toOption] at h
  | succ depth' =>
    simp only [Proto.mergeMessage, Bind.bind, Except.bind] at h
    rcases hcw : Proto.checkWireType .lengthDelimited wt with _ | ⟨⟩
    · simp [hcw, Except.toOption] at h
    · simp only [hcw] at h
      rcases hdv : Proto.decodeVarint bs with _ | ⟨len, r0⟩
      · simp [hdv, Except.toOption] at h
      · simp only [hdv] at h
        have hlt0 : r0.length < bs.length := (proto_decodeVarint_suffix (by rw [hdv]; rfl)).1
        rcases hte : Proto.takeExact len.toNat r0 with _ | ⟨sub, after⟩
        · simp [hte, Except.toOption] at h
        · simp only [hte] at h
          rcases hloop : Proto.mergeFieldsLoop PolynomialEncoder.mergeField sub.length m sub depth' with _ | m2
          · simp [hloop, Except.toOption] at h
          · simp only [hloop, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            obtain ⟨hpts, hpolys⟩ := polyEncoder_mergeFieldsLoop_pts_polys_len _ hloop
            have hte' := hte
            rw [takeExact_eq_take_drop] at hte'
            split at hte'
            · rename_i hlen_le
              injection hte' with hpair; injection hpair with hsub hafter; subst hsub hafter
              rw [List.length_take_of_le hlen_le] at hpts hpolys
              rw [List.length_drop]
              exact ⟨by omega, by omega⟩
            · nomatch hte'

/-! ## 5. Representation Predicates and Hoare `Spec`s for `V1State.Chunked.*` `merge` -/

def chunkedCt1ReceivedPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.Ct1Received) : SepProp :=
  optEkSentCt1ReceivedPBAt A a m.uc ∗
    optPolynomialEncoderPBAt A (a + 104#64) m.sendingEk

def chunkedCt1ReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.Ct1Received) : SepProp :=
  optUnchunkedEkSentCt1ReceivedPBCapAt A a bsLen m.uc ∗
    optPolynomialEncoderPBAt A (a + 104#64) m.sendingEk

theorem chunkedCt1ReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Received) {k n : Nat} (hle : k ≤ n) :
    chunkedCt1ReceivedPBCapAt A a n m ⊢ chunkedCt1ReceivedPBCapAt A a k m :=
  sepConj_mono_left (optUnchunkedEkSentCt1ReceivedPBCapAt_mono A a m.uc hle)

theorem chunkedCt1ReceivedPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.Ct1Received) :
    chunkedCt1ReceivedPBCapAt A a n m ⊢ chunkedCt1ReceivedPBAt A a m :=
  sepConj_mono_left (optUnchunkedEkSentCt1ReceivedPBCapAt_entails_optEkSentCt1ReceivedPBAt A a n m.uc)

theorem chunkedCt1ReceivedPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Received) :
    chunkedCt1ReceivedPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.Ct1Received, chunkedCt1ReceivedPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedCt1AcknowledgedPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.Ct1Acknowledged) : SepProp :=
  optCt1SentPBAt A a m.uc ∗
    optPolynomialDecoderPBAt A (a + 128#64) m.receivingEk

def chunkedCt1AcknowledgedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.Ct1Acknowledged) : SepProp :=
  optUnchunkedCt1SentPBCapAt A a bsLen m.uc ∗
    optPolynomialDecoderPBAt A (a + 128#64) m.receivingEk

theorem chunkedCt1AcknowledgedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Acknowledged) {k n : Nat} (hle : k ≤ n) :
    chunkedCt1AcknowledgedPBCapAt A a n m ⊢ chunkedCt1AcknowledgedPBCapAt A a k m :=
  sepConj_mono_left (optUnchunkedCt1SentPBCapAt_mono A a m.uc hle)

theorem chunkedCt1AcknowledgedPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.Ct1Acknowledged) :
    chunkedCt1AcknowledgedPBCapAt A a n m ⊢ chunkedCt1AcknowledgedPBAt A a m :=
  sepConj_mono_left (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A a n m.uc)

theorem chunkedCt1AcknowledgedPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Acknowledged) :
    chunkedCt1AcknowledgedPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.Ct1Acknowledged, chunkedCt1AcknowledgedPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedEkSentCt1ReceivedPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.EkSentCt1Received) : SepProp :=
  optEkSentCt1ReceivedPBAt A a m.uc ∗
    optPolynomialDecoderPBAt A (a + 104#64) m.receivingCt2

def chunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.EkSentCt1Received) : SepProp :=
  optUnchunkedEkSentCt1ReceivedPBCapAt A a bsLen m.uc ∗
    optPolynomialDecoderPBAt A (a + 104#64) m.receivingCt2

theorem chunkedEkSentCt1ReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.EkSentCt1Received) {k n : Nat} (hle : k ≤ n) :
    chunkedEkSentCt1ReceivedPBCapAt A a n m ⊢ chunkedEkSentCt1ReceivedPBCapAt A a k m :=
  sepConj_mono_left (optUnchunkedEkSentCt1ReceivedPBCapAt_mono A a m.uc hle)

theorem chunkedEkSentCt1ReceivedPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.EkSentCt1Received) :
    chunkedEkSentCt1ReceivedPBCapAt A a n m ⊢ chunkedEkSentCt1ReceivedPBAt A a m :=
  sepConj_mono_left (optUnchunkedEkSentCt1ReceivedPBCapAt_entails_optEkSentCt1ReceivedPBAt A a n m.uc)

theorem chunkedEkSentCt1ReceivedPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.EkSentCt1Received) :
    chunkedEkSentCt1ReceivedPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.EkSentCt1Received, chunkedEkSentCt1ReceivedPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedCt1SampledPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.Ct1Sampled) : SepProp :=
  optUnchunkedCt1SentPBCapAt A a bsLen m.uc ∗
    optPolynomialEncoderPBAt A (a + 128#64) m.sendingCt1 ∗
    optPolynomialDecoderPBAt A (a + 184#64) m.receivingEk

theorem chunkedCt1SampledPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Sampled) {k n : Nat} (hle : k ≤ n) :
    chunkedCt1SampledPBCapAt A a n m ⊢ chunkedCt1SampledPBCapAt A a k m :=
  sepConj_mono_left (optUnchunkedCt1SentPBCapAt_mono A a m.uc hle)

theorem chunkedCt1SampledPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.Ct1Sampled) :
    chunkedCt1SampledPBCapAt A a n m ⊢ chunkedCt1SampledPBAt A a m :=
  sepConj_mono_left (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A a n m.uc)

theorem chunkedCt1SampledPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct1Sampled) :
    chunkedCt1SampledPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.Ct1Sampled, chunkedCt1SampledPBAt A a m' :=
  Entails.sepExists_intro m

structure ChunkedCt1ReceivedMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : V1State.Chunked.Ct1Received
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def chunkedCt1ReceivedMergeSpec (A : RustAlloc) : Spec ChunkedCt1ReceivedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyEncoderPtsLen x.msg.sendingEk + x.bs.length < 2 ^ 56 ∧
      optPolyEncoderPolysLen x.msg.sendingEk + x.bs.length < 2 ^ 56⌝ ∗
      chunkedCt1ReceivedPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp chunkedMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt1ReceivedPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct1Received, chunkedCt1ReceivedPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedCt1AcknowledgedMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : V1State.Chunked.Ct1Acknowledged
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def chunkedCt1AcknowledgedMergeSpec (A : RustAlloc) : Spec ChunkedCt1AcknowledgedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length < 2 ^ 56⌝ ∗
      chunkedCt1AcknowledgedPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp chunkedMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt1AcknowledgedPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct1Acknowledged, chunkedCt1AcknowledgedPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedEkSentCt1ReceivedMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : V1State.Chunked.EkSentCt1Received
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def chunkedEkSentCt1ReceivedMergeSpec (A : RustAlloc) : Spec ChunkedEkSentCt1ReceivedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyDecoderPtsLen x.msg.receivingCt2 + x.bs.length < 2 ^ 56⌝ ∗
      chunkedEkSentCt1ReceivedPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp chunkedMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedEkSentCt1ReceivedPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.EkSentCt1Received, chunkedEkSentCt1ReceivedPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedCt1SampledMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : V1State.Chunked.Ct1Sampled
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def chunkedCt1SampledMergeSpec (A : RustAlloc) : Spec ChunkedCt1SampledMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyEncoderPtsLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 ∧
      optPolyEncoderPolysLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 ∧
      optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length < 2 ^ 56⌝ ∗
      chunkedCt1SampledPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp chunkedMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt1SampledPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct1Sampled, chunkedCt1SampledPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 6. Pure `mergeField` Step Lemmas for `V1State.Chunked.*` -/

theorem chunkedCt1Received_mergeField_tag1 (m : V1State.Chunked.Ct1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Received.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Received.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Received_mergeField_tag2 (m : V1State.Chunked.Ct1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Received.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with sendingEk := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Received.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Received_mergeField_other (m : V1State.Chunked.Ct1Received) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (V1State.Chunked.Ct1Received.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.Ct1Received.mergeField; simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem chunkedCt1Acknowledged_mergeField_tag1 (m : V1State.Chunked.Ct1Acknowledged) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Acknowledged.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Acknowledged.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Acknowledged_mergeField_tag2 (m : V1State.Chunked.Ct1Acknowledged) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Acknowledged.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with receivingEk := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Acknowledged.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Acknowledged_mergeField_other (m : V1State.Chunked.Ct1Acknowledged) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (V1State.Chunked.Ct1Acknowledged.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.Ct1Acknowledged.mergeField; simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem chunkedEkSentCt1Received_mergeField_tag1 (m : V1State.Chunked.EkSentCt1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.EkSentCt1Received.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedEkSentCt1Received_mergeField_tag3 (m : V1State.Chunked.EkSentCt1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingCt2.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with receivingCt2 := some v }, rest')) := by
  unfold V1State.Chunked.EkSentCt1Received.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl, show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingCt2.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedEkSentCt1Received_mergeField_other (m : V1State.Chunked.EkSentCt1Received) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne3 : tag ≠ 3) :
    (V1State.Chunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.EkSentCt1Received.mergeField; simp only [hb1, hb3, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem chunkedCt1Sampled_mergeField_tag1 (m : V1State.Chunked.Ct1Sampled) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Sampled.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Sampled.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Sampled_mergeField_tag2 (m : V1State.Chunked.Ct1Sampled) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Sampled.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with sendingCt1 := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Sampled.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Sampled_mergeField_tag3 (m : V1State.Chunked.Ct1Sampled) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.Ct1Sampled.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with receivingEk := some v }, rest')) := by
  unfold V1State.Chunked.Ct1Sampled.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl, show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedCt1Sampled_mergeField_other (m : V1State.Chunked.Ct1Sampled) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) :
    (V1State.Chunked.Ct1Sampled.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.Ct1Sampled.mergeField; simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

/-! ## 7. 128-Byte Stack Frame (`chunkedMergeStack`) and Sub-Call Stack Splits -/

abbrev chunkedBelow (sp : BitVec 64) : SepProp := stackAt (sp - 128#64) unchunkedMergeStack

private theorem bv_sub_add_128 (sp v : BitVec 64) : sp - 128#64 = sp - (v + 128#64) + v := by bv_lin
private theorem bv_sub_128_sub (sp v : BitVec 64) : sp - 128#64 - v = sp - (v + 128#64) := by bv_lin
private theorem bv_sub_128_add_cancel (sp u w : BitVec 64) : sp - 128#64 - w = sp - 128#64 - (u + w) + u := by bv_lin

theorem stackAt_chunkedMerge (sp : BitVec 64) :
    stackAt sp chunkedMergeStack =
      (∃∗ v19 : BitVec 64, ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
        ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64, ∃∗ v24 : BitVec 64,
        ∃∗ v25 : BitVec 64, ∃∗ v_lr : BitVec 64, ∃∗ v_fp : BitVec 64,
        chunkedBelow sp ∗ memRegion (sp - 128#64) 48 ∗
          ((sp - 80#64) ↦₆₄ v_fp) ∗ ((sp - 72#64) ↦₆₄ v_lr) ∗
          ((sp - 64#64) ↦₆₄ v25) ∗ memRegion (sp - 56#64) 8 ∗
          ((sp - 48#64) ↦₆₄ v24) ∗ ((sp - 40#64) ↦₆₄ v23) ∗
          ((sp - 32#64) ↦₆₄ v22) ∗ ((sp - 24#64) ↦₆₄ v21) ∗
          ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
  simp only [stackAt, chunkedBelow]
  have hlen : chunkedMergeStack = unchunkedMergeStack + 128 := by simp only [chunkedMergeStack]; omega
  have hbound : chunkedMergeStack ≤ 2 ^ 64 := by
    simp only [chunkedMergeStack, unchunkedMergeStack, authMergeStack, skipField3Stack,
      decodeVarint2Stack, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]; omega
  have hbit : BitVec.ofNat 64 chunkedMergeStack = BitVec.ofNat 64 unchunkedMergeStack + 128#64 := by
    rw [hlen, BitVec.ofNat_add]
  have h1 := memRegion_split' (b := sp - BitVec.ofNat 64 chunkedMergeStack) (b' := sp - 128#64)
    (n := unchunkedMergeStack) (k := 128) (N := chunkedMergeStack) hlen (by rw [hbit]; exact bv_sub_add_128 sp _) hbound
  have hsp_sub : sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack = sp - BitVec.ofNat 64 chunkedMergeStack := by
    rw [hbit]; exact bv_sub_128_sub sp _
  have h2 := memRegion_split' (b := sp - 128#64) (b' := sp - 80#64) (n := 48) (k := 80) (N := 128) rfl (by bv_lin) (by decide)
  have h3 := memRegion_split' (b := sp - 80#64) (b' := sp - 72#64) (n := 8) (k := 72) (N := 80) rfl (by bv_lin) (by decide)
  have h4 := memRegion_split' (b := sp - 72#64) (b' := sp - 64#64) (n := 8) (k := 64) (N := 72) rfl (by bv_lin) (by decide)
  have h5 := memRegion_split' (b := sp - 64#64) (b' := sp - 56#64) (n := 8) (k := 56) (N := 64) rfl (by bv_lin) (by decide)
  have h6 := memRegion_split' (b := sp - 56#64) (b' := sp - 48#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  have h7 := memRegion_split' (b := sp - 48#64) (b' := sp - 40#64) (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have h8 := memRegion_split' (b := sp - 40#64) (b' := sp - 32#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have h9 := memRegion_split' (b := sp - 32#64) (b' := sp - 24#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have h10 := memRegion_split' (b := sp - 24#64) (b' := sp - 16#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have h11 := memRegion_split' (b := sp - 16#64) (b' := sp - 8#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [hsp_sub, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    Prost.memRegion_eight (sp - 80#64), Prost.memRegion_eight (sp - 72#64), Prost.memRegion_eight (sp - 64#64),
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64), Prost.memRegion_eight (sp - 32#64),
    Prost.memRegion_eight (sp - 24#64), Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

abbrev chunkedSkipRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack) 64

theorem chunkedBelow_skipField3_98 (sp : BitVec 64) :
    chunkedBelow sp = chunkedSkipRest sp ∗ stackAt (sp - 128#64) (skipField3Stack 98) := by
  simp only [chunkedBelow, chunkedSkipRest, stackAt]
  have hlen : unchunkedMergeStack = 64 + skipField3Stack 98 := rfl
  have hbit : BitVec.ofNat 64 unchunkedMergeStack = BitVec.ofNat 64 64 + BitVec.ofNat 64 (skipField3Stack 98) := rfl
  exact memRegion_split' (b := sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack)
    (b' := sp - 128#64 - BitVec.ofNat 64 (skipField3Stack 98)) (n := 64) (k := skipField3Stack 98)
    (N := unchunkedMergeStack) hlen (by rw [hbit]; exact bv_sub_128_add_cancel sp _ _) (by decide)

theorem chunkedBelow_skipField3_98_entails (sp : BitVec 64) :
    chunkedSkipRest sp ∗ stackAt (sp - 128#64) (skipField3Stack 98) ⊢ chunkedBelow sp :=
  Entails.of_eq (chunkedBelow_skipField3_98 sp).symm

abbrev chunkedLeafRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack) (160 + 98 * 0x60)

theorem chunkedBelow_leaf (sp : BitVec 64) :
    chunkedBelow sp = chunkedLeafRest sp ∗ stackAt (sp - 128#64) decodeVarint2Stack := by
  simp only [chunkedBelow, chunkedLeafRest, stackAt]
  have hlen : unchunkedMergeStack = (160 + 98 * 0x60) + decodeVarint2Stack := rfl
  have hbit : BitVec.ofNat 64 unchunkedMergeStack = BitVec.ofNat 64 (160 + 98 * 0x60) + BitVec.ofNat 64 decodeVarint2Stack := rfl
  exact memRegion_split' (b := sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack)
    (b' := sp - 128#64 - BitVec.ofNat 64 decodeVarint2Stack) (n := 160 + 98 * 0x60) (k := decodeVarint2Stack)
    (N := unchunkedMergeStack) hlen (by rw [hbit]; exact bv_sub_128_add_cancel sp _ _) (by decide)

theorem chunkedBelow_leaf_entails (sp : BitVec 64) :
    chunkedLeafRest sp ∗ stackAt (sp - 128#64) decodeVarint2Stack ⊢ chunkedBelow sp :=
  Entails.of_eq (chunkedBelow_leaf sp).symm

abbrev chunkedErrRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack) (160 + 98 * 0x60 + 0x80)

theorem chunkedBelow_err (sp : BitVec 64) :
    chunkedBelow sp = chunkedErrRest sp ∗ stackAt (sp - 128#64) decodeErrorHookStack := by
  simp only [chunkedBelow, chunkedErrRest, stackAt]
  have hlen : unchunkedMergeStack = (160 + 98 * 0x60 + 0x80) + decodeErrorHookStack := rfl
  have hbit : BitVec.ofNat 64 unchunkedMergeStack = BitVec.ofNat 64 (160 + 98 * 0x60 + 0x80) + BitVec.ofNat 64 decodeErrorHookStack := rfl
  exact memRegion_split' (b := sp - 128#64 - BitVec.ofNat 64 unchunkedMergeStack)
    (b' := sp - 128#64 - BitVec.ofNat 64 decodeErrorHookStack) (n := 160 + 98 * 0x60 + 0x80) (k := decodeErrorHookStack)
    (N := unchunkedMergeStack) hlen (by rw [hbit]; exact bv_sub_128_add_cancel sp _ _) (by decide)

theorem chunkedBelow_err_entails (sp : BitVec 64) :
    chunkedErrRest sp ∗ stackAt (sp - 128#64) decodeErrorHookStack ⊢ chunkedBelow sp :=
  Entails.of_eq (chunkedBelow_err sp).symm

theorem memRegion_48_split_128 (sp : BitVec 64) :
    memRegion (sp - 128#64) 48 = (∃∗ v : BitVec 64, (sp - 128#64) ↦₆₄ v) ∗ memRegion (sp - 120#64) 40 := by
  rw [memRegion_48_split (sp - 128#64), bv_sub_add_lit sp 128 8]

theorem memRegion_48_split2_128 (sp : BitVec 64) :
    memRegion (sp - 128#64) 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ((sp - 128#64) ↦₆₄ v1) ∗ ((sp - 120#64) ↦₆₄ v0)) ∗
        memRegion (sp - 112#64) 32 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide)
  have s2 := ProofLib.memRegion_split (sp - 120#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 128 8] at s1; rw [ProofLib.bv_sub_add_lit sp 120 8] at s2
  rw [s1, s2, ProofLib.memRegion_eight (sp - 128#64), ProofLib.memRegion_eight (sp - 120#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; ac_rfl

theorem pointsTo64_memRegion32_entails_40_128 (sp v0 : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v0) ∗ memRegion (sp - 112#64) 32 ⊢ memRegion (sp - 120#64) 40 := by
  have s2 := ProofLib.memRegion_split (sp - 120#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 120 8] at s2; rw [s2]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp - 120#64) v0)

theorem pointsTo64_memRegion40_entails_48_128 (sp v0 : BitVec 64) :
    ((sp - 128#64) ↦₆₄ v0) ∗ memRegion (sp - 120#64) 40 ⊢ memRegion (sp - 128#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 128 8] at s1; rw [s1]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp - 128#64) v0)

theorem memRegion8_memRegion40_entails_48_128 (sp : BitVec 64) :
    memRegion (sp - 128#64) 8 ∗ memRegion (sp - 120#64) 40 ⊢ memRegion (sp - 128#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 128 8] at s1; exact Entails.of_eq s1.symm

theorem memRegion_48_wtErr128 (sp : BitVec 64) :
    memRegion (sp - 128#64) 48 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ v0 : BitVec 64,
        ((sp - 128#64) ↦₆₄ v0) ∗ ((sp - 120#64) ↦₈ b0) ∗ ((sp - 119#64) ↦₈ b1)) ∗
        memRegion (sp - 118#64) 38 := by
  have s1 := ProofLib.memRegion_split (sp - 128#64) 8 40 (by decide)
  have s2 := ProofLib.memRegion_split (sp - 120#64) 1 39 (by decide)
  have s3 := ProofLib.memRegion_split (sp - 119#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 128 8] at s1; rw [ProofLib.bv_sub_add_lit sp 120 1] at s2
  rw [ProofLib.bv_sub_add_lit sp 119 1] at s3
  change memRegion (sp - 119#64) 39 = memRegion (sp - 119#64) 1 ∗ memRegion (sp - 118#64) 38 at s3
  rw [s1, s2, s3, ProofLib.memRegion_eight (sp - 128#64), ProofLib.memRegion_one (sp - 120#64), ProofLib.memRegion_one (sp - 119#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; ac_rfl

theorem wtErr128_entails_memRegion40 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 120#64) ↦₈ b0) ∗ ((sp - 119#64) ↦₈ b1) ∗ memRegion (sp - 118#64) 38 ⊢ memRegion (sp - 120#64) 40 := by
  have s2 := ProofLib.memRegion_split (sp - 120#64) 1 39 (by decide)
  have s3 := ProofLib.memRegion_split (sp - 119#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 120 1] at s2; rw [ProofLib.bv_sub_add_lit sp 119 1] at s3; rw [s2, s3]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0) (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

/-! ## 8. Shared `Option` Default-Init, Error Depth, and Callee-Saved Helpers -/

theorem vecU8Buf_entails_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf; refine Entails.pure_left fun h => ?_
  exact Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem vecVecU8Buf_entails_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) :
    vecVecU8Buf A cap ptr bss ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecVecU8Buf A cap ptr bss := by
  unfold vecVecU8Buf vecBuf; refine Entails.pure_left fun h => ?_
  exact Entails.pure_right (by omega) (Entails.pure_right h (Entails.refl _))

theorem pointsTo_zero_entails_vecU8CapAt (A : RustAlloc) (a ptr : BitVec 64) (n : Nat) (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr []) := by
  refine Entails.trans ?_ (Entails.sepExists_right 0#64 (Entails.sepExists_right ptr (Entails.refl _)))
  refine Entails.pure_right (bytesMergeCapOk_zero (n := n)) ?_
  rw [vecU8At_eq_header_sep_buf, vecHeader]; unfold vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  have hp : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  exact Entails.pure_right hp (Entails.refl _)

theorem pointsTo_zero_entails_vecVecU8At (A : RustAlloc) (a ptr : BitVec 64) (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢ vecVecU8At A a [] := by
  rw [vecVecU8At_eq_exists_pin]
  refine Entails.trans ?_ (Entails.sepExists_right (VecPin.mk 0#64 ptr) (Entails.refl _))
  rw [vecVecU8PinnedAt_eq_header_buf]; unfold vecVecU8Buf vecBuf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by dsimp only [List.length]; ac_rfl)

theorem memRegion_ekSentCt1Received_none_split (a : BitVec 64) :
    memRegion (a + 8#64) 96 =
      ∃∗ v96 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
      ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((a + 8#64) ↦₆₄ v8) ∗ ((a + 16#64) ↦₆₄ v16) ∗ ((a + 24#64) ↦₆₄ v24) ∗ ((a + 32#64) ↦₆₄ v32) ∗
        ((a + 40#64) ↦₆₄ v40) ∗ ((a + 48#64) ↦₆₄ v48) ∗ memRegion (a + 56#64) 40 ∗ ((a + 96#64) ↦₆₄ v96) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 88) (N := 96) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 80) (N := 88) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 72) (N := 80) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 64) (N := 72) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := a + 40#64) (b' := a + 48#64) (n := 8) (k := 56) (N := 64) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := a + 48#64) (b' := a + 56#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  have s7 := memRegion_split' (b := a + 56#64) (b' := a + 96#64) (n := 40) (k := 8) (N := 48) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64), ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
    ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 96#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem default_ekSentCt1Received_entails_cap (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 56#64) 40 ∗ ((a + 96#64) ↦₆₄ 0#64) ⊢
      unchunkedEkSentCt1ReceivedPBCapAt A a n default := by
  unfold unchunkedEkSentCt1ReceivedPBCapAt
  change _ ⊢ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr []) ∗
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A (a + 24#64) cap ptr []) ∗
    ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64 ∗ memRegion (a + 48#64 + 8#64) 40) ∗ ((a + 96#64) ↦₆₄ 0#64)
  have h1 := pointsTo_zero_entails_vecU8CapAt A a 1#64 n (by decide)
  have h2 := pointsTo_zero_entails_vecU8CapAt A (a + 24#64) 1#64 n (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_lin
  rw [h32, h40] at h2; rw [h56]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

theorem memRegion_polyEncoder_none_split (p : BitVec 64) :
    memRegion (p + 8#64) 48 =
      ∃∗ v48 : BitVec 32, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
      ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((p + 8#64) ↦₆₄ v8) ∗ ((p + 16#64) ↦₆₄ v16) ∗ ((p + 24#64) ↦₆₄ v24) ∗
        ((p + 32#64) ↦₆₄ v32) ∗ ((p + 40#64) ↦₆₄ v40) ∗ ((p + 48#64) ↦₃₂ v48) ∗ memRegion (p + 52#64) 4 := by
  have s1 := memRegion_split' (b := p + 8#64) (b' := p + 16#64) (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := p + 16#64) (b' := p + 24#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := p + 24#64) (b' := p + 32#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := p + 32#64) (b' := p + 40#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := p + 40#64) (b' := p + 48#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := p + 48#64) (b' := p + 52#64) (n := 4) (k := 4) (N := 8) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, ProofLib.memRegion_eight (p + 8#64), ProofLib.memRegion_eight (p + 16#64),
    ProofLib.memRegion_eight (p + 24#64), ProofLib.memRegion_eight (p + 32#64), ProofLib.memRegion_eight (p + 40#64),
    ProofLib.memRegion_four (p + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem default_polyEncoder_entails_pb (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      polynomialEncoderPBAt A p default := by
  unfold polynomialEncoderPBAt
  change _ ⊢ vecVecU8At A p [] ∗ vecVecU8At A (p + 24#64) [] ∗ ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  have h1 := pointsTo_zero_entails_vecVecU8At A p 8#64 (by decide)
  have h2 := pointsTo_zero_entails_vecVecU8At A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

theorem decodeErrorWith_zero_entails_le3 (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 0 ⊢ ∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  simp only [Nat.zero_le, pure_true, emp_sepConj]; exact Entails.refl _

theorem decodeErrorWith_succ_entails_le3 (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 2) :
    decodeErrorAtStackLen A e (n + 1) ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k :=
  Entails.trans (Entails.pure_right (by omega : n + 1 ≤ 3) (Entails.refl _)) (Entails.sepExists_right (n + 1) (Entails.refl _))

@[simp] theorem optPolyEncoderPtsLen_eq_getD (opt : Option PolynomialEncoder) :
    optPolyEncoderPtsLen opt = (opt.getD default).pts.length := by cases opt <;> rfl
@[simp] theorem optPolyEncoderPolysLen_eq_getD (opt : Option PolynomialEncoder) :
    optPolyEncoderPolysLen opt = (opt.getD default).polys.length := by cases opt <;> rfl
@[simp] theorem optPolyDecoderPtsLen_eq_getD (opt : Option PolynomialDecoder) :
    optPolyDecoderPtsLen opt = (opt.getD default).pts.length := by cases opt <;> rfl

def chunkedSavedRegs (s0 : State) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ memRegion (s0.sp - 56#64) 8 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

def ChunkedHighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
    s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
    s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
    calleeSavedVRegs s = calleeSavedVRegs s0

def ChunkedLoopRegs (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 23#5) = 1#64 ∧
    s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 ∧
    s.readReg64 (Reg.gpr 25#5) = 8#64 ∧ ChunkedHighCalleeSaved s0 s

theorem proto_mergeMessage_len_le {M : Type} {mf : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {wt : Proto.WireType} {m m' : M} {bs rest : List (BitVec 8)} {d : Nat}
    (h : (Proto.mergeMessage mf wt m bs d).toOption = some (m', rest)) : rest.length ≤ bs.length :=
  (proto_mergeMessage_suffix h).1

theorem chunkedBelow_eq_unchunked (sp : BitVec 64) : chunkedBelow sp = stackAt (sp - 128#64) unchunkedMergeStack := rfl
theorem chunkedBelow_eq_poly (sp : BitVec 64) : chunkedBelow sp = stackAt (sp - 128#64) polyMergeStack := rfl

end CryptoVerification.SpqrV1.Prost.MessageMerge
