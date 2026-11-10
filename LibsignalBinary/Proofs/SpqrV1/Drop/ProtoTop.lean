/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.TopDecodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

/-!
# Drop Glue for `Option<v1_state::InnerState>` (Specifications and Simple/Compound Variants)

Defines the `.rodata` jump table, representation predicates (`protoInnerStateAt`,
`optProtoInnerStateAt`, `protoPqRatchetStateAt`), and specifications for
`core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>`
(`0x4c0d4`, Block `267`) and `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>`
(`0x4c460`, Block `270`), together with the non-looping per-variant proofs of Block `267`.
-/

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L14

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## `.rodata` Jump Table for `Option<V1State.InnerState>` -/

/-- The 10-byte jump table for `Option<spqr::proto::pq_ratchet::v1_state::InnerState>`
    (base `entry + 92`, scaled by `<< 2`). -/
def optProtoInnerStateJumpTableBytes : List (BitVec 8) :=
  [34#8, 0#8, 54#8, 0#8, 5#8, 97#8, 102#8, 59#8, 135#8, 10#8]

/-- Read-only separation-logic assertion for the 10-byte jump table. -/
def optProtoInnerStateJumpTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_bytes% "220036000561663b870a")) ↦ᵣ optProtoInnerStateJumpTableBytes

abbrev optProtoInnerStateJumpTableSym : String :=
  "spqr:.rodata.core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"

def optProtoInnerStateJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsmpl.ρ optProtoInnerStateJumpTableSym) ↦ᵣ optProtoInnerStateJumpTableBytes

theorem fnAddr_adrp_4c118 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr dropOptProtoInnerStateName + 68#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := by
  rw [Program.fnAddr_rebase, dropOptProtoInnerState_fnOff]
  revert hb; bv_bits

/-! ## Representation Predicates for `V1State.InnerState` (`224` B) and `PqRatchetState` (`352` B) -/

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled` at `a` (`56` bytes = `0x38`):
    * `+0`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+48`: `epoch: u64` (8B) -/
def protoUnchunkedKeysUnsampledAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.KeysUnsampled) : SepProp :=
  optProtoAuthenticatorAt A a st.auth ∗
    ((a + 48#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled>` at `a` (`56` bytes = `0x38`):
    * `none`: `(a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48` (`-2` niche)
    * `some st`: `protoUnchunkedKeysUnsampledAt A a st` -/
def optProtoUnchunkedKeysUnsampledAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.KeysUnsampled → SepProp
  | none => (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48
  | some st => protoUnchunkedKeysUnsampledAt A a st

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent` at `a` (`56` bytes = `0x38`):
    * `+0`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+48`: `epoch: u64` (8B) -/
def protoUnchunkedCt2SentAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct2Sent) : SepProp :=
  optProtoAuthenticatorAt A a st.auth ∗
    ((a + 48#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent>` at `a` (`56` bytes = `0x38`):
    * `none`: `(a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48` (`-2` niche)
    * `some st`: `protoUnchunkedCt2SentAt A a st` -/
def optProtoUnchunkedCt2SentAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.Ct2Sent → SepProp
  | none => (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48
  | some st => protoUnchunkedCt2SentAt A a st

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent` at `a` (`104` bytes = `0x68`):
    * `+0`: `ek: Vec<u8>` (24B)
    * `+24`: `dk: Vec<u8>` (24B)
    * `+48`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+96`: `epoch: u64` (8B) -/
def protoUnchunkedHeaderSentAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.HeaderSent) : SepProp :=
  vecU8 A a st.ek ∗
    vecU8 A (a + 24#64) st.dk ∗
    optProtoAuthenticatorAt A (a + 48#64) st.auth ∗
    ((a + 96#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent>` at `a` (`104` bytes = `0x68`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96` (`-1` niche)
    * `some st`: `protoUnchunkedHeaderSentAt A a st` -/
def optProtoUnchunkedHeaderSentAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some st => protoUnchunkedHeaderSentAt A a st

/-- `spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled` at `a` (`56` bytes = `0x38`, align `8`):
    * `+0..+56`: `uc: Option<V1State.Unchunked.KeysUnsampled>` (`56`B) -/
def protoChunkedKeysUnsampledAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.KeysUnsampled) : SepProp :=
  optProtoUnchunkedKeysUnsampledAt A a st.uc

/-- `spqr::proto::pq_ratchet::v1_state::chunked::KeysSampled` at `a` (`160` bytes = `0xa0`, align `8`):
    * `+0..+104`: `uc: Option<V1State.Unchunked.HeaderSent>` (`104`B)
    * `+104..+160`: `sending_hdr: Option<PolynomialEncoder>` (`56`B) -/
def protoChunkedKeysSampledAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.KeysSampled) : SepProp :=
  optProtoUnchunkedHeaderSentAt A a st.uc ∗
    optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingHdr.map pbToProtoPolyEncoder)

/-- `spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled` at `a` (`224` bytes = `0xe0`, align `8`):
    * `+0..+128`: `uc: Option<V1State.Unchunked.Ct1Sent>` (`128`B)
    * `+128..+184`: `sending_ct1: Option<PolynomialEncoder>` (`56`B)
    * `+184..+224`: `receiving_ek: Option<PolynomialDecoder>` (`40`B) -/
def protoChunkedCt1SampledAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.Ct1Sampled) : SepProp :=
  optProtoUnchunkedCt1SentAt A a st.uc ∗
    optProtoPolynomialEncoderAt A (a + 128#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
    optProtoPolynomialDecoderAt A (a + 184#64) (st.receivingEk.map pbToProtoPolyDecoder)

/-- `spqr::proto::pq_ratchet::v1_state::chunked::EkReceivedCt1Sampled` at `a` (`184` bytes = `0xb8`, align `8`):
    * `+0..+128`: `uc: Option<V1State.Unchunked.Ct1SentEkReceived>` (`128`B)
    * `+128..+184`: `sending_ct1: Option<PolynomialEncoder>` (`56`B) -/
def protoChunkedEkReceivedCt1SampledAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.EkReceivedCt1Sampled) : SepProp :=
  optProtoUnchunkedCt1SentEkReceivedAt A a st.uc ∗
    optProtoPolynomialEncoderAt A (a + 128#64) (st.sendingCt1.map pbToProtoPolyEncoder)

/-- `spqr::proto::pq_ratchet::v1_state::chunked::Ct1Acknowledged` at `a` (`168` bytes = `0xa8`, align `8`):
    * `+0..+128`: `uc: Option<V1State.Unchunked.Ct1Sent>` (`128`B)
    * `+128..+168`: `receiving_ek: Option<PolynomialDecoder>` (`40`B) -/
def protoChunkedCt1AcknowledgedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.Ct1Acknowledged) : SepProp :=
  optProtoUnchunkedCt1SentAt A a st.uc ∗
    optProtoPolynomialDecoderAt A (a + 128#64) (st.receivingEk.map pbToProtoPolyDecoder)

/-- `spqr::proto::pq_ratchet::v1_state::chunked::Ct2Sampled` at `a` (`112` bytes = `0x70`, align `8`):
    * `+0..+56`: `sending_ct2: Option<PolynomialEncoder>` (`56`B)
    * `+56..+112`: `uc: Option<V1State.Unchunked.Ct2Sent>` (`56`B) -/
def protoChunkedCt2SampledAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.Ct2Sampled) : SepProp :=
  optProtoPolynomialEncoderAt A a (st.sendingCt2.map pbToProtoPolyEncoder) ∗
    optProtoUnchunkedCt2SentAt A (a + 56#64) st.uc

/-- Representation predicate for `spqr::proto::pq_ratchet::v1_state::InnerState` at `a` (`224` bytes = `0xe0`). -/
def protoInnerStateAt (A : RustAlloc) (a : BitVec 64) : V1State.InnerState → SepProp
  | .keysUnsampled s =>
      (a ↦₆₄ 0x8000000000000000#64) ∗
      protoChunkedKeysUnsampledAt A (a + 8#64) s ∗
      memRegion (a + 64#64) 160
  | .keysSampled s =>
      (a ↦₆₄ 0x8000000000000001#64) ∗
      protoChunkedKeysSampledAt A (a + 8#64) s ∗
      memRegion (a + 168#64) 56
  | .headerSent s =>
      (a ↦₆₄ 0x8000000000000002#64) ∗
      protoChunkedHeaderSentAt A (a + 8#64) s ∗
      memRegion (a + 184#64) 40
  | .ct1Received s =>
      (a ↦₆₄ 0x8000000000000003#64) ∗
      protoChunkedCt1ReceivedAt A (a + 8#64) s ∗
      memRegion (a + 168#64) 56
  | .ekSentCt1Received s =>
      (a ↦₆₄ 0x8000000000000004#64) ∗
      protoChunkedEkSentCt1ReceivedAt A (a + 8#64) s ∗
      memRegion (a + 152#64) 72
  | .noHeaderReceived s =>
      (a ↦₆₄ 0x8000000000000005#64) ∗
      protoChunkedNoHeaderReceivedAt A (a + 8#64) s ∗
      memRegion (a + 104#64) 120
  | .headerReceived s =>
      (a ↦₆₄ 0x8000000000000006#64) ∗
      protoChunkedHeaderReceivedAt A (a + 8#64) s ∗
      memRegion (a + 128#64) 96
  | .ct1Sampled s =>
      protoChunkedCt1SampledAt A a s
  | .ekReceivedCt1Sampled s =>
      (a ↦₆₄ 0x8000000000000008#64) ∗
      protoChunkedEkReceivedCt1SampledAt A (a + 8#64) s ∗
      memRegion (a + 192#64) 32
  | .ct1Acknowledged s =>
      (a ↦₆₄ 0x8000000000000009#64) ∗
      protoChunkedCt1AcknowledgedAt A (a + 8#64) s ∗
      memRegion (a + 176#64) 48
  | .ct2Sampled s =>
      (a ↦₆₄ 0x800000000000000a#64) ∗
      protoChunkedCt2SampledAt A (a + 8#64) s ∗
      memRegion (a + 120#64) 104

/-- `Option<spqr::proto::pq_ratchet::v1_state::InnerState>` at `a` (`224` bytes = `0xe0`, align `8`):
    * `none`: `(a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216` (`0xFFFFFFFFFFFFFFFE` niche)
    * `some st`: `protoInnerStateAt A a st` -/
def optProtoInnerStateAt (A : RustAlloc) (a : BitVec 64) : Option V1State.InnerState → SepProp
  | none    => (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216
  | some st => protoInnerStateAt A a st

/-- Niche value `0xFFFFFFFFFFFFFFFD` (`-3`) used for `Option<pq_ratchet_state::Inner>::None`. -/
def none3Cap' : BitVec 64 := 0xfffffffffffffffd#64

/-- `Option<spqr::proto::pq_ratchet::pq_ratchet_state::Inner>` at `a` (`224` bytes = `0xe0`, align `8`):
    * `none`: `(a ↦₆₄ none3Cap') ∗ memRegion (a + 8#64) 216` (`0xFFFFFFFFFFFFFFFD` niche)
    * `some (.v1 v1)`: `optProtoInnerStateAt A a v1.innerState` -/
def optProtoPqRatchetInnerAt (A : RustAlloc) (a : BitVec 64) :
    Option PqRatchetState.Inner → SepProp
  | none           => (a ↦₆₄ none3Cap') ∗ memRegion (a + 8#64) 216
  | some (.v1 v1) => optProtoInnerStateAt A a v1.innerState

/-- Representation predicate for `spqr::proto::pq_ratchet::PqRatchetState` at `a` (`352` bytes = `0x160`). -/
def protoPqRatchetStateAt (A : RustAlloc) (a : BitVec 64) (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBAt A a st.versionNegotiation ∗
    optChainPBAt A (a + 48#64) st.chain ∗
    optProtoPqRatchetInnerAt A (a + 128#64) st.inner

/-! ## Arithmetic and Cap-Exposure Helpers for `0x4c0d4` and `0x4c460` -/

theorem xor_highBit_toNat_of_lt_2pow63 {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap ^^^ 9223372036854775808#64).toNat = cap.toNat + 9223372036854775808 := by
  revert hlt; bv_bits

theorem cap_xor_highBit_ult_11_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap ^^^ 9223372036854775808#64) 11#64 = false := by
  have hge : 11 ≤ (cap ^^^ 9223372036854775808#64).toNat := by
    rw [xor_highBit_toNat_of_lt_2pow63 hlt]; omega
  simp only [BitVec.ult, show (11#64 : BitVec 64).toNat = 11 from rfl, decide_eq_false_iff_not]
  omega

theorem cap_xor_highBit_cc_11_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    ConditionHolds .CC (subsPState64 (cap ^^^ 9223372036854775808#64) 11#64) = false := by
  rw [conditionHolds_cc_subsPState64, cap_xor_highBit_ult_11_false hlt]

/-- Remainder of `protoUnchunkedCt1SentEkReceivedAt A d st` when `d ↦₆₄ cap` is split out. -/
def protoUnchunkedCt1SentEkReceivedRestAt (A : RustAlloc) (d cap ptr : BitVec 64)
    (st : V1State.Unchunked.Ct1SentEkReceived) : SepProp :=
  ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
    ⌜st.es.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       ptr ↦ₛ st.es ∗
       memRegion (ptr + BitVec.ofNat 64 st.es.length) (cap.toNat - st.es.length)) ∗
    vecU8 A (d + 24#64) st.ek ∗
    vecU8 A (d + 48#64) st.ct1 ∗
    optProtoAuthenticatorAt A (d + 72#64) st.auth ∗
    ((d + 120#64) ↦₆₄ st.epoch)

theorem protoUnchunkedCt1SentEkReceivedAt_expose_cap (A : RustAlloc) (d : BitVec 64)
    (st : V1State.Unchunked.Ct1SentEkReceived) :
    protoUnchunkedCt1SentEkReceivedAt A d st ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        (d ↦₆₄ cap) ∗
        protoUnchunkedCt1SentEkReceivedRestAt A d cap ptr st := by
  unfold protoUnchunkedCt1SentEkReceivedAt
  nth_rw 1 [vecU8]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold protoUnchunkedCt1SentEkReceivedRestAt vecU8At vecHeader
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜st.es.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d ↦₆₄ cap) ∗
        (((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗
             ptr ↦ₛ st.es ∗
             memRegion (ptr + BitVec.ofNat 64 st.es.length) (cap.toNat - st.es.length)) ∗
          vecU8 A (d + 24#64) st.ek ∗
          vecU8 A (d + 48#64) st.ct1 ∗
          optProtoAuthenticatorAt A (d + 72#64) st.auth ∗
          ((d + 120#64) ↦₆₄ st.epoch))) by ac_rfl)) ?_
  apply Entails.pure_left; intro hp
  refine Entails.pure_right hp.2.1 ?_
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜st.es.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d ↦₆₄ cap) ∗
        (((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗
             ptr ↦ₛ st.es ∗
             memRegion (ptr + BitVec.ofNat 64 st.es.length) (cap.toNat - st.es.length)) ∗
          vecU8 A (d + 24#64) st.ek ∗
          vecU8 A (d + 48#64) st.ct1 ∗
          optProtoAuthenticatorAt A (d + 72#64) st.auth ∗
          ((d + 120#64) ↦₆₄ st.epoch))) = _ by ac_rfl))
  exact Entails.pure_right hp (Entails.refl _)

theorem protoUnchunkedCt1SentEkReceivedAt_unexpose_cap (A : RustAlloc) (d cap ptr : BitVec 64)
    (st : V1State.Unchunked.Ct1SentEkReceived) :
    (d ↦₆₄ cap) ∗ protoUnchunkedCt1SentEkReceivedRestAt A d cap ptr st ⊢
      protoUnchunkedCt1SentEkReceivedAt A d st := by
  unfold protoUnchunkedCt1SentEkReceivedAt
  nth_rw 1 [vecU8]
  refine Entails.trans ?_
    (sepConj_mono_left (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))))
  unfold protoUnchunkedCt1SentEkReceivedRestAt vecU8At vecHeader
  exact Entails.of_eq (by ac_rfl)

def headerSentToEkSentCt1Received (u : V1State.Unchunked.HeaderSent) :
    V1State.Unchunked.EkSentCt1Received :=
  { dk := u.ek, ct1 := u.dk, auth := u.auth, epoch := u.epoch }

def keysSampledToCt1Received (st : V1State.Chunked.KeysSampled) :
    V1State.Chunked.Ct1Received :=
  { uc := st.uc.map headerSentToEkSentCt1Received, sendingEk := st.sendingHdr }

theorem optProtoUnchunkedHeaderSentAt_eq_ekSentCt1Received (A : RustAlloc) (a : BitVec 64)
    (uc : Option V1State.Unchunked.HeaderSent) :
    optProtoUnchunkedHeaderSentAt A a uc =
      optProtoUnchunkedEkSentCt1ReceivedAt A a (uc.map headerSentToEkSentCt1Received) := by
  cases uc <;> rfl

theorem protoChunkedKeysSampledAt_eq_ct1ReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Chunked.KeysSampled) :
    protoChunkedKeysSampledAt A a st =
      protoChunkedCt1ReceivedAt A a (keysSampledToCt1Received st) := by
  unfold protoChunkedKeysSampledAt protoChunkedCt1ReceivedAt keysSampledToCt1Received
  rw [optProtoUnchunkedHeaderSentAt_eq_ekSentCt1Received]

theorem tag_and_two_regions_entails_224 (a tag : BitVec 64) (sz pad : Nat) (off : BitVec 64)
    (hoff : a + off = (a + 8#64) + BitVec.ofNat 64 sz)
    (hsum : sz + pad = 216) :
    (a ↦₆₄ tag) ∗ memRegion (a + 8#64) sz ∗ memRegion (a + off) pad ⊢
      memRegion a 224 := by
  have h1 : memRegion (a + 8#64) sz ∗ memRegion (a + off) pad ⊢ memRegion (a + 8#64) 216 := by
    rw [hoff, ← hsum, ProofLib.memRegion_split (a + 8#64) sz pad (by omega)]
    exact Entails.refl _
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a tag) h1

theorem stackAt_dropStack96_split_48 (sp : BitVec 64) :
    stackAt sp dropStack96 = memRegion (sp - 4192#64) 48 ∗ stackAt sp dropStack48 :=
  stackAt_split_bottom sp dropStack48 48 (by decide)

/-! ## Specifications for `0x4c0d4` (`Option<InnerState>`) and `0x4c460` (`PqRatchetState`) -/

def optProtoInnerStateSize : Nat := 224
def protoPqRatchetStateSize : Nat := 352

structure DropOptProtoInnerStateGhost where
  a : BitVec 64
  st : Option V1State.InnerState

def dropOptProtoInnerStateSpec (A : RustAlloc) (b : BitVec 64) :
    Spec DropOptProtoInnerStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      optProtoInnerStateAt A x.a x.st ∗
      optProtoInnerStateJumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStack96
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a optProtoInnerStateSize ∗
      optProtoInnerStateJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStack96

structure DropProtoPqRatchetStateGhost where
  a : BitVec 64
  st : PqRatchetState

def dropProtoPqRatchetStateSpec (A : RustAlloc) (b : BitVec 64) :
    Spec DropProtoPqRatchetStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      protoPqRatchetStateAt A x.a x.st ∗
      optProtoInnerStateJumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStack96
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoPqRatchetStateSize ∗
      optProtoInnerStateJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStack96

def dropOptProtoInnerStatePlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec DropOptProtoInnerStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ optProtoInnerStateAt A x.a x.st ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp dropStack96
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a optProtoInnerStateSize ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp dropStack96

def dropProtoPqRatchetStatePlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec DropProtoPqRatchetStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ protoPqRatchetStateAt A x.a x.st ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp dropStack96
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a protoPqRatchetStateSize ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp dropStack96

/-- Per-variant specification of `0x4c0d4` (`Option<InnerState>`) for a fixed `st`.
    Used for modular per-variant `subroutine_ok` proofs; `dropOptProtoInnerStateSpec` is
    definitionally equal to `dropOptProtoInnerStateVariantSpec A b x.st` at `x.a`. -/
def dropOptProtoInnerStateVariantSpec (A : RustAlloc) (b : BitVec 64)
    (st : Option V1State.InnerState) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a ∧ b &&& 0xfff#64 = 0#64⌝ ∗
      optProtoInnerStateAt A a st ∗
      optProtoInnerStateJumpTableAt b ∗
      A.pool ∗ stackAt s.sp dropStack96
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion a optProtoInnerStateSize ∗
      optProtoInnerStateJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp dropStack96

def dropOptProtoInnerStatePlacedVariantSpec [LibsignalPlacement] (A : RustAlloc)
    (st : Option V1State.InnerState) : Spec (BitVec 64) where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a⌝ ∗ optProtoInnerStateAt A a st ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp dropStack96
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a optProtoInnerStateSize ∗
      optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp dropStack96

/-! ## Per-Variant Helpers for `0x4c0d4` (`Option<InnerState>`) -/

theorem optProtoInnerState_none_entails_224 (a : BitVec 64) :
    (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216 ⊢ memRegion a 224 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a none2Cap)

theorem drop_opt_proto_inner_state_none {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b none) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  ls_code_fetches libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt,
    optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19; wp_steps
  refine SepWP.focus_weaken (optProtoInnerState_none_entails_224 a) (by sep_focus) ?_
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  wp_done

local macro "opt_proto_tail48_steps " tag:term:max sz1:term:max sz2:term:max off:term:max arg:term:max : tactic => `(tactic| (
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19; wp_steps
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  rw [stackAt_dropStack96_split_48 s0.sp]; wp_call hcallee ⟨a + 8#64, $arg⟩
  rw [← stackAt_dropStack96_split_48 s0.sp]
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a $tag $sz1 $sz2 $off
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 $sz1)).symm rfl) (by sep_focus) ?_
  wp_done))

local macro "opt_proto_tail96_steps " tag:term:max sz1:term:max sz2:term:max off:term:max arg:term:max : tactic => `(tactic| (
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19; wp_steps
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  wp_call hcallee ⟨a + 8#64, $arg⟩
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a $tag $sz1 $sz2 $off
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 $sz1)).symm rfl) (by sep_focus) ?_
  wp_done))

theorem drop_opt_proto_inner_state_keysSampled {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) (st : V1State.Chunked.KeysSampled) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.keysSampled st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hcallee : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"))
      (dropProtoChunkedCt1ReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>") (by decide))
    (drop_proto_chunked_ct1_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&& 0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]; have hadrp' := hadrp h
  opt_proto_tail48_steps 0x8000000000000001#64 160 56 168#64 (keysSampledToCt1Received st)

theorem drop_opt_proto_inner_state_headerSent {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) (st : V1State.Chunked.HeaderSent) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.headerSent st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hcallee : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"))
      (dropProtoChunkedHeaderSentSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>") (by decide))
    (drop_proto_chunked_header_sent_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&& 0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_tail96_steps 0x8000000000000002#64 176 40 184#64 st

theorem drop_opt_proto_inner_state_ct1Received {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) (st : V1State.Chunked.Ct1Received) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.ct1Received st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hcallee : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>"))
      (dropProtoChunkedCt1ReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Received>") (by decide))
    (drop_proto_chunked_ct1_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&& 0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_tail48_steps 0x8000000000000003#64 160 56 168#64 st

theorem drop_opt_proto_inner_state_ekSentCt1Received {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) (st : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.ekSentCt1Received st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hcallee : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"))
      (dropProtoChunkedEkSentCt1ReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>") (by decide))
    (drop_proto_chunked_ek_sent_ct1_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&& 0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_tail48_steps 0x8000000000000004#64 144 72 152#64 st

theorem drop_opt_proto_inner_state_noHeaderReceived {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) (st : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.noHeaderReceived st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hcallee : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>"))
      (dropProtoChunkedNoHeaderReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived>") (by decide))
    (drop_proto_chunked_no_header_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&& 0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_tail48_steps 0x8000000000000005#64 96 120 104#64 st

theorem drop_opt_proto_inner_state_headerReceived {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) (st : V1State.Chunked.HeaderReceived) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.headerReceived st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hcallee : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"))
      (dropProtoChunkedHeaderReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>") (by decide))
    (drop_proto_chunked_header_received_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&& 0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_tail48_steps 0x8000000000000006#64 120 96 128#64 st

section PlacedSimpleVariants
variable [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}

theorem drop_opt_proto_inner_state_none_placed :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A none) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19; wp_steps
  refine SepWP.focus_weaken (optProtoInnerState_none_entails_224 a) (by sep_focus) ?_
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  wp_done

theorem drop_opt_proto_inner_state_keysSampled_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec A))
    (st : V1State.Chunked.KeysSampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.keysSampled st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init a s0; rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]
  opt_proto_tail48_steps 0x8000000000000001#64 160 56 168#64 (keysSampledToCt1Received st)

theorem drop_opt_proto_inner_state_headerSent_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 281) (dropProtoChunkedHeaderSentSpec A))
    (st : V1State.Chunked.HeaderSent) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.headerSent st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init a s0; opt_proto_tail96_steps 0x8000000000000002#64 176 40 184#64 st

theorem drop_opt_proto_inner_state_ct1Received_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec A))
    (st : V1State.Chunked.Ct1Received) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct1Received st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init a s0; opt_proto_tail48_steps 0x8000000000000003#64 160 56 168#64 st

theorem drop_opt_proto_inner_state_ekSentCt1Received_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 285) (dropProtoChunkedEkSentCt1ReceivedSpec A))
    (st : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.ekSentCt1Received st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init a s0; opt_proto_tail48_steps 0x8000000000000004#64 144 72 152#64 st

theorem drop_opt_proto_inner_state_noHeaderReceived_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 284) (dropProtoChunkedNoHeaderReceivedSpec A))
    (st : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.noHeaderReceived st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init a s0; opt_proto_tail48_steps 0x8000000000000005#64 96 120 104#64 st

theorem drop_opt_proto_inner_state_headerReceived_placed
    (hcallee : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 283) (dropProtoChunkedHeaderReceivedSpec A))
    (st : V1State.Chunked.HeaderReceived) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.headerReceived st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hcallee ⊢
  wp_init a s0; opt_proto_tail48_steps 0x8000000000000006#64 120 96 128#64 st

end PlacedSimpleVariants

theorem stackAt_sub48_split_32 (sp : BitVec 64) :
    memRegion (sp - 4192#64) 48 ∗ stackAt (sp - 48#64) allocHookStack =
      memRegion (sp - 4192#64) 16 ∗ stackAt (sp - 48#64) dropStack32 := by
  rw [← stackAt_dropStack48_sub48_split_bottom sp,
      stackAt_split_bottom (sp - 48#64) dropStack32 16 (by decide)]
  have hsub : (sp - 48#64) - 4144#64 = sp - 4192#64 := by bv_omega
  rw [hsub]

def optProtoInnerStateJumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_bytes% "220036000561663b870a")) ↦₈ᵣ 34#8) ∗ ((b + bv% ((ls_bytes% "220036000561663b870a") + 1)) ↦₈ᵣ 0#8) ∗
  ((b + bv% ((ls_bytes% "220036000561663b870a") + 2)) ↦₈ᵣ 54#8) ∗ ((b + bv% ((ls_bytes% "220036000561663b870a") + 3)) ↦₈ᵣ 0#8) ∗
  ((b + bv% ((ls_bytes% "220036000561663b870a") + 4)) ↦₈ᵣ 5#8) ∗ ((b + bv% ((ls_bytes% "220036000561663b870a") + 5)) ↦₈ᵣ 97#8) ∗
  ((b + bv% ((ls_bytes% "220036000561663b870a") + 6)) ↦₈ᵣ 102#8) ∗ ((b + bv% ((ls_bytes% "220036000561663b870a") + 7)) ↦₈ᵣ 59#8) ∗
  ((b + bv% ((ls_bytes% "220036000561663b870a") + 8)) ↦₈ᵣ 135#8) ∗ ((b + bv% ((ls_bytes% "220036000561663b870a") + 9)) ↦₈ᵣ 10#8)

def optProtoInnerStateJumpTablePlacedExpanded [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ optProtoInnerStateJumpTableSym) ↦₈ᵣ 34#8) ∗ ((lsmpl.ρ optProtoInnerStateJumpTableSym + 1#64) ↦₈ᵣ 0#8) ∗
  ((lsmpl.ρ optProtoInnerStateJumpTableSym + 2#64) ↦₈ᵣ 54#8) ∗ ((lsmpl.ρ optProtoInnerStateJumpTableSym + 3#64) ↦₈ᵣ 0#8) ∗
  ((lsmpl.ρ optProtoInnerStateJumpTableSym + 4#64) ↦₈ᵣ 5#8) ∗ ((lsmpl.ρ optProtoInnerStateJumpTableSym + 5#64) ↦₈ᵣ 97#8) ∗
  ((lsmpl.ρ optProtoInnerStateJumpTableSym + 6#64) ↦₈ᵣ 102#8) ∗ ((lsmpl.ρ optProtoInnerStateJumpTableSym + 7#64) ↦₈ᵣ 59#8) ∗
  ((lsmpl.ρ optProtoInnerStateJumpTableSym + 8#64) ↦₈ᵣ 135#8) ∗ ((lsmpl.ρ optProtoInnerStateJumpTableSym + 9#64) ↦₈ᵣ 10#8)

local macro "opt_proto_ekReceivedCt1Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 664#64)
    (P_mid := ((a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 128 ∗
      optProtoPolynomialEncoderAt A (a + 136#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
      memRegion (a + 192#64) 32) ∗ $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentEkReceivedAt_none, h16]; wp_steps
      have hnone128 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 120 ⊢ memRegion (a + 8#64) 128 := by
        rw [← h16]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (a + 8#64)
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (a + 8#64) u) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt; wp_steps
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (a + 8#64) cap ptr u) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      wp_call hct1_sent ⟨a + 8#64, u⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_; wp_steps
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    dsimp only [optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
    have hjoin184 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 56 ⊢ memRegion (a + 8#64) 184 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 184 ∗ memRegion (a + 192#64) 32 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000008#64 184 32 192#64 (BitVec.add_assoc a 8#64 184#64).symm rfl
    cases hct1 : st.sendingCt1 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]; wp_steps
      have hnone56 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 48 ⊢ memRegion (a + 136#64) 56 := by
        rw [← h144]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 136#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 136#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt; wp_steps
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 136#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      wp_call hpoly_enc ⟨a + 136#64, pbToProtoPolyEncoder enc⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      wp_done))

theorem drop_opt_proto_inner_state_ekReceivedCt1Sampled {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.ekReceivedCt1Sampled st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hct1_sent : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"))
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>") (by decide))
    (drop_proto_unchunked_ct1_sent_ek_received_ok_ext hdealloc)
  have hpoly_enc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"))
      (dropProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>") (by decide))
    (drop_glue_proto_poly_encoder_ok_ext hdealloc)
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    optProtoInnerStateJumpTableAt, optProtoInnerStateJumpTableBytes,
    optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hct1_sent hpoly_enc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_ekReceivedCt1Sampled_steps entry (optProtoInnerStateJumpTableExpanded b)

theorem drop_opt_proto_inner_state_ekReceivedCt1Sampled_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hct1_sent : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hpoly_enc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (st : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.ekReceivedCt1Sampled st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hct1_sent hpoly_enc ⊢
  wp_init a s0
  opt_proto_ekReceivedCt1Sampled_steps (blkPl_267).base optProtoInnerStateJumpTablePlacedExpanded

def auth8HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ ga.v1.cap) ∗ ((a + 16#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
  ((a + 32#64) ↦₆₄ ga.v2.cap) ∗ ((a + 40#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 48#64) 8

theorem twoVecHeadersAt_8_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 8#64) ga = auth8HeadersAt a ga := by
  unfold twoVecHeadersAt auth8HeadersAt
  rw [BitVec.add_assoc a 8#64 8#64, BitVec.add_assoc a 8#64 16#64,
      BitVec.add_assoc a 8#64 24#64, BitVec.add_assoc a 8#64 32#64,
      BitVec.add_assoc a 8#64 40#64]; rfl

theorem auth8HeadersAt_entails_memRegion_56 (a : BitVec 64) (ga : TwoVecGhost) (epoch : BitVec 64) :
    ((a + 8#64) ↦₆₄ ga.v1.cap) ∗ ((a + 16#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ ga.v2.cap) ∗ ((a + 40#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
      ((a + 56#64) ↦₆₄ epoch) ⊢ memRegion (a + 8#64) 56 := by
  have h56 : (a + 8#64) + 48#64 = a + 56#64 := BitVec.add_assoc a 8#64 48#64
  rw [← h56]
  refine Entails.trans (Entails.of_eq (show _ = auth8HeadersAt a ga ∗ (((a + 8#64) + 48#64) ↦₆₄ epoch) by
    unfold auth8HeadersAt; ac_rfl)) ?_
  rw [← twoVecHeadersAt_8_eq, ProofLib.memRegion_split' (b := a + 8#64) (n := 48) (k := 8)
    (b' := (a + 8#64) + 48#64) rfl rfl (by decide)]
  exact sepConj_mono (twoVecHeadersAt_entails_memRegion_48 (a + 8#64) ga) (pointsTo64_entails_memRegion _ _)

theorem optProtoAuthenticatorAt_8_none_entails_memRegion_56 (A : RustAlloc) (a : BitVec 64) (epoch : BitVec 64) :
    ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 40 ∗ ((a + 56#64) ↦₆₄ epoch) ⊢
      memRegion (a + 8#64) 56 := by
  have h56 : (a + 8#64) + 48#64 = a + 56#64 := BitVec.add_assoc a 8#64 48#64
  have hnone8 : optProtoAuthenticatorAt A (a + 8#64) none =
      ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 40 := by
    rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 8#64 8#64]; rfl
  rw [← h56, ← sepConj_assoc, ← hnone8, ProofLib.memRegion_split' (b := a + 8#64) (n := 48) (k := 8)
    (b' := (a + 8#64) + 48#64) rfl rfl (by decide)]
  exact sepConj_mono (optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 8#64)) (pointsTo64_entails_memRegion _ _)

def auth64HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 64#64) ↦₆₄ ga.v1.cap) ∗ ((a + 72#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 80#64) 8 ∗
  ((a + 88#64) ↦₆₄ ga.v2.cap) ∗ ((a + 96#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 104#64) 8

theorem twoVecHeadersAt_64_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 64#64) ga = auth64HeadersAt a ga := by
  unfold twoVecHeadersAt auth64HeadersAt
  rw [BitVec.add_assoc a 64#64 8#64, BitVec.add_assoc a 64#64 16#64,
      BitVec.add_assoc a 64#64 24#64, BitVec.add_assoc a 64#64 32#64,
      BitVec.add_assoc a 64#64 40#64]; rfl

theorem auth64HeadersAt_entails_memRegion_56 (a : BitVec 64) (ga : TwoVecGhost) (epoch : BitVec 64) :
    ((a + 64#64) ↦₆₄ ga.v1.cap) ∗ ((a + 72#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 80#64) 8 ∗
      ((a + 88#64) ↦₆₄ ga.v2.cap) ∗ ((a + 96#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 104#64) 8 ∗
      ((a + 112#64) ↦₆₄ epoch) ⊢ memRegion (a + 64#64) 56 := by
  have h112 : (a + 64#64) + 48#64 = a + 112#64 := BitVec.add_assoc a 64#64 48#64
  rw [← h112]
  refine Entails.trans (Entails.of_eq (show _ = auth64HeadersAt a ga ∗ (((a + 64#64) + 48#64) ↦₆₄ epoch) by
    unfold auth64HeadersAt; ac_rfl)) ?_
  rw [← twoVecHeadersAt_64_eq, ProofLib.memRegion_split' (b := a + 64#64) (n := 48) (k := 8)
    (b' := (a + 64#64) + 48#64) rfl rfl (by decide)]
  exact sepConj_mono (twoVecHeadersAt_entails_memRegion_48 (a + 64#64) ga) (pointsTo64_entails_memRegion _ _)

theorem optProtoAuthenticatorAt_64_none_entails_memRegion_56 (A : RustAlloc) (a : BitVec 64) (epoch : BitVec 64) :
    ((a + 64#64) ↦₆₄ noneCap) ∗ memRegion (a + 72#64) 40 ∗ ((a + 112#64) ↦₆₄ epoch) ⊢
      memRegion (a + 64#64) 56 := by
  have h112 : (a + 64#64) + 48#64 = a + 112#64 := BitVec.add_assoc a 64#64 48#64
  have hnone64 : optProtoAuthenticatorAt A (a + 64#64) none =
      ((a + 64#64) ↦₆₄ noneCap) ∗ memRegion (a + 72#64) 40 := by
    rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 64#64 8#64]; rfl
  rw [← h112, ← sepConj_assoc, ← hnone64, ProofLib.memRegion_split' (b := a + 64#64) (n := 48) (k := 8)
    (b' := (a + 64#64) + 48#64) rfl rfl (by decide)]
  exact sepConj_mono (optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 64#64)) (pointsTo64_entails_memRegion _ _)

local macro "opt_proto_keysUnsampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have hjoin224 : (a ↦₆₄ 0x8000000000000000#64) ∗ memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 160 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000000#64 56 160 64#64 (BitVec.add_assoc a 8#64 56#64).symm rfl
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  cases huc : st.uc with
  | none =>
    have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
    dsimp only [optProtoUnchunkedKeysUnsampledAt]; rw [h16]; wp_steps
    have hnone56 : ((a + 8#64) ↦₆₄ none2Cap) ∗ memRegion (a + 16#64) 48 ⊢ memRegion (a + 8#64) 56 := by
      rw [← h16]; exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (a + 8#64)
    refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
    wp_done
  | some u =>
    have h56 : (a + 8#64) + 48#64 = a + 56#64 := BitVec.add_assoc a 8#64 48#64
    dsimp only [optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]; rw [h56]
    cases hauth : u.auth with
    | none =>
      have hnone8 : optProtoAuthenticatorAt A (a + 8#64) none = ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 40 := by
        rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 8#64 8#64]; rfl
      rw [hnone8]; wp_steps
      refine SepWP.focus_weaken (optProtoAuthenticatorAt_8_none_entails_memRegion_56 A a u.epoch) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 8#64) auth) (by sep_focus) ?_
      wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_8_eq]; wp_focus_pure; intro hga_lt
      have hne_none2 := cap_add_two_beq_zero_false hga_lt
      have hne_none1 := cap_add_one_beq_zero_false hga_lt
      refine seq_clean (mid := $entry + 276#64)
        (P_mid := ((a ↦₆₄ 0x8000000000000000#64) ∗
          ((auth8HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ ((a + 56#64) ↦₆₄ u.epoch)) ∗
          memRegion (a + 64#64) 160) ∗ $jtExp ∗
          A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
      · dsimp only [auth8HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
            optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; wp_steps
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
            optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
        dsimp only [auth8HeadersAt, vecCapPtrDealloc, optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken (auth8HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · wp_steps
          refine SepWP.focus_weaken (auth8HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1)
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_; wp_done))

theorem drop_opt_proto_inner_state_keysUnsampled {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : V1State.Chunked.KeysUnsampled) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.keysUnsampled st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  ls_code_fetches libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedKeysUnsampledAt, optProtoInnerStateJumpTableAt,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_keysUnsampled_steps entry (optProtoInnerStateJumpTableExpanded b)

theorem drop_opt_proto_inner_state_keysUnsampled_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (st : V1State.Chunked.KeysUnsampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.keysUnsampled st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init a s0
  opt_proto_keysUnsampled_steps (blkPl_267).base optProtoInnerStateJumpTablePlacedExpanded

local macro "opt_proto_ct2Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 600#64)
    (P_mid := ((a ↦₆₄ 0x800000000000000a#64) ∗
      optProtoPolynomialEncoderAt A (a + 8#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
      memRegion (a + 64#64) 56 ∗ memRegion (a + 120#64) 104) ∗ $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h72 : (a + 64#64) + 8#64 = a + 72#64 := BitVec.add_assoc a 64#64 8#64
      dsimp only [optProtoUnchunkedCt2SentAt]; rw [h72]; wp_steps
      have hnone56 : ((a + 64#64) ↦₆₄ none2Cap) ∗ memRegion (a + 72#64) 48 ⊢ memRegion (a + 64#64) 56 := by
        rw [← h72]; exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (a + 64#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      have h112 : (a + 64#64) + 48#64 = a + 112#64 := BitVec.add_assoc a 64#64 48#64
      dsimp only [optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt]; rw [h112]
      cases hauth : u.auth with
      | none =>
        have hnone64 : optProtoAuthenticatorAt A (a + 64#64) none = ((a + 64#64) ↦₆₄ noneCap) ∗ memRegion (a + 72#64) 40 := by
          rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 64#64 8#64]; rfl
        rw [hnone64]; wp_steps
        refine SepWP.focus_weaken (optProtoAuthenticatorAt_64_none_entails_memRegion_56 A a u.epoch) (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
          optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 64#64) auth) (by sep_focus) ?_
        wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_64_eq]; wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        refine seq_clean (mid := $entry + 568#64)
          (P_mid := ((a ↦₆₄ 0x800000000000000a#64) ∗
            optProtoPolynomialEncoderAt A (a + 8#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
            ((auth64HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ ((a + 112#64) ↦₆₄ u.epoch)) ∗
            memRegion (a + 120#64) 104) ∗ $jtExp ∗
            A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
        · dsimp only [auth64HeadersAt, vecCapPtrDealloc]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; wp_steps
            refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
        · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx0_a1⟩
          dsimp only [auth64HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    dsimp only [optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
    have hjoin112 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 56 ⊢ memRegion (a + 8#64) 112 := by
      rw [← h64, ProofLib.memRegion_split (a + 8#64) 56 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 8#64) 112 ∗ memRegion (a + 120#64) 104 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x800000000000000a#64 112 104 120#64 (BitVec.add_assoc a 8#64 112#64).symm rfl
    cases hct2 : st.sendingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [h16]; wp_steps
      have hnone56 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 48 ⊢ memRegion (a + 8#64) 56 := by
        rw [← h16]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 8#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 8#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt; wp_steps
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 8#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      wp_call hpoly_enc ⟨a + 8#64, pbToProtoPolyEncoder enc⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      wp_done))

theorem drop_opt_proto_inner_state_ct2Sampled {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : V1State.Chunked.Ct2Sampled) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.ct2Sampled st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hpoly_enc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"))
      (dropProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>") (by decide))
    (drop_glue_proto_poly_encoder_ok_ext hdealloc)
  ls_code_fetches libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt2SampledAt, optProtoInnerStateJumpTableAt,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly_enc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0
  opt_proto_ct2Sampled_steps entry (optProtoInnerStateJumpTableExpanded b)

theorem drop_opt_proto_inner_state_ct2Sampled_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly_enc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (st : V1State.Chunked.Ct2Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct2Sampled st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt2SampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpoly_enc ⊢
  wp_init a s0
  opt_proto_ct2Sampled_steps (blkPl_267).base optProtoInnerStateJumpTablePlacedExpanded

end CryptoVerification.SpqrV1.Drop

