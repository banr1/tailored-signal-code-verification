/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Shared Base for `prost::encoding::message::encode` on `unchunked::EkSentCt1Received` and `unchunked::Ct1Sent`

Shared instruction decode lemmas (`0x37a10..0x37f7c` and `0x52a9c..0x530a0`), symbol names,
pure encoding model bridge lemmas, and specifications for:
1. `prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#1, #2]`
   (`0x37a10`, 150 insns; `0x52a9c`, 166 insns)
2. `prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#1, #2]`
   (`0x37c68`, 197 insns; `0x52d34`, 219 insns)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree libsignalSessionBin [
  0x37af4 → 0x38060,
  0x4d6a4 → 0x4dca8
]

abbrev ekSentCt1ReceivedEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#1]"

abbrev ekSentCt1ReceivedEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#2]"

abbrev ct1SentEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#1]"

abbrev ct1SentEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]"

@[simp, arm64_norm] theorem ekSentCt1ReceivedEncode1_fnOff :
    libsignalSessionCode.fnOff ekSentCt1ReceivedEncode1Name = 0x37af4 :=
  libsignalSessionCode_fnOff_0x37af4

@[simp, arm64_norm] theorem ekSentCt1ReceivedEncode2_fnOff :
    libsignalSessionCode.fnOff ekSentCt1ReceivedEncode2Name = 0x4d6a4 :=
  libsignalSessionCode_fnOff_0x4d6a4

@[simp, arm64_norm] theorem ct1SentEncode1_fnOff :
    libsignalSessionCode.fnOff ct1SentEncode1Name = 0x37d4c :=
  libsignalSessionCode_fnOff_0x37d4c

@[simp, arm64_norm] theorem ct1SentEncode2_fnOff :
    libsignalSessionCode.fnOff ct1SentEncode2Name = 0x4d93c :=
  libsignalSessionCode_fnOff_0x4d93c

/-- Stack budget for `encode<EkSentCt1Received>` and `encode<Ct1Sent>` parameterized by `resStack`:
`64 + authEncodeStackOf resStack = 128 + (0x30 + resStack)` bytes
(`0x40 = 64` B own frame + `authEncodeStackOf resStack` for `encode<Authenticator>`). -/
abbrev unchunkedMsgEncodeStackOf (resStack : Nat) : Nat := 64 + authEncodeStackOf resStack

/-- Stack budget at `doReserveStack` (`4384` B). -/
abbrev unchunkedMsgEncodeStack : Nat := unchunkedMsgEncodeStackOf doReserveStack

/-- Stack budget at `doReserveStackX` (`16624` B). -/
abbrev unchunkedMsgEncodeStackX : Nat := unchunkedMsgEncodeStackOf doReserveStackX

/-! ## 2. Pure Model Equivalence & Decomposition Lemmas -/

theorem protoEncodeKey_1_varint :
    Proto.encodeKey 1#32 .varint = [0x08#8] := rfl

theorem protoEncodeKey_3_lengthDelimited :
    Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := rfl

theorem protoEncodeKey_4_lengthDelimited :
    Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := rfl

theorem protoEncodeKey_5_lengthDelimited :
    Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] := rfl

theorem protoEncodeKey_6_lengthDelimited :
    Proto.encodeKey 6#32 .lengthDelimited = [0x32#8] := rfl

theorem protoEncodeKey_7_lengthDelimited :
    Proto.encodeKey 7#32 .lengthDelimited = [0x3a#8] := rfl

theorem protoEncodeU64Field_zero (tag : BitVec 32) :
    Proto.encodeUint64Field tag 0#64 = [] := rfl

theorem protoEncodeU64Field_1_of_ne_zero {v : BitVec 64} (hne : v ≠ 0#64) :
    Proto.encodeUint64Field 1#32 v =
      [0x08#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint v := by
  have hbeq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [Proto.encodeUint64Field, hbeq, Bool.false_eq_true, ↓reduceIte,
    protoEncodeKey_1_varint, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_3_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 3#32 bs =
      [0x1a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_3_lengthDelimited, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_4_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 4#32 bs =
      [0x22#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_4_lengthDelimited, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_5_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 5#32 bs =
      [0x2a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_5_lengthDelimited, protoEncodeVarint_eq_codec]

/-- Pure bytes appended by `encode<EkSentCt1Received>` (`tag = 1`, length-delimited):
`Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m`
(definitionally equal to `Proto.encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 (some m)`). -/
abbrev encodeEkSentCt1ReceivedMsg (m : V1State.Unchunked.EkSentCt1Received) : List (BitVec 8) :=
  Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m

/-- Pure bytes appended by `encode<Ct1Sent>` (`tag = 1`, length-delimited):
`Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m`
(definitionally equal to `Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 (some m)`). -/
abbrev encodeCt1SentMsg (m : V1State.Unchunked.Ct1Sent) : List (BitVec 8) :=
  Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m

/-- Outer message header bytes (`tag = 1`, length-delimited: `0x0a#8` + `encodeVarint innerLen`). -/
def msgHeaderBytes (innerLen : Nat) : List (BitVec 8) :=
  [0x0a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 innerLen)

/-- Encoded `epoch: u64` field (`tag = 1`, varint). -/
def u64Field1Bytes (epoch : BitVec 64) : List (BitVec 8) :=
  Proto.encodeUint64Field 1#32 epoch

/-- Encoded `auth: Option<Authenticator>` field (`tag = 2`, length-delimited). -/
def optAuthField2Bytes (auth : Option AuthenticatorPB) : List (BitVec 8) :=
  Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 auth

/-- Encoded `Vec<u8>` field with tag `tag` (length-delimited). -/
def bytesFieldTagged (tag : BitVec 32) (bs : List (BitVec 8)) : List (BitVec 8) :=
  Proto.encodeBytesField tag bs

theorem bs_append_msgHeaderBytes (bs : List (BitVec 8)) (innerLen : Nat) :
    (bs ++ [0x0a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 innerLen) =
      bs ++ msgHeaderBytes innerLen := by
  simp only [msgHeaderBytes, List.append_assoc]

theorem msgHeaderBytes_len_bounds (innerLen : Nat) :
    2 ≤ (msgHeaderBytes innerLen).length ∧ (msgHeaderBytes innerLen).length ≤ 11 := by
  have hb := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 innerLen)
  simp only [msgHeaderBytes, List.length_append, List.length_singleton]
  omega

theorem bs_append_u64Field1Bytes_of_ne_zero {epoch : BitVec 64} (hne : epoch ≠ 0#64)
    (bs : List (BitVec 8)) :
    (bs ++ [0x08#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint epoch =
      bs ++ u64Field1Bytes epoch := by
  rw [u64Field1Bytes, protoEncodeU64Field_1_of_ne_zero hne]
  simp only [List.append_assoc]

theorem bs_append_u64Field1Bytes_of_zero {epoch : BitVec 64} (hz : epoch = 0#64)
    (bs : List (BitVec 8)) :
    bs = bs ++ u64Field1Bytes epoch := by
  subst hz
  simp only [u64Field1Bytes, protoEncodeU64Field_zero, List.append_nil]

theorem u64Field1Bytes_len_of_ne_zero {epoch : BitVec 64} (hne : epoch ≠ 0#64) :
    (u64Field1Bytes epoch).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint epoch).length := by
  rw [u64Field1Bytes, protoEncodeU64Field_1_of_ne_zero hne]
  simp only [List.length_append, List.length_singleton]

theorem bs_append_optAuthField2Bytes_some (bs : List (BitVec 8)) (au : AuthenticatorPB) :
    bs ++ encodeAuthMsg au = bs ++ optAuthField2Bytes (some au) := rfl

theorem bs_append_optAuthField2Bytes_none (bs : List (BitVec 8)) :
    bs = bs ++ optAuthField2Bytes none := by
  simp only [optAuthField2Bytes, Proto.encodeOptMessage, List.append_nil]

theorem bs_append_bytesField3_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false)
    (bs : List (BitVec 8)) :
    ((bs ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)) ++ f =
      bs ++ bytesFieldTagged 3#32 f := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_3_of_ne_nil hne']
  simp only [List.append_assoc]

theorem bs_append_bytesField4_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false)
    (bs : List (BitVec 8)) :
    ((bs ++ [0x22#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)) ++ f =
      bs ++ bytesFieldTagged 4#32 f := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_4_of_ne_nil hne']
  simp only [List.append_assoc]

theorem bs_append_bytesField5_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false)
    (bs : List (BitVec 8)) :
    ((bs ++ [0x2a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)) ++ f =
      bs ++ bytesFieldTagged 5#32 f := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_5_of_ne_nil hne']
  simp only [List.append_assoc]

theorem bs_append_bytesFieldTagged_of_empty (tag : BitVec 32) {f : List (BitVec 8)}
    (hemp : f.isEmpty = true) (bs : List (BitVec 8)) :
    bs = bs ++ bytesFieldTagged tag f := by
  have hnil : f = [] := List.isEmpty_iff.mp hemp
  subst hnil
  simp only [bytesFieldTagged, protoEncodeBytesField_nil, List.append_nil]

theorem bytesField3_len_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false) :
    (bytesFieldTagged 3#32 f).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)).length + f.length := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_3_of_ne_nil hne']
  simp only [List.length_append, List.length_singleton]

theorem bytesField4_len_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false) :
    (bytesFieldTagged 4#32 f).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)).length + f.length := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_4_of_ne_nil hne']
  simp only [List.length_append, List.length_singleton]

theorem bytesField5_len_of_ne_empty {f : List (BitVec 8)} (hne : f.isEmpty = false) :
    (bytesFieldTagged 5#32 f).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 f.length)).length + f.length := by
  have hne' : f ≠ [] := List.isEmpty_eq_false_iff.mp hne
  rw [bytesFieldTagged, protoEncodeBytesField_5_of_ne_nil hne']
  simp only [List.length_append, List.length_singleton]

theorem encodeEkSentCt1ReceivedMsg_eq_parts (m : V1State.Unchunked.EkSentCt1Received) :
    encodeEkSentCt1ReceivedMsg m =
      msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m) ++
        u64Field1Bytes m.epoch ++
        optAuthField2Bytes m.auth ++
        bytesFieldTagged 3#32 m.dk ++
        bytesFieldTagged 4#32 m.ct1 := by
  have hlen : (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length = ekSentCt1ReceivedPBEncodedLen m :=
    ekSentCt1ReceivedPBEncodedLen_eq_proto m
  dsimp only [encodeEkSentCt1ReceivedMsg, Proto.encodeMessage, msgHeaderBytes, u64Field1Bytes,
    optAuthField2Bytes, bytesFieldTagged]
  rw [hlen, protoEncodeKey_1_lengthDelimited, protoEncodeVarint_eq_codec]
  simp only [V1State.Unchunked.EkSentCt1Received.encodeRaw, Proto.encodeUint64Field, List.append_assoc]

theorem bs0_append_encodeEkSentCt1ReceivedMsg (bs0 : List (BitVec 8))
    (m : V1State.Unchunked.EkSentCt1Received) :
    ((((bs0 ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)) ++ u64Field1Bytes m.epoch) ++
      optAuthField2Bytes m.auth) ++ bytesFieldTagged 3#32 m.dk) ++ bytesFieldTagged 4#32 m.ct1 =
      bs0 ++ encodeEkSentCt1ReceivedMsg m := by
  rw [encodeEkSentCt1ReceivedMsg_eq_parts]
  simp only [List.append_assoc]

theorem encodeEkSentCt1ReceivedMsg_len_split (m : V1State.Unchunked.EkSentCt1Received) :
    (encodeEkSentCt1ReceivedMsg m).length =
      (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length +
        (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.dk).length +
        (bytesFieldTagged 4#32 m.ct1).length := by
  rw [encodeEkSentCt1ReceivedMsg_eq_parts]
  simp only [List.length_append, Nat.add_assoc]

theorem ekSentCt1ReceivedPBEncodedLen_eq_fields_len (m : V1State.Unchunked.EkSentCt1Received) :
    ekSentCt1ReceivedPBEncodedLen m =
      (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.dk).length +
        (bytesFieldTagged 4#32 m.ct1).length := by
  have h := ekSentCt1ReceivedPBEncodedLen_eq_proto m
  rw [← h]
  simp only [V1State.Unchunked.EkSentCt1Received.encodedLen,
    V1State.Unchunked.EkSentCt1Received.encodeRaw, Proto.encodeUint64Field,
    u64Field1Bytes, optAuthField2Bytes, bytesFieldTagged, List.length_append, Nat.add_assoc]

theorem encodeCt1SentMsg_eq_parts (m : V1State.Unchunked.Ct1Sent) :
    encodeCt1SentMsg m =
      msgHeaderBytes (ct1SentPBEncodedLen m) ++
        u64Field1Bytes m.epoch ++
        optAuthField2Bytes m.auth ++
        bytesFieldTagged 3#32 m.hdr ++
        bytesFieldTagged 4#32 m.es ++
        bytesFieldTagged 5#32 m.ct1 := by
  have hlen : (V1State.Unchunked.Ct1Sent.encodeRaw m).length = ct1SentPBEncodedLen m :=
    ct1SentPBEncodedLen_eq_proto m
  dsimp only [encodeCt1SentMsg, Proto.encodeMessage, msgHeaderBytes, u64Field1Bytes,
    optAuthField2Bytes, bytesFieldTagged]
  rw [hlen, protoEncodeKey_1_lengthDelimited, protoEncodeVarint_eq_codec]
  simp only [V1State.Unchunked.Ct1Sent.encodeRaw, Proto.encodeUint64Field, List.append_assoc]

theorem bs0_append_encodeCt1SentMsg (bs0 : List (BitVec 8))
    (m : V1State.Unchunked.Ct1Sent) :
    (((((bs0 ++ msgHeaderBytes (ct1SentPBEncodedLen m)) ++ u64Field1Bytes m.epoch) ++
      optAuthField2Bytes m.auth) ++ bytesFieldTagged 3#32 m.hdr) ++ bytesFieldTagged 4#32 m.es) ++
      bytesFieldTagged 5#32 m.ct1 =
      bs0 ++ encodeCt1SentMsg m := by
  rw [encodeCt1SentMsg_eq_parts]
  simp only [List.append_assoc]

theorem encodeCt1SentMsg_len_split (m : V1State.Unchunked.Ct1Sent) :
    (encodeCt1SentMsg m).length =
      (msgHeaderBytes (ct1SentPBEncodedLen m)).length +
        (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.hdr).length +
        (bytesFieldTagged 4#32 m.es).length +
        (bytesFieldTagged 5#32 m.ct1).length := by
  rw [encodeCt1SentMsg_eq_parts]
  simp only [List.length_append, Nat.add_assoc]

theorem ct1SentPBEncodedLen_eq_fields_len (m : V1State.Unchunked.Ct1Sent) :
    ct1SentPBEncodedLen m =
      (u64Field1Bytes m.epoch).length +
        (optAuthField2Bytes m.auth).length +
        (bytesFieldTagged 3#32 m.hdr).length +
        (bytesFieldTagged 4#32 m.es).length +
        (bytesFieldTagged 5#32 m.ct1).length := by
  have h := ct1SentPBEncodedLen_eq_proto m
  rw [← h]
  simp only [V1State.Unchunked.Ct1Sent.encodedLen,
    V1State.Unchunked.Ct1Sent.encodeRaw, Proto.encodeUint64Field,
    u64Field1Bytes, optAuthField2Bytes, bytesFieldTagged, List.length_append, Nat.add_assoc]

/-! ## 3. Specifications of `encode<EkSentCt1Received>` & `encode<Ct1Sent>` (`[local#1, 2]`) -/

/-- Shared panic postcondition for `prost::encoding::message::encode` subroutines. -/
def msgEncodeOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Pinned ghost arguments of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>`:
- `msgA`: pointer to `&spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received` (`x0`, 104 bytes),
- `g`: `(cap, ptr)` pins for `dk`, `ct1`, and `auth`,
- `m`: pure `V1State.Unchunked.EkSentCt1Received` value,
- `v`: pointer to `buf: &mut Vec<u8>` (`x1`, 24 bytes),
- `cap`, `ptr`, `bs`: initial capacity, buffer pointer, and contents of `buf`. -/
structure EkSentCt1ReceivedEncodePinnedGhost where
  msgA : BitVec 64
  g : Unchunked4PBGhost
  m : V1State.Unchunked.EkSentCt1Received
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>`. -/
structure EkSentCt1ReceivedEncodeGhost where
  msgA : BitVec 64
  m : V1State.Unchunked.EkSentCt1Received
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`.
Note on the capacity/length bound: top-level `Message::encode` pre-allocates `cap = encoded_len`,
discharging the left disjunct `x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat`;
growing callers discharge the right disjunct `< 2 ^ 62` from protocol message size bounds. -/
def ekSentCt1ReceivedEncodePinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EkSentCt1ReceivedEncodePinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`. -/
def ekSentCt1ReceivedEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EkSentCt1ReceivedEncodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ekSentCt1ReceivedPBAt A x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBAt A x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

abbrev ekSentCt1ReceivedEncodePinnedSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodePinnedGhost :=
  ekSentCt1ReceivedEncodePinnedSpecOf doReserveStack A

abbrev ekSentCt1ReceivedEncodePinnedSpecX (A : RustAlloc) : Spec EkSentCt1ReceivedEncodePinnedGhost :=
  ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A

abbrev ekSentCt1ReceivedEncodeSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodeGhost :=
  ekSentCt1ReceivedEncodeSpecOf doReserveStack A

abbrev ekSentCt1ReceivedEncodeSpecX (A : RustAlloc) : Spec EkSentCt1ReceivedEncodeGhost :=
  ekSentCt1ReceivedEncodeSpecOf doReserveStackX A

def EkSentCt1ReceivedEncode1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncode1Name)
    (ekSentCt1ReceivedEncodePinnedSpec A)

def EkSentCt1ReceivedEncode1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncode1Name)
    (ekSentCt1ReceivedEncodeSpec A)

def EkSentCt1ReceivedEncode1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ekSentCt1ReceivedEncode1Name)
    ((ekSentCt1ReceivedEncodePinnedSpecX A).inImage img)

def EkSentCt1ReceivedEncode1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ekSentCt1ReceivedEncode1Name)
    ((ekSentCt1ReceivedEncodeSpecX A).inImage img)

def EkSentCt1ReceivedEncode2PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncode2Name)
    (ekSentCt1ReceivedEncodePinnedSpec A)

def EkSentCt1ReceivedEncode2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncode2Name)
    (ekSentCt1ReceivedEncodeSpec A)

def EkSentCt1ReceivedEncode2PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ekSentCt1ReceivedEncode2Name)
    ((ekSentCt1ReceivedEncodePinnedSpecX A).inImage img)

def EkSentCt1ReceivedEncode2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ekSentCt1ReceivedEncode2Name)
    ((ekSentCt1ReceivedEncodeSpecX A).inImage img)

/-- Pinned ghost arguments of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>`:
- `msgA`: pointer to `&spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent` (`x0`, 128 bytes),
- `g`: `(cap, ptr)` pins for `hdr`, `es`, `ct1`, and `auth`,
- `m`: pure `V1State.Unchunked.Ct1Sent` value,
- `v`: pointer to `buf: &mut Vec<u8>` (`x1`, 24 bytes),
- `cap`, `ptr`, `bs`: initial capacity, buffer pointer, and contents of `buf`. -/
structure Ct1SentEncodePinnedGhost where
  msgA : BitVec 64
  g : Unchunked5PBGhost
  m : V1State.Unchunked.Ct1Sent
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>`. -/
structure Ct1SentEncodeGhost where
  msgA : BitVec 64
  m : V1State.Unchunked.Ct1Sent
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`.
Note on the capacity/length bound: top-level `Message::encode` pre-allocates `cap = encoded_len`,
discharging the left disjunct `x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat`;
growing callers discharge the right disjunct `< 2 ^ 62` from protocol message size bounds. -/
def ct1SentEncodePinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec Ct1SentEncodePinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeCt1SentMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<Ct1Sent, Vec<u8>>` (`[local#1, 2]`),
parameterized by `resStack`. -/
def ct1SentEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec Ct1SentEncodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeCt1SentMsg x.m).length + 10 < 2 ^ 62)⌝ ∗
      ct1SentPBAt A x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBAt A x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
      A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)
  onPanic := fun _ s0 sf => msgEncodeOnPanic s0 sf

abbrev ct1SentEncodePinnedSpec (A : RustAlloc) : Spec Ct1SentEncodePinnedGhost :=
  ct1SentEncodePinnedSpecOf doReserveStack A

abbrev ct1SentEncodePinnedSpecX (A : RustAlloc) : Spec Ct1SentEncodePinnedGhost :=
  ct1SentEncodePinnedSpecOf doReserveStackX A

abbrev ct1SentEncodeSpec (A : RustAlloc) : Spec Ct1SentEncodeGhost :=
  ct1SentEncodeSpecOf doReserveStack A

abbrev ct1SentEncodeSpecX (A : RustAlloc) : Spec Ct1SentEncodeGhost :=
  ct1SentEncodeSpecOf doReserveStackX A

def Ct1SentEncode1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode1Name)
    (ct1SentEncodePinnedSpec A)

def Ct1SentEncode1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode1Name)
    (ct1SentEncodeSpec A)

def Ct1SentEncode1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1SentEncode1Name)
    ((ct1SentEncodePinnedSpecX A).inImage img)

def Ct1SentEncode1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1SentEncode1Name)
    ((ct1SentEncodeSpecX A).inImage img)

def Ct1SentEncode2PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name)
    (ct1SentEncodePinnedSpec A)

def Ct1SentEncode2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name)
    (ct1SentEncodeSpec A)

def Ct1SentEncode2PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1SentEncode2Name)
    ((ct1SentEncodePinnedSpecX A).inImage img)

def Ct1SentEncode2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1SentEncode2Name)
    ((ct1SentEncodeSpecX A).inImage img)

/-! ## 4. Stack, Memory, and Callee Helpers -/

theorem stackAt_unchunkedMsgEncode {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (unchunkedMsgEncodeStackOf resStack) =
      stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp (authEncodeStackOf resStack) 8
    (by dsimp [authEncodeStackOf]; omega)
  have heq : authEncodeStackOf resStack + 8 * 8 = unchunkedMsgEncodeStackOf resStack := by
    dsimp [unchunkedMsgEncodeStackOf, authEncodeStackOf]; omega
  rw [heq] at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_authEncode_eq_encodeVarint64 {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (authEncodeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
        stackAt sp1 (0x30 + resStack) := by
  have h := ProofLib.stackAt_split_bottom sp1 (0x30 + resStack) 64 (by omega)
  have heq : 0x30 + resStack + 64 = authEncodeStackOf resStack := by
    dsimp [authEncodeStackOf]; omega
  simpa only [heq] using h

theorem stackAt_authEncode_eq_encodedLen {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (authEncodeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (authEncodeStackOf resStack)) (authEncodeStackOf resStack - 16) ∗
        stackAt sp1 unchunkedEncodedLenStack := by
  have h := ProofLib.stackAt_split_bottom sp1 unchunkedEncodedLenStack
    (authEncodeStackOf resStack - 16) (by dsimp [unchunkedEncodedLenStack, authEncodeStackOf]; omega)
  have heq : unchunkedEncodedLenStack + (authEncodeStackOf resStack - 16) =
      authEncodeStackOf resStack := by
    dsimp [unchunkedEncodedLenStack, authEncodeStackOf]; omega
  simpa only [heq] using h

/-- Callee-saved registers `x24..x28` untouched by `encode<EkSentCt1Received>` and `encode<Ct1Sent>`
(`x19..x23, fp, lr` are saved on stack), together with `StepInv s0 s` for `inImage img` invariant propagation. -/
def UnchunkedEncodeCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem UnchunkedEncodeCalleeSaved.refl (s0 : State) : UnchunkedEncodeCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, StepInv.refl s0⟩

theorem UnchunkedEncodeCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : UnchunkedEncodeCalleeSaved s0 s1) (h12 : UnchunkedEncodeCalleeSaved s1 s2) :
    UnchunkedEncodeCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

theorem UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : UnchunkedEncodeCalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem UnchunkedEncodeCalleeSaved.step {s0 s1 s2 : State}
    (h01 : UnchunkedEncodeCalleeSaved s0 s1)
    (hx24 : s2.readReg64 (Reg.gpr 24#5) = s1.readReg64 (Reg.gpr 24#5))
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    UnchunkedEncodeCalleeSaved s0 s2 :=
  h01.trans ⟨hx24, hx25, hx26, hx27, hx28, hvregs, hinv⟩

/-- Wrap a `Spec α` with `⌜UnchunkedEncodeCalleeSaved s0 s⌝` in the precondition. -/
def withUnchunkedEncodeCS {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜UnchunkedEncodeCalleeSaved s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withUnchunkedEncodeCS {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withUnchunkedEncodeCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withUnchunkedEncodeCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withUnchunkedEncodeCS_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withUnchunkedEncodeCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withUnchunkedEncodeCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2.2.2.2.2 img hinv0, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

/-! ### Call Wrapper Lemmas -/

theorem step_unchunked_memcpy_call (b : BitVec 64)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc sessionMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; simp only [sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_encode_varint_call {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withUnchunkedEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCS, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCS, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCS, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_do_reserve2_call {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withUnchunkedEncodeCS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  have hres64 : resStack + 48 + 64 < 2 ^ 64 := by omega
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
          memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCS, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCS, doReserve2SpecOf, doReserveSpec, msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withUnchunkedEncodeCS, doReserve2SpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_do_reserve7_call {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withUnchunkedEncodeCS s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  have hres64 : resStack + 48 + 64 < 2 ^ 64 := by omega
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
          memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCS, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCS, doReserveSpecOf, doReserveSpec, msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withUnchunkedEncodeCS, doReserveSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_auth_encode_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withUnchunkedEncodeCS s0 (authEncodePinnedSpecOf resStack A)))
    (authA : BitVec 64) (gAuth : AuthenticatorPBGhost) (auth : AuthenticatorPB)
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_fit : curBs.length + (encodeAuthMsg auth).length ≤ curCap.toNat ∨
      curBs.length + (encodeAuthMsg auth).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = authA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (authenticatorPBPinnedAt A gAuth authA auth ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeAuthMsg auth).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((authenticatorPBPinnedAt A gAuth authA auth ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeAuthMsg auth) ∗ A.pool ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := AuthEncodePinnedGhost.mk authA gAuth auth v curCap curPtr curBs)
    (F := F) hauthEnc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withUnchunkedEncodeCS, authEncodePinnedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_fit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCS, authEncodePinnedSpecOf, msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withUnchunkedEncodeCS, authEncodePinnedSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    rw [sepConj_left_comm (authenticatorPBPinnedAt A gAuth authA auth)]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hpure => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hpure.1 hpure.2)
    exact Entails.of_eq (by ac_rfl)

theorem step_ekSentCt1Received_encoded_len_call {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withUnchunkedEncodeCS s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A)))
    (g : Unchunked4PBGhost) (msgA sp ret_pc : BitVec 64) (m : V1State.Unchunked.EkSentCt1Received)
    (hfit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA) (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m) →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := PinnedEncLenGhost.mk msgA g m)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack))
            (authEncodeStackOf resStack - 16) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCS, ekSentCt1ReceivedEncodedLenPinnedSpec,
      unchunked4EncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hfit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withUnchunkedEncodeCS, ekSentCt1ReceivedEncodedLenPinnedSpec,
      unchunked4EncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCS, ekSentCt1ReceivedEncodedLenPinnedSpec, unchunked4EncodedLenPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodedLen hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_ct1Sent_encoded_len_call {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withUnchunkedEncodeCS s0 (ct1SentEncodedLenPinnedSpec A)))
    (g : Unchunked5PBGhost) (msgA sp ret_pc : BitVec 64) (m : V1State.Unchunked.Ct1Sent)
    (hfit : ct1SentPBEncodedLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA) (hcs : UnchunkedEncodeCalleeSaved s0 s)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ct1SentPBEncodedLen m) →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((ct1SentPBPinnedAt A g msgA m ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := PinnedEncLenGhost.mk msgA g m)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack))
            (authEncodeStackOf resStack - 16) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCS, ct1SentEncodedLenPinnedSpec,
      unchunked5EncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hfit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withUnchunkedEncodeCS, ct1SentEncodedLenPinnedSpec,
      unchunked5EncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCS, ct1SentEncodedLenPinnedSpec, unchunked5EncodedLenPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm
        (hcs.trans (UnchunkedEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodedLen hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Prost.MessageEncode

