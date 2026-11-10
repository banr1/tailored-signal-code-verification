/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq

/-!
# Pure and separation-logic helper lemmas for `SignalMessage::new` (`0x1d918`)
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost

/-! ## Callee and panic-stub address helpers -/

theorem fnAddr_new_add_eq_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff signalMessageNewName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + off =
      (tripleRatchetProgAtExt b ext).fnAddr target := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem fnAddr_new_add_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff signalMessageNewName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + off =
      (tripleRatchetProgAt b C ctl abs).fnAddr target :=
  fnAddr_new_add_eq_ext h

theorem signalMessageNew_panic_at_handle_alloc_error2_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol])

theorem signalMessageNew_panic_at_handle_alloc_error2 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  signalMessageNew_panic_at_handle_alloc_error2_ext hk

theorem serializeAddresses_ok_at_new_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : SerializeAddressesOkExt b A uuidTryParse ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      (serializeAddressesSpec A uuidTryParse) := by
  rw [fnAddr_new_add_eq_ext (target := serializeAddressesName)]
  exact h

theorem serializeAddresses_ok_at_new {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : SerializeAddressesOk b C A ctl uuidTryParse abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      (serializeAddressesSpec A uuidTryParse) :=
  serializeAddresses_ok_at_new_ext h

theorem publicKeySerialize_ok_at_new_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : PublicKeySerializeOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (publicKeySerializeSpec A) := by
  rw [fnAddr_new_add_eq_ext (target := publicKeySerializeName)]
  exact h

theorem publicKeySerialize_ok_at_new {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : PublicKeySerializeOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (publicKeySerializeSpec A) :=
  publicKeySerialize_ok_at_new_ext h

theorem encodedLen_ok_at_new_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : EncodedLenOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (encodedLenSpec A) := by
  rw [fnAddr_new_add_eq_ext (target := encodedLenName)]
  exact h

theorem encodedLen_ok_at_new {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : EncodedLenOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (encodedLenSpec A) :=
  encodedLen_ok_at_new_ext h

theorem encodeVarint_ok_at_new_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : EncodeVarintOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      (encodeVarintSpec A) := by
  rw [fnAddr_new_add_eq_ext (target := encodeVarintName)]
  exact h

theorem encodeVarint_ok_at_new {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : EncodeVarintOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      (encodeVarintSpec A) :=
  encodeVarint_ok_at_new_ext h

theorem computeMac_ok_at_new_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : ComputeMacRawOkExt b C A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      (computeMacSpec C.F A) := by
  rw [fnAddr_new_add_eq_ext (target := computeMacName)]
  exact h

theorem computeMac_ok_at_new {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : ComputeMacRawOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      (computeMacSpec C.F A) :=
  computeMac_ok_at_new_ext h

theorem signalMessageNew_computeMac_inImage_ok_at_new_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : ComputeMacOkExt img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      ((computeMacSpec C.F A).inImage img) := by
  rw [fnAddr_new_add_eq_ext (target := computeMacName)]
  exact h

theorem signalMessageNew_computeMac_inImage_ok_at_new {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : ComputeMacOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      ((computeMacSpec C.F A).inImage img) :=
  signalMessageNew_computeMac_inImage_ok_at_new_ext h

theorem serializeAddresses_ok_at_new_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : SerializeAddressesOkX img A uuidTryParse ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      ((serializeAddressesSpecX A uuidTryParse).inImage img) := by
  rw [fnAddr_new_add_eq_ext (target := serializeAddressesName)]
  exact h

theorem publicKeySerialize_ok_at_new_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : PublicKeySerializeOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      ((publicKeySerializeSpecX A).inImage img) := by
  rw [fnAddr_new_add_eq_ext (target := publicKeySerializeName)]
  exact h

theorem encodeVarint_ok_at_new_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : EncodeVarintOkExtX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      ((encodeVarintSpecX A).inImage img) := by
  rw [fnAddr_new_add_eq_ext (target := encodeVarintName)]
  exact h

theorem signalMessageNew_computeMac_inImage_ok_at_new_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : ComputeMacOkX img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      ((computeMacSpecX C.F A).inImage img) := by
  rw [fnAddr_new_add_eq_ext (target := computeMacName)]
  exact h

/-! ## Pure field-length and protobuf-encoding lemmas -/

theorem publicKey_serialize_length (pk : PublicKey) :
    pk.serialize.length = 33 := by
  simp [PublicKey.serialize, List.Vector.toList_length]

theorem publicKey_serialize_ne_nil (pk : PublicKey) :
    pk.serialize ≠ [] := by
  simp [PublicKey.serialize]

theorem addrBytes_length (sid : Bool × List.Vector (BitVec 8) 16) (dev : BitVec 8) :
    (addrBytes sid dev).length = 18 := by
  simp [addrBytes, List.Vector.toList_length]

theorem serializeAddresses_length {parse : ServiceIdParser} {s r : AddrGhost} {bs : List (BitVec 8)}
    (h : serializeAddresses parse s r = some bs) :
    bs.length = 36 := by
  simp only [serializeAddresses, bind, Option.bind] at h
  cases hs : parse s.name.bytes with
  | none => simp [hs] at h
  | some sv =>
    simp only [hs] at h
    cases hr : parse r.name.bytes with
    | none => simp [hr] at h
    | some rv =>
      simp only [hr, pure] at h
      injection h with h
      subst h
      simp [List.length_append, addrBytes_length]

theorem addresses_length {x : SignalMessageNewGhost} {ad : List (BitVec 8)}
    (h : x.addresses uuidTryParse = some ad) :
    ad.length = 36 := by
  simp only [SignalMessageNewGhost.addresses] at h
  cases hx : x.loc with
  | none => simp [hx] at h
  | some l =>
    simp only [hx, Option.bind_some] at h
    exact serializeAddresses_length h

theorem addresses_ne_nil {x : SignalMessageNewGhost} {ad : List (BitVec 8)}
    (h : x.addresses uuidTryParse = some ad) :
    ad ≠ [] := by
  intro hnil
  have hlen := addresses_length h
  simp [hnil] at hlen

theorem encodeVarintAux_length_pos (k : Nat) (v : BitVec 64) :
    1 ≤ (encodeVarintAux (k + 1) v).length := by
  simp only [encodeVarintAux]
  split
  · simp
  · simp

theorem signalMessageNew_encodeVarintAux_length_le (k : Nat) (v : BitVec 64) :
    (encodeVarintAux k v).length ≤ k := by
  induction k generalizing v with
  | zero => simp [encodeVarintAux]
  | succ k ih =>
    simp only [encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v >>> 7)
      omega

theorem signalMessageNew_encodeVarint_length_bounds (v : BitVec 64) :
    1 ≤ (encodeVarint v).length ∧ (encodeVarint v).length ≤ 10 :=
  ⟨encodeVarintAux_length_pos 9 v, signalMessageNew_encodeVarintAux_length_le 10 v⟩

theorem encodeKey_1_ld : encodeKey 1 .lengthDelimited = [0x0a#8] := by decide
theorem encodeKey_2_varint : encodeKey 2 .varint = [0x10#8] := by decide
theorem encodeKey_3_varint : encodeKey 3 .varint = [0x18#8] := by decide
theorem encodeKey_4_ld : encodeKey 4 .lengthDelimited = [0x22#8] := by decide
theorem encodeKey_5_ld : encodeKey 5 .lengthDelimited = [0x2a#8] := by decide
theorem encodeKey_6_ld : encodeKey 6 .lengthDelimited = [0x32#8] := by decide
theorem encodeVarint_33 : encodeVarint 33#64 = [0x21#8] := by decide
theorem encodeVarint_36 : encodeVarint 36#64 = [0x24#8] := by decide

theorem encodeBytesField_1_protoMsg (x : SignalMessageNewGhost) :
    encodeBytesField 1 (x.protoMsg uuidTryParse).ratchetKey =
      [0x0a#8, 0x21#8] ++ x.senderRatchetKey.serialize := by
  simp [SignalMessageNewGhost.protoMsg, encodeBytesField, publicKey_serialize_length,
    encodeKey_1_ld, encodeVarint_33]

theorem encodeUint32Field_2_protoMsg (x : SignalMessageNewGhost) :
    encodeUint32Field 2 (x.protoMsg uuidTryParse).counter =
      [0x10#8] ++ encodeVarint (x.counter.zeroExtend 64) := by
  simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_2_varint]

theorem encodeUint32Field_3_protoMsg (x : SignalMessageNewGhost) :
    encodeUint32Field 3 (x.protoMsg uuidTryParse).previousCounter =
      [0x18#8] ++ encodeVarint (x.previousCounter.zeroExtend 64) := by
  simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_3_varint]

theorem encodeBytesField_4_protoMsg (x : SignalMessageNewGhost) :
    encodeBytesField 4 (x.protoMsg uuidTryParse).ciphertext =
      [0x22#8] ++ encodeVarint (BitVec.ofNat 64 x.ciphertext.length) ++ x.ciphertext := by
  simp [SignalMessageNewGhost.protoMsg, encodeBytesField, encodeKey_4_ld]

theorem encodeBytesField_5_protoMsg_empty (x : SignalMessageNewGhost)
    (h : x.pqRatchet = []) :
    encodeBytesField 5 (x.protoMsg uuidTryParse).pqRatchet = [] := by
  simp [SignalMessageNewGhost.protoMsg, h, encodeBytesField]

theorem encodeBytesField_5_protoMsg_nonempty (x : SignalMessageNewGhost)
    (h : x.pqRatchet ≠ []) :
    encodeBytesField 5 (x.protoMsg uuidTryParse).pqRatchet =
      [0x2a#8] ++ encodeVarint (BitVec.ofNat 64 x.pqRatchet.length) ++ x.pqRatchet := by
  have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr h
  simp [SignalMessageNewGhost.protoMsg, hemp, encodeBytesField, encodeKey_5_ld]

theorem encodeBytesField_6_protoMsg_none (x : SignalMessageNewGhost)
    (h : x.addresses uuidTryParse = none) :
    encodeBytesField 6 (x.protoMsg uuidTryParse).addresses = [] := by
  simp [SignalMessageNewGhost.protoMsg, h, encodeBytesField]

theorem encodeBytesField_6_protoMsg_some (x : SignalMessageNewGhost)
    {ad : List (BitVec 8)} (h : x.addresses uuidTryParse = some ad) :
    encodeBytesField 6 (x.protoMsg uuidTryParse).addresses = [0x32#8, 0x24#8] ++ ad := by
  have hlen := addresses_length h
  simp [SignalMessageNewGhost.protoMsg, h, hlen, encodeBytesField, encodeKey_6_ld, encodeVarint_36]

theorem encode_protoMsg_length_bounds (x : SignalMessageNewGhost)
    (hct : x.ciphertext.length ≤ 2 ^ 32) (hpq : x.pqRatchet.length < 2 ^ 32) :
    35 ≤ (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length ∧
      (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length < 2 ^ 34 := by
  unfold LibsignalProtoCodec.encode
  rw [encodeBytesField_1_protoMsg, encodeUint32Field_2_protoMsg,
    encodeUint32Field_3_protoMsg, encodeBytesField_4_protoMsg]
  have hrk := publicKey_serialize_length x.senderRatchetKey
  have ⟨_, hv2⟩ := signalMessageNew_encodeVarint_length_bounds (x.counter.zeroExtend 64)
  have ⟨_, hv3⟩ := signalMessageNew_encodeVarint_length_bounds (x.previousCounter.zeroExtend 64)
  have ⟨_, hv4⟩ := signalMessageNew_encodeVarint_length_bounds (BitVec.ofNat 64 x.ciphertext.length)
  have hpq_len : (encodeBytesField 5 (x.protoMsg uuidTryParse).pqRatchet).length ≤ 11 + x.pqRatchet.length := by
    by_cases hpq0 : x.pqRatchet = []
    · rw [encodeBytesField_5_protoMsg_empty x hpq0]; simp
    · rw [encodeBytesField_5_protoMsg_nonempty x hpq0]
      have ⟨_, hv5⟩ := signalMessageNew_encodeVarint_length_bounds (BitVec.ofNat 64 x.pqRatchet.length)
      simp only [List.length_append, List.length_singleton]
      omega
  have had_len : (encodeBytesField 6 (x.protoMsg uuidTryParse).addresses).length ≤ 38 := by
    cases had : x.addresses uuidTryParse with
    | none => rw [encodeBytesField_6_protoMsg_none x had]; simp
    | some ad =>
      rw [encodeBytesField_6_protoMsg_some x had]
      have := addresses_length had
      simp [this]
  simp only [List.length_append, List.length_cons, List.length_nil, hrk]
  omega

theorem wireLengthsFit_protoMsg (x : SignalMessageNewGhost)
    (hct : x.ciphertext.length ≤ 2 ^ 32) (hpq : x.pqRatchet.length < 2 ^ 32) :
    WireLengthsFit (x.protoMsg uuidTryParse) := by
  unfold WireLengthsFit
  have ⟨_, hlt⟩ := encode_protoMsg_length_bounds x hct hpq
  omega

theorem signalMessageNew_length_sha256With (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  generalize (chunks64 (sha256Pad m)).foldl F sha256IV = s
  rcases s with ⟨l, hl⟩
  simp [toBEBytes, List.length_flatMap, hl]

theorem signalMessageNew_length_hmacWith (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 :=
  signalMessageNew_length_sha256With F _

theorem signalMessageNew_computeMac_length (F : ShaCompress) (s r : IdentityKey) (k : BitVec 256)
    (msg : List (BitVec 8)) :
    (computeMac F s r k msg).length = 8 := by
  simp [computeMac, hmacSha256Trunc8, signalMessageNew_length_hmacWith]

/-! ## Prefix definitions for inlined `encode_raw` (`+0x1b8..+0x3dc`) -/

/-- Prefix 0 of `serialized` (`+0x1a0`): `[versionByte x.messageVersion]`. -/
def SignalMessageNewGhost.serPrefix0 (x : SignalMessageNewGhost) : List (BitVec 8) :=
  [versionByte x.messageVersion]

/-- Prefix 1 of `serialized` (`+0x210`, after tag 1 `ratchet_key`). -/
def SignalMessageNewGhost.serPrefix1 (parse : UuidParser) (x : SignalMessageNewGhost) :
    List (BitVec 8) :=
  x.serPrefix0 ++ encodeBytesField 1 (x.protoMsg parse).ratchetKey

/-- Prefix 2 of `serialized` (`+0x240`, after tag 2 `counter`). -/
def SignalMessageNewGhost.serPrefix2 (parse : UuidParser) (x : SignalMessageNewGhost) :
    List (BitVec 8) :=
  x.serPrefix1 parse ++ encodeUint32Field 2 (x.protoMsg parse).counter

/-- Prefix 3 of `serialized` (`+0x274`, after tag 3 `previous_counter`). -/
def SignalMessageNewGhost.serPrefix3 (parse : UuidParser) (x : SignalMessageNewGhost) :
    List (BitVec 8) :=
  x.serPrefix2 parse ++ encodeUint32Field 3 (x.protoMsg parse).previousCounter

/-- Prefix 4 of `serialized` (`+0x2dc`, after tag 4 `ciphertext`). -/
def SignalMessageNewGhost.serPrefix4 (parse : UuidParser) (x : SignalMessageNewGhost) :
    List (BitVec 8) :=
  x.serPrefix3 parse ++ encodeBytesField 4 (x.protoMsg parse).ciphertext

/-- Prefix 5 of `serialized` (`+0x360`, after tag 5 `pq_ratchet`). -/
def SignalMessageNewGhost.serPrefix5 (parse : UuidParser) (x : SignalMessageNewGhost) :
    List (BitVec 8) :=
  x.serPrefix4 parse ++ encodeBytesField 5 (x.protoMsg parse).pqRatchet

/-- Prefix 6 of `serialized` (`+0x3dc`, after tag 6 `addresses`) = `serializeContent`. -/
def SignalMessageNewGhost.serPrefix6 (parse : UuidParser) (x : SignalMessageNewGhost) :
    List (BitVec 8) :=
  x.serPrefix5 parse ++ encodeBytesField 6 (x.protoMsg parse).addresses

theorem serPrefix6_eq_serializeContent (x : SignalMessageNewGhost) :
    x.serPrefix6 uuidTryParse =
      serializeContent protoSignalCodec x.messageVersion x.senderRatchetKey x.counter
        x.previousCounter x.ciphertext x.pqRatchet (x.addresses uuidTryParse) := by
  simp only [SignalMessageNewGhost.serPrefix6, SignalMessageNewGhost.serPrefix5,
    SignalMessageNewGhost.serPrefix4, SignalMessageNewGhost.serPrefix3,
    SignalMessageNewGhost.serPrefix2, SignalMessageNewGhost.serPrefix1,
    SignalMessageNewGhost.serPrefix0, serializeContent, protoSignalCodec,
    LibsignalProtoCodec.encode, SignalMessageNewGhost.protoMsg,
    List.cons_append, List.nil_append, List.append_assoc]

theorem serPrefix6_length (x : SignalMessageNewGhost) :
    (x.serPrefix6 uuidTryParse).length = 1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length := by
  rw [serPrefix6_eq_serializeContent]
  simp [serializeContent, protoSignalCodec, SignalMessageNewGhost.protoMsg]
  omega

theorem serPrefix_lengths_le (x : SignalMessageNewGhost) :
    (x.serPrefix0).length = 1 ∧
    (x.serPrefix1 uuidTryParse).length = 36 ∧
    (x.serPrefix1 uuidTryParse).length ≤ (x.serPrefix2 uuidTryParse).length ∧
    (x.serPrefix2 uuidTryParse).length ≤ (x.serPrefix3 uuidTryParse).length ∧
    (x.serPrefix3 uuidTryParse).length ≤ (x.serPrefix4 uuidTryParse).length ∧
    (x.serPrefix4 uuidTryParse).length ≤ (x.serPrefix5 uuidTryParse).length ∧
    (x.serPrefix5 uuidTryParse).length ≤ (x.serPrefix6 uuidTryParse).length := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SignalMessageNewGhost.serPrefix1, SignalMessageNewGhost.serPrefix0,
      encodeBytesField_1_protoMsg, publicKey_serialize_length]
  · simp [SignalMessageNewGhost.serPrefix2]
  · simp [SignalMessageNewGhost.serPrefix3]
  · simp [SignalMessageNewGhost.serPrefix4]
  · simp [SignalMessageNewGhost.serPrefix5]
  · simp [SignalMessageNewGhost.serPrefix6]

theorem model_serialized_eq (F : ShaCompress)
    (x : SignalMessageNewGhost) :
    (x.model F uuidTryParse).serialized =
      x.serPrefix6 uuidTryParse ++ computeMac F x.senderIk x.receiverIk x.macKey (x.serPrefix6 uuidTryParse) := by
  simp [SignalMessageNewGhost.model, SignalMessage.new, serPrefix6_eq_serializeContent]

theorem model_serialized_length (F : ShaCompress)
    (x : SignalMessageNewGhost) :
    (x.model F uuidTryParse).serialized.length =
      1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8 := by
  rw [model_serialized_eq, List.length_append, serPrefix6_length, signalMessageNew_computeMac_length]

/-! ## Separation-logic helpers for `vecU8At` and `sret` (`memRegion x.ret 120`) -/

theorem vecU8At_eq_of_pos (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < cap.toNat) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  have hne : cap ≠ 0#64 := by
    intro h
    subst h
    simp at hpos
  simp [vecU8At, vecHeader, hne, sepConj_assoc]

theorem pointsToBytes_append_singleton (ptr : BitVec 64) (bs : List (BitVec 8)) (b : BitVec 8) :
    ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b)) = (ptr ↦ₛ (bs ++ [b])) := by
  rw [pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem memRegion_split_one (a : BitVec 64) (n : Nat) (h1 : 1 ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegion a n = (∃∗ b : BitVec 8, a ↦₈ b) ∗ memRegion (a + 1#64) (n - 1) := by
  rw [memRegion_split' (n := 1) (k := n - 1) (by omega) rfl hn, memRegion_one]

/-- Split `memRegion r 120` into the cells written by `+0x57c..+0x5a8`:
13 64-bit words at `r + 0x00 .. r + 0x60` (104 B), two 32-bit words at `r + 0x68` and `r + 0x6c`
(8 B), one byte at `r + 0x70` (1 B), and `memRegion (r + 0x71#64) 7` (7 B). -/
theorem memRegion_sret_120 (r : BitVec 64) :
    memRegion r 120 =
      cells r 13 ∗
        (∃∗ w0 : BitVec 32, (r + 0x68#64) ↦₃₂ w0) ∗
        (∃∗ w1 : BitVec 32, (r + 0x6c#64) ↦₃₂ w1) ∗
        (∃∗ b0 : BitVec 8, (r + 0x70#64) ↦₈ b0) ∗
        memRegion (r + 0x71#64) 7 := by
  rw [memRegion_split' (b := r) (b' := r + 0x68#64) (n := 104) (k := 16) (by decide) rfl (by decide),
      show (104 : Nat) = 8 * 13 by rfl, memRegion_cells r 13 (by decide),
      memRegion_split' (b := r + 0x68#64) (b' := r + 0x6c#64) (n := 4) (k := 12) (by decide)
        (by bv_kernel) (by decide),
      memRegion_four (r + 0x68#64),
      memRegion_split' (b := r + 0x6c#64) (b' := r + 0x70#64) (n := 4) (k := 8) (by decide)
        (by bv_kernel) (by decide),
      memRegion_four (r + 0x6c#64),
      memRegion_split' (b := r + 0x70#64) (b' := r + 0x71#64) (n := 1) (k := 7) (by decide)
        (by bv_kernel) (by decide),
      memRegion_one (r + 0x70#64)]

/-! ## `boxU8Buf`, `vecU8At`, and `optVecU8At` equality helpers -/

theorem vecU8At_exact_eq_boxU8Buf (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    vecU8At A a (BitVec.ofNat 64 bs.length) ptr bs =
      ((a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        boxU8Buf A ptr bs) := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hzero_iff : (BitVec.ofNat 64 bs.length = 0) ↔ bs = [] := by
    constructor
    · intro h
      have ht := congrArg BitVec.toNat h
      rw [htoNat] at ht
      exact List.eq_nil_of_length_eq_zero ht
    · rintro rfl; rfl
  by_cases hbs : bs = []
  · subst hbs
    simp [vecU8At, vecHeader, boxU8Buf, sepConj_assoc]
  · have hcap0 : BitVec.ofNat 64 bs.length ≠ 0 := fun h => hbs (hzero_iff.mp h)
    have hpure : (bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0) =
        (ptr ≠ 0#64 ∧ bs.length < 2 ^ 63) :=
      propext ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨Nat.le_refl _, h1, h2⟩⟩
    simp only [vecU8At, vecHeader, boxU8Buf, hcap0, hbs, ↓reduceIte, htoNat,
      Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc, hpure]

theorem memRegion_16_eq_cells2 (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 8) (by decide) rfl (by decide),
      memRegion_eight a, memRegion_eight (a + 8#64)]

theorem optVecU8At_none_eq (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optVecU8At A pin a none =
      (a ↦₆₄ noneCap) ∗ (∃∗ w0 : BitVec 64, (a + 8#64) ↦₆₄ w0) ∗
        (∃∗ w1 : BitVec 64, (a + 16#64) ↦₆₄ w1) := by
  simp only [optVecU8At, memRegion_16_eq_cells2 (a + 8#64)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_kernel
  rw [h16]

theorem optVecU8At_some_exact_eq (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    optVecU8At A ⟨BitVec.ofNat 64 bs.length, ptr⟩ a (some bs) =
      ((a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        boxU8Buf A ptr bs) :=
  vecU8At_exact_eq_boxU8Buf A a ptr bs hlen

theorem signalMessageNew_optSerializeAddressesAt_none_eq (A : RustAlloc) (r : BitVec 64) :
    optSerializeAddressesAt A r none =
      (r ↦₆₄ noneCap) ∗ (∃∗ w0 : BitVec 64, (r + 8#64) ↦₆₄ w0) ∗
        (∃∗ w1 : BitVec 64, (r + 16#64) ↦₆₄ w1) := by
  simp only [optSerializeAddressesAt, memRegion_16_eq_cells2 (r + 8#64)]
  have h16 : r + 8#64 + 8#64 = r + 16#64 := by bv_kernel
  rw [h16]

theorem signalMessageNew_optSerializeAddressesAt_some_eq (A : RustAlloc) (r : BitVec 64)
    {ad : List (BitVec 8)} (hlen : ad.length = 36) :
    optSerializeAddressesAt A r (some ad) =
      ∃∗ ptr : BitVec 64,
        (r ↦₆₄ 36#64) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ 36#64) ∗
          boxU8Buf A ptr ad := by
  simp only [optSerializeAddressesAt]
  congr 1; funext ptr
  have h := vecU8At_exact_eq_boxU8Buf A r ptr ad (by omega)
  rw [hlen] at h
  exact h

/-! ## Relocatable `[LibsignalPlacement]` helpers (Block `63`) -/

abbrev lsRawVecHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

abbrev lsAllocHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

theorem new_externAt?_handle_error [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : H lsRawVecHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked :=
  (mac_ls_externAt?_of_mem (by decide) hi hunmut).trans h

theorem new_externAt?_handle_alloc_error [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : H lsAllocHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ lsAllocHandleErrorSym) = some Rust.panicked :=
  (mac_ls_externAt?_of_mem (by decide) hi hunmut).trans h

theorem new_shim_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSym) noAllocShimSpec :=
  mac_ls_hook_ok_of_mem h_shim (by decide) hi hunmut

theorem new_alloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSym) (rustAllocSpec A) :=
  mac_ls_hook_ok_of_mem h_alloc (by decide) hi hunmut

theorem new_dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
  mac_ls_hook_ok_of_mem h_dealloc (by decide) hi hunmut

set_option maxRecDepth 200000 in
theorem new_memcpy_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsMemcpySym) framelessMemcpySpec :=
  mac_ls_hook_ok_of_mem h_mc (by decide) hi hunmut

end CryptoVerification.LibsignalTripleRatchet
