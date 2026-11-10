/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKey
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoX
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecX
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.X
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.X
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Getters.SameAccount
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import ProofLib.SepLogic.WP.Apply

/-!
# Callee Contract Glue for Triple Ratchet Proofs

Assembles unconditional and hook-scoped `subroutine_ok` corollaries across the triple-ratchet
submodules (`Alloc`, `Prost`, `Bytes`, `Getters`, `ChainKey`, and
`ConsumeMessageKeyTransfer`), discharging callee-hypothesis abbreviations on
`tripleRatchetProgAtExt`, `tripleRatchetProgAt`, and `AllocContractsX`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Glue

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet

/-! ## Callee Discharges Across Submodules -/

theorem encode_varint_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    Prost.EncodeVarintOkExt b A ext :=
  Prost.encodeVarint_ok_ext b A ext (do_reserve_ok_ext hA)

theorem encodeVarint_ok_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    Prost.EncodeVarintOkExt b A ext :=
  Prost.encodeVarint_ok_ext b A ext (do_reserve_ok_ext hA)

theorem encode_varint_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    Prost.EncodeVarintOkExt b A ext :=
  encode_varint_ok_ext hH.toAllocContracts

theorem encode_varint_ok_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    Prost.EncodeVarintOk_trap b C A abs :=
  Prost.encodeVarint_ok_trap b C A abs (do_reserve_ok_trap hA)

theorem encode_varint_ok
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    Prost.EncodeVarintOk b C A ctl abs :=
  (trTrapProgAt_fnAddr_eq b C ctl abs Prost.encodeVarintName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (Prost.encodeVarintSpec A))
    (subroutine_ok_kit_of_trTrap (encode_varint_ok_trap hA))

theorem encodeVarint_ok_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    Prost.EncodeVarintOk_trap b C A abs :=
  Prost.encodeVarint_ok_trap b C A abs (do_reserve_ok_trap hA)

theorem encodeVarint_ok
    (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    Prost.EncodeVarintOk b C A ctl abs :=
  encode_varint_ok hA

theorem encode_varint_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    Prost.EncodeVarintOk_trap b C A abs :=
  encode_varint_ok_trap hH.alloc

theorem encode_varint_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    Prost.EncodeVarintOk b C A ctl abs :=
  encode_varint_ok hH.alloc

theorem publicKeyEq_ok_ext
    (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : Rust.withPanics ext "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook) :
    Getters.PublicKeyEqOkExt b ext :=
  ConsumeMessageKeyTransfer.publicKeyEq_ok_ext b h_bb

theorem publicKeyEq_ok_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    Getters.PublicKeyEqOk_trap b C abs :=
  ConsumeMessageKeyTransfer.publicKeyEq_ok_trap b C abs

theorem publicKeyEq_ok
    (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Getters.PublicKeyEqOk b C ctl abs :=
  ConsumeMessageKeyTransfer.publicKeyEq_ok b C ctl abs

theorem is_same_account_ok_ext
    (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : Rust.withPanics ext "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.isSameAccountName)
      Getters.isSameAccountSpec :=
  Getters.is_same_account_ok_ext b ext (ConsumeMessageKeyTransfer.publicKeyEq_ok_ext b h_bb)

theorem is_same_account_ok_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr Getters.isSameAccountName)
      Getters.isSameAccountSpec :=
  Getters.is_same_account_ok_trap b C abs (ConsumeMessageKeyTransfer.publicKeyEq_ok_trap b C abs)

theorem is_same_account_ok
    (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr Getters.isSameAccountName)
      Getters.isSameAccountSpec :=
  (trTrapProgAt_fnAddr_eq b C ctl abs Getters.isSameAccountName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr Getters.isSameAccountSpec)
    (subroutine_ok_kit_of_trTrap (is_same_account_ok_trap b C abs))

/-! ## Callee Wrapper Corollaries -/

theorem publicKeySerializeOk_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    PublicKeySerializeOkExt b A ext :=
  public_key_serialize_ok_ext hA

theorem publicKeySerializeOk_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    PublicKeySerializeOkExt b A ext :=
  public_key_serialize_ok_ext hH.toAllocContracts

theorem publicKeySerializeOk_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    PublicKeySerializeOk_trap b C A abs :=
  public_key_serialize_ok_trap hA

theorem publicKeySerializeOk
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    PublicKeySerializeOk b C A ctl abs :=
  (trTrapProgAt_fnAddr_eq b C ctl abs publicKeySerializeName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (publicKeySerializeSpec A))
    (subroutine_ok_kit_of_trTrap (publicKeySerializeOk_trap hA))

theorem publicKeySerializeOk_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    PublicKeySerializeOk_trap b C A abs :=
  public_key_serialize_ok_trap hH.alloc

theorem publicKeySerializeOk_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    PublicKeySerializeOk b C A ctl abs :=
  publicKeySerializeOk hH.alloc

theorem remoteIdentityKeyOk_ext
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    OutgoingRatchet.RemoteIdentityKeyExtOk img A ext :=
  Getters.remote_identity_key_ok_ext img A ext (pkTryFrom_ok_ext img ext himg)

theorem remoteIdentityKeyOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    OutgoingRatchet.RemoteIdentityKeyOk_trap img C A abs :=
  Getters.remote_identity_key_ok_trap img C A abs himg

theorem remoteIdentityKeyOk
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs :=
  Getters.remote_identity_key_ok img C A ctl abs himg

theorem dropSpeOk_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContracts img.base A ext) :
    OutgoingRatchet.DropSpeExtOk img A ext :=
  Getters.drop_spe_ok_ext himg hA

theorem dropSpeOk_of_tripleRatchetHooks_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    OutgoingRatchet.DropSpeExtOk img A ext :=
  Getters.drop_spe_ok_ext himg hH.toAllocContracts

theorem dropSpeOk_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs) :
    OutgoingRatchet.DropSpeOk_trap img C A abs :=
  Getters.drop_spe_ok_trap himg hA

theorem dropSpeOk
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs) :
    OutgoingRatchet.DropSpeOk img C A ctl abs :=
  Getters.drop_spe_ok himg hA

theorem dropSpeOk_of_tripleRatchetHooks_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hH : TripleRatchetHooks C A S abs) :
    OutgoingRatchet.DropSpeOk_trap img C A abs :=
  Getters.drop_spe_ok_trap himg hH.alloc

theorem dropSpeOk_of_tripleRatchetHooks
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hH : TripleRatchetHooks C A S abs) :
    OutgoingRatchet.DropSpeOk img C A ctl abs :=
  Getters.drop_spe_ok himg hH.alloc

theorem deserializeOk_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    DeserializeOkExt b ext :=
  ConsumeMessageKeyTransfer.deserialize_ok_ext b ext

theorem deserializeOk_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    DeserializeOkExt b (trTrapExterns C abs) :=
  ConsumeMessageKeyTransfer.deserialize_ok_trap b C abs

theorem deserializeOk
    (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    DeserializeOk b C ctl abs :=
  ConsumeMessageKeyTransfer.deserialize_ok b C ctl abs

theorem newFromSliceOk_trap
    {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    NewFromSliceOk_trap img C abs :=
  ConsumeMessageKeyTransfer.new_from_slice_ok_trap img C abs himg

theorem newFromSliceOk
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    NewFromSliceOk img C ctl abs :=
  ConsumeMessageKeyTransfer.new_from_slice_ok img C ctl abs himg

theorem ctEqROOk
    (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CtEqROOk b C ctl abs :=
  ConsumeMessageKeyTransfer.ctEqRO_ok b C ctl abs

theorem encodedLenOk_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prost.EncodedLenOkExt b A ext :=
  Prost.encodedLen_ok_ext b A ext

theorem encodedLenOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    Prost.EncodedLenOkExt b A (trTrapExterns C abs) :=
  Prost.encodedLen_ok_ext b A (trTrapExterns C abs)

theorem encodedLenOk
    (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Prost.EncodedLenOk b C A ctl abs :=
  subroutine_ok_kit_of_trTrap (encodedLenOk_trap b C A abs)

theorem findReceiverChainKeyOk_ext
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)}
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (himg : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOkExt img A ext :=
  findReceiverChainKey_ok_ext hle himg

theorem findReceiverChainKeyOk_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOkExt img A (trTrapExterns C abs) :=
  findReceiverChainKey_ok_ext (ConsumeMessageKeyTransfer.sessionExterns_le_trap C abs) himg

theorem findReceiverChainKeyOk
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOk img C A ctl abs :=
  subroutine_ok_kit_of_trTrap (findReceiverChainKeyOk_trap himg)

theorem messageKeysOk_ext
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img F A ext :=
  messageKeys_ok_ext hA hle himg

theorem messageKeysOk_of_tripleRatchetHooks_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs ext : String → Option (State → State)}
    (hH : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f)
    (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img C.F A ext :=
  messageKeys_ok_ext hH.toAllocContracts hle himg

theorem messageKeysOk_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img C.F A (trTrapExterns C abs) :=
  messageKeys_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA)
    (ConsumeMessageKeyTransfer.sessionExterns_le_trap C abs) himg

theorem messageKeysOk_of_tripleRatchetHooks_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img C.F A (trTrapExterns C abs) :=
  messageKeysOk_trap hH.alloc himg

theorem messageKeysOk
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOk img C A ctl abs :=
  subroutine_ok_kit_of_trTrap (messageKeysOk_trap hA himg)

theorem messageKeysOk_of_tripleRatchetHooks
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOk img C A ctl abs :=
  subroutine_ok_kit_of_trTrap (messageKeysOk_of_tripleRatchetHooks_trap hH himg)

theorem nextChainKeyOk_ext
    {img : Obj.Image} {F : ShaCompress} {abs ext : String → Option (State → State)}
    (hle : ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (himg : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOkExt img F ext :=
  nextChainKey_ok_ext hle himg

theorem nextChainKeyOk_trap
    {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOkExt img C.F (trTrapExterns C abs) :=
  nextChainKey_ok_ext (ConsumeMessageKeyTransfer.sessionExterns_le_trap C abs) himg

theorem nextChainKeyOk
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOk img C ctl abs :=
  subroutine_ok_kit_of_trTrap (nextChainKeyOk_trap himg)

/-! ## `bytes::Bytes` Corollaries -/

theorem bytes_from_vec_inImage_ok_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img) :=
  subroutine_ok_inImage img
    (bytesFromVec_base_ok_ext (ProofLib.ObjectLoad.base_aligned_of_loads himg))

theorem bytes_from_vec_inImage_ok
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img) :=
  bytes_from_vec_inImage_ok_ext himg

theorem promotable_even_drop_inImage_ok_ext
    {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName)
      ((promotableEvenDropSpec A).inImage img) :=
  subroutine_ok_inImage img (promotableEvenDrop_base_ok_ext hA)

theorem promotable_even_drop_inImage_ok
    {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr promotableEvenDropName)
      ((promotableEvenDropSpec A).inImage img) :=
  promotable_even_drop_inImage_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem promotable_odd_drop_inImage_ok_ext
    {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName)
      ((promotableOddDropSpec A).inImage img) :=
  subroutine_ok_inImage img (promotableOddDrop_base_ok_ext hA)

theorem promotable_odd_drop_inImage_ok
    {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr promotableOddDropName)
      ((promotableOddDropSpec A).inImage img) :=
  promotable_odd_drop_inImage_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem bytes_static_drop_inImage_ok_ext
    {img : Obj.Image} {b : BitVec 64} {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr bytesStaticDropName)
      (bytesStaticDropSpec.inImage img) :=
  subroutine_ok_inImage img bytesStaticDrop_base_ok_ext

theorem bytes_static_drop_inImage_ok
    {img : Obj.Image} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr bytesStaticDropName)
      (bytesStaticDropSpec.inImage img) :=
  bytes_static_drop_inImage_ok_ext

theorem bytes_vtable_drop_inImage_ok_ext
    {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (bytesDropFnAddr b ptr bs.length)
      ((bytesVtableDropSpec A ptr bs off).inImage img) :=
  subroutine_ok_inImage img (bytesVtableDrop_base_ok_ext hA ptr bs off)

theorem bytes_vtable_drop_inImage_ok
    {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (bytesDropFnAddr b ptr bs.length)
      ((bytesVtableDropSpec A ptr bs off).inImage img) :=
  bytes_vtable_drop_inImage_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) ptr bs off

/-! ## `TripleRatchetHooks` and `Stage2Contracts` Wrappers -/

theorem finish_grow_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  finish_grow_ok_ext hH.toAllocContracts

theorem finish_grow_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  finish_grow_ok_trap hH.alloc

theorem finish_grow_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs finishGrowName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (finishGrowSpec A))
    (subroutine_ok_kit_of_trTrap (finish_grow_ok_of_tripleRatchetHooks_trap hH))

theorem do_reserve_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (doReserveSpec A) :=
  do_reserve_ok_ext hH.toAllocContracts

theorem do_reserve_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr doReserveName)
      (doReserveSpec A) :=
  do_reserve_ok_trap hH.alloc

theorem do_reserve_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserveName)
      (doReserveSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs doReserveName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (doReserveSpec A))
    (subroutine_ok_kit_of_trTrap (do_reserve_ok_of_tripleRatchetHooks_trap hH))

theorem into_boxed_slice_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec A) :=
  into_boxed_slice_ok_ext hH.toAllocContracts

theorem into_boxed_slice_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec A) :=
  into_boxed_slice_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hH.alloc)

theorem into_boxed_slice_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs intoBoxedSliceName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (intoBoxedSliceSpec A))
    (subroutine_ok_kit_of_trTrap (into_boxed_slice_ok_of_tripleRatchetHooks_trap hH))

theorem try_clone_from_ref_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec A) :=
  try_clone_from_ref_ok_ext hH.toAllocContracts

theorem try_clone_from_ref_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec A) :=
  try_clone_from_ref_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hH.alloc)

theorem try_clone_from_ref_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs tryCloneFromRefName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (tryCloneFromRefSpec A))
    (subroutine_ok_kit_of_trTrap (try_clone_from_ref_ok_of_tripleRatchetHooks_trap hH))

theorem chain_key_to_pb_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec A) :=
  chain_key_to_pb_ok_ext hH.toAllocContracts

theorem chain_key_to_pb_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec A) :=
  chain_key_to_pb_ok_trap hH.alloc

theorem chain_key_to_pb_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainKeyToPbName)
      (chainKeyToPbSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs chainKeyToPbName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (chainKeyToPbSpec A))
    (subroutine_ok_kit_of_trTrap (chain_key_to_pb_ok_of_tripleRatchetHooks_trap hH))

theorem clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.clearUpkName)
      (Getters.clearUpkSpec A) :=
  Getters.clear_unacknowledged_pre_key_message_ok_ext b A ext hH.toAllocContracts

theorem clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr Getters.clearUpkName)
      (Getters.clearUpkSpec A) :=
  Getters.clear_unacknowledged_pre_key_message_ok_trap b C A abs hH.alloc

theorem clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr Getters.clearUpkName)
      (Getters.clearUpkSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs Getters.clearUpkName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (Getters.clearUpkSpec A))
    (subroutine_ok_kit_of_trTrap (clear_unacknowledged_pre_key_message_ok_of_tripleRatchetHooks_trap hH))

theorem drop_vec_message_key_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.dropVecMessageKeyName)
      (Getters.dropVecMessageKeySpec A) :=
  Getters.drop_vec_message_key_ok_ext hH.toAllocContracts

theorem drop_vec_message_key_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr Getters.dropVecMessageKeyName)
      (Getters.dropVecMessageKeySpec A) :=
  Getters.drop_vec_message_key_ok_trap hH.alloc

theorem drop_vec_message_key_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr Getters.dropVecMessageKeyName)
      (Getters.dropVecMessageKeySpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs Getters.dropVecMessageKeyName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (Getters.dropVecMessageKeySpec A))
    (subroutine_ok_kit_of_trTrap (drop_vec_message_key_ok_of_tripleRatchetHooks_trap hH))

theorem drop_chain_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.dropChainName)
      (Getters.dropChainSpec A) :=
  Getters.drop_chain_ok_ext hH.toAllocContracts

theorem drop_chain_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr Getters.dropChainName)
      (Getters.dropChainSpec A) :=
  Getters.drop_chain_ok_trap hH.alloc

theorem drop_chain_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr Getters.dropChainName)
      (Getters.dropChainSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs Getters.dropChainName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (Getters.dropChainSpec A))
    (subroutine_ok_kit_of_trTrap (drop_chain_ok_of_tripleRatchetHooks_trap hH))

theorem drop_vec_chain_ok_of_tripleRatchetHooks_ext
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hH : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.dropVecChainName)
      (Getters.dropVecChainSpec A) :=
  Getters.drop_vec_chain_ok_ext hH.toAllocContracts

theorem drop_vec_chain_ok_of_tripleRatchetHooks_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr Getters.dropVecChainName)
      (Getters.dropVecChainSpec A) :=
  Getters.drop_vec_chain_ok_trap hH.alloc

theorem drop_vec_chain_ok_of_tripleRatchetHooks
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr Getters.dropVecChainName)
      (Getters.dropVecChainSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs Getters.dropVecChainName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (Getters.dropVecChainSpec A))
    (subroutine_ok_kit_of_trTrap (drop_vec_chain_ok_of_tripleRatchetHooks_trap hH))

/-! ## 32-Bit `black_box` and `AllocContractsX` Glue -/

section Ext32Glue

open ProofLib.ProgramReflection

private theorem publicKey_beq_false_of_ne_ext32 {ik1 ik2 : IdentityKey} (h : ik1 ≠ ik2) :
    (ik1.publicKey == ik2.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  cases ik1; cases ik2
  cases heq
  rfl

private theorem publicKeyEq_ok_at_isSameAccount_ext32 (b : BitVec 64)
    (ext : String → Option (State → State))
    (hEq : Getters.PublicKeyEqOkExt32 b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.isSameAccountName +
        bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      Getters.publicKeyEqSpecExt := by
  have hEq' := hEq
  unfold Getters.PublicKeyEqOkExt32 at hEq'
  rwa [Program.fnAddr_rel
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
    (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
      ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) rfl] at hEq'

private theorem stackAt_isSameAccount_split_ext32 (sp : BitVec 64) :
    stackAt sp Getters.isSameAccountStackExt =
      stackAt (sp - 80#64) Getters.publicKeyEqStackExt ∗
      memRegion (sp - 80#64) 32 ∗
      cells (sp - 48#64) 6 := by
  simp only [stackAt, Getters.isSameAccountStackExt, Getters.publicKeyEqStackExt, extHookStack]
  have htop : sp - 80#64 - BitVec.ofNat 64 (64 + 2 ^ 14) =
      sp - BitVec.ofNat 64 (80 + (64 + 2 ^ 14)) := by bv_omega
  rw [htop,
      show (80 + (64 + 2 ^ 14) : Nat) = 64 + 2 ^ 14 + 80 by decide,
      ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (64 + 2 ^ 14 + 80))
        (n := 64 + 2 ^ 14) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 32) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 48#64) 6 (by decide) :
        memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]

attribute [local irreducible] Program.fnOff Program.fetch Program.externAt? in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem is_same_account_ok_of_publicKeyEq_ext32 (b : BitVec 64)
    (ext : String → Option (State → State))
    (hEq : Getters.PublicKeyEqOkExt32 b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.isSameAccountName)
      Getters.isSameAccountSpecExt := by
  simp only [Getters.isSameAccountSpecExt]
  have hEq' := publicKeyEq_ok_at_isSameAccount_ext32 b ext hEq
  simp only [Getters.publicKeyEqSpecExt] at hEq'
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) 0 40
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) 68 20
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨localIkA, localIk, remoteIkA, remoteIk⟩ := x
  dsimp only at *
  subst h_1 h_2
  rw [stackAt_isSameAccount_split_ext32 s0.sp]
  cells_unfold
  wp_pull_exists
  have hne := publicKey_beq_false_of_ne_ext32 h
  wp_steps
  wp_apply
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at *
  wp_steps
  wp_done

theorem hookSat_withPanics_blackBox {ext : String → Option (State → State)}
    {α : Type} {spec : Spec α}
    (h_bb : HookSat ext "subtle::black_box::<u8>" spec) :
    HookSat (Rust.withPanics ext) "subtle::black_box::<u8>" spec := by
  rcases h_bb with ⟨f, hf, hok⟩
  refine ⟨f, ?_, hok⟩
  simpa [Rust.withPanics, Rust.isPanicSymbol] using hf

theorem publicKeyEq_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" FindReceiverChainIndex.blackBoxSpec32) :
    Getters.PublicKeyEqOkExt32 b ext :=
  FindReceiverChainIndex.publicKey_eq_stack_ok_ext32 b (hookSat_withPanics_blackBox h_bb)

theorem is_same_account_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" FindReceiverChainIndex.blackBoxSpec32) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.isSameAccountName)
      Getters.isSameAccountSpecExt :=
  is_same_account_ok_of_publicKeyEq_ext32 b ext (publicKeyEq_ok_ext32 b h_bb)

theorem encode_varint_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    Prost.EncodeVarintOkExtX img A ext :=
  Prost.encode_varint_ok_ext_x hA

theorem publicKeySerializeOk_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr publicKeySerializeName)
      ((publicKeySerializeSpecX A).inImage img) :=
  public_key_serialize_ok_ext_x hA

theorem dropSpeOk_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.dropSpeName)
      ((Getters.dropSpeSpecX A).inImage img) :=
  Getters.drop_spe_ok_x himg hA

theorem finish_grow_ok_ext_x'
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName)
      ((finishGrowSpecX A).inImage img) :=
  finish_grow_ok_ext_x hA

theorem do_reserve_ok_ext_x'
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((doReserveSpecX A).inImage img) :=
  do_reserve_ok_ext_x hA

theorem into_boxed_slice_ok_ext_x'
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr intoBoxedSliceName)
      ((intoBoxedSliceSpecX A).inImage img) :=
  into_boxed_slice_ok_ext_x hA

theorem try_clone_from_ref_ok_ext_x'
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryCloneFromRefName)
      ((tryCloneFromRefSpecX A).inImage img) :=
  try_clone_from_ref_ok_ext_x hA

theorem chain_key_to_pb_ok_ext_x'
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainKeyToPbName)
      ((chainKeyToPbSpecX A).inImage img) :=
  chain_key_to_pb_ok_ext_x hA

theorem clear_unacknowledged_pre_key_message_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.clearUpkName)
      ((Getters.clearUpkSpecX A).inImage img) :=
  Getters.clear_unacknowledged_pre_key_message_ok_x img A ext hA

theorem drop_vec_message_key_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.dropVecMessageKeyName)
      ((Getters.dropVecMessageKeySpecX A).inImage img) :=
  Getters.drop_vec_message_key_ok_x hA

theorem drop_chain_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.dropChainName)
      ((Getters.dropChainSpecX A).inImage img) :=
  Getters.drop_chain_ok_x hA

theorem drop_vec_chain_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.dropVecChainName)
      ((Getters.dropVecChainSpecX A).inImage img) :=
  Getters.drop_vec_chain_ok_x hA

end Ext32Glue

end CryptoVerification.LibsignalTripleRatchet.Glue
