/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# Ext-Generic `SessionStoreKitOkS` Bundle (`SessionStoreKitOkSE`)

Generalizes `SessionStoreKitOkS` to `tripleRatchetProgAtExt img.base ext` over an arbitrary
external-hook table `ext : String → Option (State → State)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession

/-- Ext-generic `SessionStoreKitOkS` bundle for a `SessionStoreSpec` at scope `Scope` over
`tripleRatchetProgAtExt img.base ext`. -/
structure SessionStoreKitOkSE {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop where
  loadShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.loadShimOff)
    ((kitLoadShimSpec kit).inImage img)
  loadPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.loadPollOff)
    (kitLoadPollSpecSE img kit Scope encRecord)
  loadFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.loadFutDropOff)
    futDropSpec
  storeShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.storeShimOff)
    ((kitStoreShimSpec kit).inImage img)
  storePoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.storePollOff)
    ((kitStorePollSpecE kit encRecord).inImage img)
  storeFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.storeFutDropOff)
    futDropSpec
  trustShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 184))
    (isTrustedShimSpec A img.base)
  trustPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16328))
    (isTrustedPollSpec A img.base)
  saveShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 88))
    (saveIdentityShimSpec A img.base)
  savePoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16192))
    (saveIdentityPollSpec A img.base)
  idFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744)) futDropSpec

abbrev SessionStoreKitOkE {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  SessionStoreKitOkSE kit RecordInScope encRecord ext

theorem SessionStoreKitOkS.toE {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SessionStoreKitOkS kit Scope C encRecord ctl abs) :
    SessionStoreKitOkSE kit Scope encRecord (tripleRatchetExterns C ctl abs) :=
  ⟨h.loadShim, h.loadPoll, h.loadFutDrop, h.storeShim, h.storePoll, h.storeFutDrop,
   h.trustShim, h.trustPoll, h.saveShim, h.savePoll, h.idFutDrop⟩

theorem SessionStoreKitOkSE.ofE {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SessionStoreKitOkSE kit Scope encRecord (tripleRatchetExterns C ctl abs)) :
    SessionStoreKitOkS kit Scope C encRecord ctl abs :=
  ⟨h.loadShim, h.loadPoll, h.loadFutDrop, h.storeShim, h.storePoll, h.storeFutDrop,
   h.trustShim, h.trustPoll, h.saveShim, h.savePoll, h.idFutDrop⟩

end CryptoVerification.LibsignalPublicApi.StoreKit
