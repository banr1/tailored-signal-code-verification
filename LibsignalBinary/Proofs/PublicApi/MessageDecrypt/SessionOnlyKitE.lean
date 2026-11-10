/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitE

/-!
# External-Hook-Generic `SessionOnlyKitOkS` Bundle

Generalizes `SessionOnlyKitOkS` from `tripleRatchetProgAt img.base C ctl abs` to
`tripleRatchetProgAtExt img.base ext` for arbitrary external-hook tables `ext`, with definitional
conversions `.toE` and `.ofE`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

/-- Ext-generic session-store-only `subroutine_ok` bundle (load/store shims, polls, and future
drops) at `tripleRatchetProgAtExt img.base ext`. -/
structure SessionOnlyKitOkSE {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
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

theorem SessionOnlyKitOkS.toE {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SessionOnlyKitOkS kit Scope C encRecord ctl abs) :
    SessionOnlyKitOkSE kit Scope encRecord (tripleRatchetExterns C ctl abs) :=
  ⟨h.loadShim, h.loadPoll, h.loadFutDrop, h.storeShim, h.storePoll, h.storeFutDrop⟩

theorem SessionOnlyKitOkSE.ofE {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SessionOnlyKitOkSE kit Scope encRecord (tripleRatchetExterns C ctl abs)) :
    SessionOnlyKitOkS kit Scope C encRecord ctl abs :=
  ⟨h.loadShim, h.loadPoll, h.loadFutDrop, h.storeShim, h.storePoll, h.storeFutDrop⟩

theorem SessionStoreKitOkSE.toSessionOnly {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    (h : SessionStoreKitOkSE kit Scope encRecord ext) :
    SessionOnlyKitOkSE kit Scope encRecord ext :=
  ⟨h.loadShim, h.loadPoll, h.loadFutDrop, h.storeShim, h.storePoll, h.storeFutDrop⟩

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem SessionOnlyKitPlacedOkSE.loadShim_197 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_197 H) (0#64 + kit.loadShimOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadShimSpec kit)) :=
  h.loadShim (callerBlk := 197) (by decide)

theorem SessionOnlyKitPlacedOkSE.loadPoll_197 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_197 H) (0#64 + kit.loadPollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitLoadPollPlacedSpecSE kit Scope encRecord)) :=
  h.loadPoll (callerBlk := 197) (by decide)

theorem SessionOnlyKitPlacedOkSE.loadFutDrop_197 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_197 H) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec) :=
  h.loadFutDrop (callerBlk := 197) (by decide)

theorem SessionOnlyKitPlacedOkSE.storeShim_197 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_197 H) (0#64 + kit.storeShimOff)
      (StoreKit.withLsRoCl lsmpl (kitStoreShimSpec kit)) :=
  h.storeShim (callerBlk := 197) (by decide)

theorem SessionOnlyKitPlacedOkSE.storePoll_197 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_197 H) (0#64 + kit.storePollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitStorePollPlacedSpecE kit encRecord)) :=
  h.storePoll (callerBlk := 197) (by decide)

theorem SessionOnlyKitPlacedOkSE.storeFutDrop_197 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_197 H) (0#64 + kit.storeFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec) :=
  h.storeFutDrop (callerBlk := 197) (by decide)

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt
