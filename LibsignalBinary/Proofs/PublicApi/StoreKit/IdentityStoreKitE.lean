/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# Extern-Generic `IdentityStoreKitOk` Bundles (`IdentityStoreKitOkE`, `IdentityStoreKitOkIE`)

Generalizes `IdentityStoreKitOk` and `IdentityStoreKitOkI` from `tripleRatchetProgAt b C ctl abs` to
`tripleRatchetProgAtExt b ext` for arbitrary external-hook tables `ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit.Identity

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Ext-generic `IdentityStoreKitOk` bundle for an `IdentityStoreSpec` at
`tripleRatchetProgAtExt b ext`. -/
structure IdentityStoreKitOkE {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ext : String → Option (State → State)) : Prop where
  trustShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.trustShimOff)
    (kitTrustShimSpec ikit)
  trustPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.trustPollOff)
    (kitTrustPollSpecE ikit)
  trustFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.trustFutDropOff)
    futDropSpec
  saveShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.saveShimOff)
    (kitSaveShimSpec ikit)
  savePoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.savePollOff)
    (kitSavePollSpecE ikit)
  saveFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.saveFutDropOff)
    futDropSpec

theorem IdentityStoreKitOk.toE {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : IdentityStoreKitOk ikit C ctl abs) :
    IdentityStoreKitOkE ikit (tripleRatchetExterns C ctl abs) :=
  ⟨h.trustShim, h.trustPoll, h.trustFutDrop, h.saveShim, h.savePoll, h.saveFutDrop⟩

theorem IdentityStoreKitOkE.ofE {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : IdentityStoreKitOkE ikit (tripleRatchetExterns C ctl abs)) :
    IdentityStoreKitOk ikit C ctl abs :=
  ⟨h.trustShim, h.trustPoll, h.trustFutDrop, h.saveShim, h.savePoll, h.saveFutDrop⟩

/-- Ext-generic `IdentityStoreKitOkI` bundle (`withLogOff … .inImage img` on polls and `.inImage img`
on shims) at `tripleRatchetProgAtExt b ext`. -/
structure IdentityStoreKitOkIE {A : RustAlloc} {b : BitVec 64} (img : Obj.Image)
    (ikit : IdentityStoreSpec A b)
    (ext : String → Option (State → State)) : Prop where
  trustShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.trustShimOff)
    ((kitTrustShimSpec ikit).inImage img)
  trustPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.trustPollOff)
    (kitTrustPollSpecI img ikit)
  trustFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.trustFutDropOff)
    futDropSpec
  saveShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.saveShimOff)
    ((kitSaveShimSpec ikit).inImage img)
  savePoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.savePollOff)
    (kitSavePollSpecI img ikit)
  saveFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + ikit.saveFutDropOff)
    futDropSpec

theorem IdentityStoreKitOkI.toE {A : RustAlloc} {b : BitVec 64} {img : Obj.Image}
    {ikit : IdentityStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : IdentityStoreKitOkI img ikit C ctl abs) :
    IdentityStoreKitOkIE img ikit (tripleRatchetExterns C ctl abs) :=
  ⟨h.trustShim, h.trustPoll, h.trustFutDrop, h.saveShim, h.savePoll, h.saveFutDrop⟩

theorem IdentityStoreKitOkIE.ofE {A : RustAlloc} {b : BitVec 64} {img : Obj.Image}
    {ikit : IdentityStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : IdentityStoreKitOkIE img ikit (tripleRatchetExterns C ctl abs)) :
    IdentityStoreKitOkI img ikit C ctl abs :=
  ⟨h.trustShim, h.trustPoll, h.trustFutDrop, h.saveShim, h.savePoll, h.saveFutDrop⟩

/-- An ext-generic identity store that assumes nothing about the image gives
`IdentityStoreKitOkIE`. -/
theorem IdentityStoreKitOkE.toI {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (h : IdentityStoreKitOkE ikit ext) : IdentityStoreKitOkIE img ikit ext where
  trustShim := subroutine_ok_inImage_of_subroutine_ok img h.trustShim
  trustPoll := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withLogOff img h.trustPoll fun _ _ _ => by
      dsimp only [kitTrustPollSpecE, withEnvPre, kitTrustPollSpec]
      rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _))
  trustFutDrop := h.trustFutDrop
  saveShim := subroutine_ok_inImage_of_subroutine_ok img h.saveShim
  savePoll := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withLogOff img h.savePoll fun _ _ _ => by
      dsimp only [kitSavePollSpecE, withEnvPre, kitSavePollSpec]
      rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _))
  saveFutDrop := h.saveFutDrop

end CryptoVerification.LibsignalPublicApi.StoreKit.Identity

namespace CryptoVerification.LibsignalPublicApi.StoreKit

export Identity
  (IdentityStoreKitOkE IdentityStoreKitOkIE IdentityStoreKitOkE.toI)

end CryptoVerification.LibsignalPublicApi.StoreKit
