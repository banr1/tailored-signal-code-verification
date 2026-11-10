/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# Ext-Generic `SignedPreKeyStoreKitOk` Bundles

Generalizes `SignedPreKeyStoreKitOk` and `SignedPreKeyStoreKitOkImg` to `tripleRatchetProgAtExt`
over an arbitrary external-hook table `ext : String → Option (State → State)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

/-- Ext-generic code-contract bundle for `kit : SignedPreKeyStoreSpec A b` (without
    `img.FrozenLoaded`) at `tripleRatchetProgAtExt b ext`. -/
structure SignedPreKeyStoreKitOkE {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b)
    (ext : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getShimOff)
    (kitSpkGetShimSpec kit)
  getPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getPollOff)
    (kitSpkGetPollSpecE kit)
  getFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getFutDropOff)
    futDropSpec

theorem SignedPreKeyStoreKitOk.toE {A : RustAlloc} {b : BitVec 64}
    {kit : SignedPreKeyStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SignedPreKeyStoreKitOk kit C ctl abs) :
    SignedPreKeyStoreKitOkE kit (tripleRatchetExterns C ctl abs) :=
  ⟨h.getShim, h.getPoll, h.getFutDrop⟩

theorem SignedPreKeyStoreKitOkE.ofE {A : RustAlloc} {b : BitVec 64}
    {kit : SignedPreKeyStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SignedPreKeyStoreKitOkE kit (tripleRatchetExterns C ctl abs)) :
    SignedPreKeyStoreKitOk kit C ctl abs :=
  ⟨h.getShim, h.getPoll, h.getFutDrop⟩

/-- Ext-generic image-relocated code-contract bundle (`Spec.inImage ... img`, providing
    `img.FrozenLoaded` to shim, poll, and future drop) at `tripleRatchetProgAtExt img.base ext`. -/
structure SignedPreKeyStoreKitOkImgE {A : RustAlloc} (img : Obj.Image)
    (kit : SignedPreKeyStoreSpec A img.base)
    (ext : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getShimOff)
    ((kitSpkGetShimSpec kit).inImage img)
  getPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getPollOff)
    ((kitSpkGetPollSpecE kit).inImage img)
  getFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getFutDropOff)
    (futDropSpec.inImage img)

theorem SignedPreKeyStoreKitOkImg.toE {A : RustAlloc} {img : Obj.Image}
    {kit : SignedPreKeyStoreSpec A img.base}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SignedPreKeyStoreKitOkImg img kit C ctl abs) :
    SignedPreKeyStoreKitOkImgE img kit (tripleRatchetExterns C ctl abs) :=
  ⟨h.getShim, h.getPoll, h.getFutDrop⟩

theorem SignedPreKeyStoreKitOkImgE.ofE {A : RustAlloc} {img : Obj.Image}
    {kit : SignedPreKeyStoreSpec A img.base}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : SignedPreKeyStoreKitOkImgE img kit (tripleRatchetExterns C ctl abs)) :
    SignedPreKeyStoreKitOkImg img kit C ctl abs :=
  ⟨h.getShim, h.getPoll, h.getFutDrop⟩

/-- An ext-generic signed pre-key store that assumes nothing about the image gives
`SignedPreKeyStoreKitOkImgE`. -/
theorem SignedPreKeyStoreKitOkE.toImg {A : RustAlloc} {img : Obj.Image}
    {kit : SignedPreKeyStoreSpec A img.base} {ext : String → Option (State → State)}
    (h : SignedPreKeyStoreKitOkE kit ext) : SignedPreKeyStoreKitOkImgE img kit ext :=
  ⟨subroutine_ok_withEnvPre h.getShim (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.getPoll (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.getFutDrop (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab)⟩

end CryptoVerification.LibsignalPublicApi.StoreKit
