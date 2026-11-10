/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# Extern-Generic `KyberPreKeyStoreKitOk` Bundles (`KyberPreKeyStoreKitOkE`, `KyberPreKeyStoreKitOkImgE`)

Generalizes `KyberPreKeyStoreKitOk` and `KyberPreKeyStoreKitOkImg` from `tripleRatchetProgAt` to
`tripleRatchetProgAtExt` for arbitrary external-hook tables `ext`.
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

/-- Ext-generic code-contract bundle for `kit : KyberPreKeyStoreSpec A b` (without
    `img.FrozenLoaded`) at `tripleRatchetProgAtExt b ext`. -/
structure KyberPreKeyStoreKitOkE {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b)
    (ext : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getShimOff)
    (kitKpkGetShimSpec kit)
  getPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getPollOff)
    (kitKpkGetPollSpecE kit)
  getFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getFutDropOff)
    futDropSpec
  markShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.markShimOff)
    (kitKpkMarkShimSpec kit)
  markPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.markPollOff)
    (kitKpkMarkPollSpecE kit)
  markFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.markFutDropOff)
    futDropSpec

theorem KyberPreKeyStoreKitOk.toE {A : RustAlloc} {b : BitVec 64}
    {kit : KyberPreKeyStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : KyberPreKeyStoreKitOk kit C ctl abs) :
    KyberPreKeyStoreKitOkE kit (tripleRatchetExterns C ctl abs) :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.markShim, h.markPoll, h.markFutDrop⟩

theorem KyberPreKeyStoreKitOkE.ofE {A : RustAlloc} {b : BitVec 64}
    {kit : KyberPreKeyStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : KyberPreKeyStoreKitOkE kit (tripleRatchetExterns C ctl abs)) :
    KyberPreKeyStoreKitOk kit C ctl abs :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.markShim, h.markPoll, h.markFutDrop⟩

/-- Ext-generic image-relocated code-contract bundle (`Spec.inImage ... img`, providing
    `img.FrozenLoaded` to every shim, poll, and future drop) at
    `tripleRatchetProgAtExt img.base ext`. -/
structure KyberPreKeyStoreKitOkImgE {A : RustAlloc} (img : Obj.Image)
    (kit : KyberPreKeyStoreSpec A img.base)
    (ext : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getShimOff)
    ((kitKpkGetShimSpec kit).inImage img)
  getPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getPollOff)
    ((kitKpkGetPollSpecE kit).inImage img)
  getFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getFutDropOff)
    (futDropSpec.inImage img)
  markShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.markShimOff)
    ((kitKpkMarkShimSpec kit).inImage img)
  markPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.markPollOff)
    ((kitKpkMarkPollSpecE kit).inImage img)
  markFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + kit.markFutDropOff) (futDropSpec.inImage img)

theorem KyberPreKeyStoreKitOkImg.toE {A : RustAlloc} {img : Obj.Image}
    {kit : KyberPreKeyStoreSpec A img.base}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : KyberPreKeyStoreKitOkImg img kit C ctl abs) :
    KyberPreKeyStoreKitOkImgE img kit (tripleRatchetExterns C ctl abs) :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.markShim, h.markPoll, h.markFutDrop⟩

theorem KyberPreKeyStoreKitOkImgE.ofE {A : RustAlloc} {img : Obj.Image}
    {kit : KyberPreKeyStoreSpec A img.base}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : KyberPreKeyStoreKitOkImgE img kit (tripleRatchetExterns C ctl abs)) :
    KyberPreKeyStoreKitOkImg img kit C ctl abs :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.markShim, h.markPoll, h.markFutDrop⟩

/-- An ext-generic Kyber pre-key store that assumes nothing about the image gives
`KyberPreKeyStoreKitOkImgE`. -/
theorem KyberPreKeyStoreKitOkE.toImg {A : RustAlloc} {img : Obj.Image}
    {kit : KyberPreKeyStoreSpec A img.base} {ext : String → Option (State → State)}
    (h : KyberPreKeyStoreKitOkE kit ext) : KyberPreKeyStoreKitOkImgE img kit ext :=
  ⟨subroutine_ok_withEnvPre h.getShim (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.getPoll (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.getFutDrop (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.markShim (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.markPoll (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.markFutDrop (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab)⟩

end CryptoVerification.LibsignalPublicApi.StoreKit
