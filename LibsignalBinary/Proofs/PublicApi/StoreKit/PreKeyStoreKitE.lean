/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# Ext-Generic `PreKeyStoreKitOk` Bundles

Generalizes `PreKeyStoreKitOk` and `PreKeyStoreKitOkImg` to `tripleRatchetProgAtExt` over an
arbitrary external-hook table `ext : String → Option (State → State)`.
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

/-- Ext-generic code-contract bundle for `kit : PreKeyStoreSpec A b` (without `img.FrozenLoaded`,
    as used by in-memory E2E stores) at `tripleRatchetProgAtExt b ext`. -/
structure PreKeyStoreKitOkE {A : RustAlloc} {b : BitVec 64} (kit : PreKeyStoreSpec A b)
    (ext : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getShimOff)
    (kitPreKeyGetShimSpec kit)
  getPoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getPollOff)
    (kitPreKeyGetPollSpecE kit)
  getFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.getFutDropOff)
    futDropSpec
  removeShim : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.removeShimOff)
    (kitPreKeyRemoveShimSpec kit)
  removePoll : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.removePollOff)
    (kitPreKeyRemovePollSpecE kit)
  removeFutDrop : subroutine_ok (tripleRatchetProgAtExt b ext) (b + kit.removeFutDropOff)
    futDropSpec

theorem PreKeyStoreKitOk.toE {A : RustAlloc} {b : BitVec 64} {kit : PreKeyStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : PreKeyStoreKitOk kit C ctl abs) :
    PreKeyStoreKitOkE kit (tripleRatchetExterns C ctl abs) :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.removeShim, h.removePoll, h.removeFutDrop⟩

theorem PreKeyStoreKitOkE.ofE {A : RustAlloc} {b : BitVec 64} {kit : PreKeyStoreSpec A b}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : PreKeyStoreKitOkE kit (tripleRatchetExterns C ctl abs)) :
    PreKeyStoreKitOk kit C ctl abs :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.removeShim, h.removePoll, h.removeFutDrop⟩

/-- Ext-generic image-relocated code-contract bundle (`Spec.inImage ... img`, providing
    `img.FrozenLoaded` to every shim, poll, and future drop) at
    `tripleRatchetProgAtExt img.base ext`. -/
structure PreKeyStoreKitOkImgE {A : RustAlloc} (img : Obj.Image)
    (kit : PreKeyStoreSpec A img.base)
    (ext : String → Option (State → State)) : Prop where
  getShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getShimOff)
    ((kitPreKeyGetShimSpec kit).inImage img)
  getPoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getPollOff)
    ((kitPreKeyGetPollSpecE kit).inImage img)
  getFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.getFutDropOff)
    (futDropSpec.inImage img)
  removeShim : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.removeShimOff)
    ((kitPreKeyRemoveShimSpec kit).inImage img)
  removePoll : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + kit.removePollOff)
    ((kitPreKeyRemovePollSpecE kit).inImage img)
  removeFutDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + kit.removeFutDropOff) (futDropSpec.inImage img)

theorem PreKeyStoreKitOkImg.toE {A : RustAlloc} {img : Obj.Image}
    {kit : PreKeyStoreSpec A img.base}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : PreKeyStoreKitOkImg img kit C ctl abs) :
    PreKeyStoreKitOkImgE img kit (tripleRatchetExterns C ctl abs) :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.removeShim, h.removePoll, h.removeFutDrop⟩

theorem PreKeyStoreKitOkImgE.ofE {A : RustAlloc} {img : Obj.Image}
    {kit : PreKeyStoreSpec A img.base}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : PreKeyStoreKitOkImgE img kit (tripleRatchetExterns C ctl abs)) :
    PreKeyStoreKitOkImg img kit C ctl abs :=
  ⟨h.getShim, h.getPoll, h.getFutDrop, h.removeShim, h.removePoll, h.removeFutDrop⟩

/-- An ext-generic pre-key store that assumes nothing about the image gives
`PreKeyStoreKitOkImgE`. -/
theorem PreKeyStoreKitOkE.toImg {A : RustAlloc} {img : Obj.Image}
    {kit : PreKeyStoreSpec A img.base} {ext : String → Option (State → State)}
    (h : PreKeyStoreKitOkE kit ext) : PreKeyStoreKitOkImgE img kit ext :=
  ⟨subroutine_ok_withEnvPre h.getShim (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.getPoll (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.getFutDrop (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.removeShim (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.removePoll (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab),
   subroutine_ok_withEnvPre h.removeFutDrop (fun s => img.FrozenLoaded s ∧ s.symtab = img.symtab)⟩

end CryptoVerification.LibsignalPublicApi.StoreKit
