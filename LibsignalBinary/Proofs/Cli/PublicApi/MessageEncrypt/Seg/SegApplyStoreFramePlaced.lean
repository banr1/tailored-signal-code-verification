/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStoreFrame
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Relocatable CLI `SegApplyStore` Frame and Poll-Output Helpers

Relocatable (`[LibsignalPlacement]`) passive-frame and `storePollPlacedOutAt` decomposition lemmas
for `segApplyStore_placed_okV`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Passive frame bundle untouched during the store phase (`+0xde8..+0xe88`) under `[LibsignalPlacement]`. -/
def storePassivePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  memRegion (sp + 0x288#64) 200 ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗
  ((sp + 0x469#64) ↦₈ 0#8) ∗
  cmScratch sp ∗
  encSpillsStoreRest kit.ss_vt ikit.id_vt sp x ∗
  storePollRest sp ∗
  memRegion x.ret 248 ∗
  FromRecordCallees.lsLogOff ∗
  ikit.identityAt x.idA ist ∗
  cliEncCommonRest A ctl x draws s0

theorem store_mem_split_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    ((sessionRecordAt A (sp + 0x110#64) g' rec' ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 0#8)) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x draws s0) ∗ encStoreExtraPlaced kit st ikit ist x s0 ⊢
    ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ((storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
    storePassivePlaced kit ikit ist ctl x k m draws s0) := by
  subst hsp
  dsimp only [storeBaseActive, storePassivePlaced]
  set sp := s0.sp - 0xbe0#64
  have hpre :
      ((sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0) ∗ encStoreExtraPlaced kit st ikit ist x s0 =
      ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      ((kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack) ∗
      (((sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      protocolAddressAt A x.rem x.remA ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
      cliEncCommonRest A ctl x draws s0))) := by
    rw [encCommonPlaced_eq]
    unfold encStoreExtraPlaced
    ac_rfl
  rw [hpre]
  refine Entails.pure_left fun hbound => Entails.pure_right hbound ?_
  have hj :
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit) := by
    have h1 := encSubStack_join_extra_placed kit st ikit ist x s0 hbound
    unfold encStoreExtraPlaced at h1
    have h0 : kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      (⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack)) ∗
        stackAt sp encSubStack :=
      Entails.trans (Entails.pure_right hbound (Entails.refl _)) (Entails.of_eq (by ac_rfl))
    exact Entails.trans h0 h1
  refine Entails.trans (sepConj_mono_left hj) ?_
  rw [encSpillsAt_store_eq, storePoll_split]
  exact Entails.of_eq (by ac_rfl)

theorem store_mem_to_stored_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    (storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
    storePassivePlaced kit ikit ist ctl x k m draws s0 ⊢
    (((∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g rec') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x draws s0) ∗ encStoreExtraPlaced kit st ikit ist x s0 := by
  subst hsp
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra_placed kit st ikit ist x s0 hbound
  have hrec : sessionRecordAt A (sp + 0x110#64) g' rec' ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g rec' :=
    Entails.sepExists_right g' (Entails.refl _)
  have h469 := pointsTo8_entails_memRegion (sp + 0x469#64) 0#8
  dsimp only [storeBaseActive, storePassivePlaced]
  have hreord1 :
      ((((sp + 0xc0#64) ↦₆₄ x.remA ∗ (sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗ stackAt sp (encSubStackV kit ikit) ∗ A.pool ∗
        kit.storeAt x.ssA st) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      cmScratch sp ∗ encSpillsStoreRest kit.ss_vt ikit.id_vt sp x ∗ storePollRest sp ∗
      memRegion x.ret 248 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist ∗
      cliEncCommonRest A ctl x draws s0)) =
      (kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit)) ∗
      sessionRecordAt A (sp + 0x110#64) g' rec' ∗
      ((sp + 0x469#64) ↦₈ 0#8) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ cmScratch sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
        protocolAddressAt A x.rem x.remA ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
        cliEncCommonRest A ctl x draws s0) := by
    rw [encSpillsAt_store_eq, storePoll_split]
    ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono hsp_split (sepConj_mono hrec (sepConj_mono_left h469))) ?_
  rw [encCommonPlaced_eq]
  exact Entails.of_eq (by ac_rfl)

theorem store_mem_to_tail_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (w3 w4 w5 : BitVec 64) (H : SepProp) :
    (storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
      H) ∗
    storePassivePlaced kit ikit ist ctl x k m draws s0 ⊢
    (dropRecordSlots A sp cmScratch g' rec' none (some m) (pollWith sp 0x9b0 [w3, w4, w5]) ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0 ∗ encStoreExtraPlaced kit st ikit ist x s0 := by
  subst hsp
  dsimp only [storeBaseActive, storePassivePlaced]
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra_placed kit st ikit ist x s0 hbound
  have hpoll := storePoll_merge_9b0 sp w3 w4 w5
  have hk : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
    have hlen : k.publicKey.bytes.toList.length = 0x20 := k.publicKey.bytes.property
    rwa [hlen] at h
  have h280 := pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64)
  have h468 := pointsTo8_entails_memRegion (sp + 0x468#64) 0#8
  have hreord :
      ((((sp + 0xc0#64) ↦₆₄ x.remA ∗ (sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗ stackAt sp (encSubStackV kit ikit) ∗ A.pool ∗
        kit.storeAt x.ssA st) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗ H) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      cmScratch sp ∗ encSpillsStoreRest kit.ss_vt ikit.id_vt sp x ∗ storePollRest sp ∗
      memRegion x.ret 248 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist ∗
      cliEncCommonRest A ctl x draws s0)) =
      (kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit)) ∗
      ((cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        (memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8)) ∗
        (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
          (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
          storePollRest sp)) ∗
        H ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        protocolAddressAt A x.rem x.remA ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
        cliEncCommonRest A ctl x draws s0) := by
    rw [encSpillsAt_store_eq]
    ac_rfl
  rw [hreord]
  have hslots :
      cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        (memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8)) ∗
        (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
          (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
          storePollRest sp) ⊢
      dropRecordSlots A sp cmScratch g' rec' none (some m) (pollWith sp 0x9b0 [w3, w4, w5]) := by
    dsimp only [dropRecordSlots, otrSlotAt, cmSlotAt]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h280
      (sepConj_mono_right (sepConj_mono (sepConj_mono hk (sepConj_mono_right h468)) hpoll))))
  refine Entails.trans (sepConj_mono hsp_split (sepConj_mono_left hslots)) ?_
  rw [encCommonPlaced_eq]
  exact Entails.of_eq (by ac_rfl)

/-- Layout-independent poll output normalization after `kit.storePoll`: gives 6 words
`[w0, w1, w2, w3, w4, w5]` at `out = sp + 0x580` plus staged resource `H`. -/
theorem storePollPlacedOut_words (out : BitVec 64) (ans : Except Unit Unit) :
    storePollPlacedOutAt out ans ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ H : SepProp,
      ⌜(w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) ∧
        w0 = pollTag ans ∧
        (ans = .ok () → H = emp) ∧
        (ans = .error () →
          H = (w1 ↦ᵣ storeHookStr) ∧ w2 = 10#64 ∧ w3 = 1#64)⌝ ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗ H := by
  rcases ans with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [storePollPlacedOutAt, errTailPlacedAt, pollTag]
    refine Entails.sepExists_elim fun strPtr => Entails.sepExists_elim fun vt => ?_
    rw [ProofLib.memRegion_eight (out + 0x28#64)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    refine Entails.sepExists_right 0x800000000000001A#64 (Entails.sepExists_right strPtr
      (Entails.sepExists_right 10#64 (Entails.sepExists_right 1#64
      (Entails.sepExists_right vt (Entails.sepExists_right w5
      (Entails.sepExists_right (strPtr ↦ᵣ storeHookStr) ?_))))))
    refine Entails.pure_right ⟨Or.inr rfl, rfl, (fun h => nomatch h),
      fun _ => ⟨rfl, rfl, rfl⟩⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [storePollPlacedOutAt, pollTag]
    rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) by decide,
        memRegion_split (out + 8#64) 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 8 (by decide),
        ProofLib.memRegion_eight (out + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
      Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
      Entails.sepExists_elim fun w1 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right emp ?_))))))
    refine Entails.pure_right ⟨Or.inl rfl, rfl, fun _ => rfl, (fun h => nomatch h)⟩ ?_
    rw [sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
