/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStoreFrame
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFrame

/-!
# CLI `SegApplyStore` Frame and `SessionRecord` Helpers

Frame-splitting and `SessionRecord` unpack/fold lemmas for the `SegApplyStore` segment (`+0xd9c..+0xe88`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet


open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

/-! ## 1. Pure Model & `SessionRecord` Unpack/Fold Lemmas -/

/-- Passive frame bundle untouched during the store phase (`+0xde8..+0xe88`). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (_ctl : BitVec 64)
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
  logOff img ∗
  ikit.identityAt x.idA ist ∗
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.store_mem_split {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
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
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0) ∗ encStoreExtra kit st ikit ist x s0 ⊢
    ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ((storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive kit ikit ist ctl x k m draws s0) := by
  subst hsp
  dsimp only [storeBaseActive, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive]
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
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0) ∗ encStoreExtra kit st ikit ist x s0 =
      ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      ((kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
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
      protocolAddressAt A x.rem x.remA ∗ logOff img ∗ A.pool ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0))) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommon_eq]
    unfold encStoreExtra
    ac_rfl
  rw [hpre]
  refine Entails.pure_left fun hbound => Entails.pure_right hbound ?_
  have hj :
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit) := by
    have h1 := encSubStack_join_extra kit st ikit ist x s0 hbound
    unfold encStoreExtra at h1
    have h0 : kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      (⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack)) ∗
        stackAt sp encSubStack :=
      Entails.trans (Entails.pure_right hbound (Entails.refl _)) (Entails.of_eq (by ac_rfl))
    exact Entails.trans h0 h1
  refine Entails.trans (sepConj_mono_left hj) ?_
  rw [encSpillsAt_store_eq, storePoll_split]
  exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.store_mem_to_stored {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    (storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive kit ikit ist ctl x k m draws s0 ⊢
    (((∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g rec') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0) ∗ encStoreExtra kit st ikit ist x s0 := by
  subst hsp
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra kit st ikit ist x s0 hbound
  have hrec : sessionRecordAt A (sp + 0x110#64) g' rec' ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g rec' :=
    Entails.sepExists_right g' (Entails.refl _)
  have h469 := pointsTo8_entails_memRegion (sp + 0x469#64) 0#8
  dsimp only [storeBaseActive, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive]
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
      memRegion x.ret 248 ∗ logOff img ∗ ikit.identityAt x.idA ist ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0)) =
      (kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit)) ∗
      sessionRecordAt A (sp + 0x110#64) g' rec' ∗
      ((sp + 0x469#64) ↦₈ 0#8) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ cmScratch sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
        protocolAddressAt A x.rem x.remA ∗ logOff img ∗ A.pool ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0) := by
    rw [encSpillsAt_store_eq, storePoll_split]
    ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono hsp_split (sepConj_mono hrec (sepConj_mono_left h469))) ?_
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommon_eq]
  exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.store_mem_to_tail {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
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
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive kit ikit ist ctl x k m draws s0 ⊢
    (dropRecordSlots A sp cmScratch g' rec' none (some m) (pollWith sp 0x9b0 [w3, w4, w5]) ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ encStoreExtra kit st ikit ist x s0 := by
  subst hsp
  dsimp only [storeBaseActive, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.storePassive]
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra kit st ikit ist x s0 hbound
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
      memRegion x.ret 248 ∗ logOff img ∗ ikit.identityAt x.idA ist ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0)) =
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
        protocolAddressAt A x.rem x.remA ∗ logOff img ∗ A.pool ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommonRest A img.base x draws s0) := by
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
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.encCommon_eq]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
