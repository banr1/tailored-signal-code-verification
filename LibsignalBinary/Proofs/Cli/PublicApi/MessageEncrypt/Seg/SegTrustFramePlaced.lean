/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustFrame
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Relocatable Poll Buffer and Seam Frame Bundles for `segTrust`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

def cliEncCommonRest [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest draws ∗ encSavedRegs s0.sp s0

def cliTrustPassive [LibsignalPlacement] (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗
  cmScratchRest sp ∗
  encSpillsRest ss_vt id_vt sp x ∗
  memRegion (sp + 0x480#64) 32 ∗
  trustPollRest sp ∗
  memRegion x.ret 248 ∗
  cliEncCommonRest A ctl x draws s0

theorem encCommonPlaced_eq [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    encCommonPlaced A ctl x draws s0 =
      protocolAddressAt A x.rem x.remA ∗ FromRecordCallees.lsLogOff ∗
      stackAt (s0.sp - 0xbe0#64) encSubStack ∗ A.pool ∗
      cliEncCommonRest A ctl x draws s0 := by
  unfold encCommonPlaced cliEncCommonRest; ac_rfl

def trustBaseActivePlaced [LibsignalPlacement] (id_vt : BitVec 64) (A : RustAlloc)
    (sp : BitVec 64) (x : WithStoresEncGhost) (k : IdentityKey) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
  ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  protocolAddressAt A x.rem x.remA ∗
  FromRecordCallees.lsLogOff ∗
  stackAt sp encSubStack ∗
  A.pool

theorem seam_mem_split_placed [LibsignalPlacement] (ss_vt id_vt : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    cmSlots A sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x716 ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 =
    (trustBaseActivePlaced id_vt A sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24) ∗
    cliTrustPassive ss_vt id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0 := by
  subst hsp
  dsimp only [trustBaseActivePlaced, cliTrustPassive]
  rw [cmSlots_eq, cmScratch_eq, encSpillsAt_eq, encCommonPlaced_eq, trustPoll_split]
  ac_rfl

theorem seam_mem_to_tail_placed [LibsignalPlacement] (ss_vt id_vt : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (P970 P9d0 poll H : SepProp)
    (hpoll :
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp ⊢ poll) :
    (trustBaseActivePlaced id_vt A sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      P970 ∗ P9d0 ∗ H) ∗
    cliTrustPassive ss_vt id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0 ⊢
    ∃∗ g : RecordGhost,
      (dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) (some m)
          poll ∗ H) ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 := by
  subst hsp
  dsimp only [trustBaseActivePlaced, cliTrustPassive] at hpoll ⊢
  set sp := s0.sp - 0xbe0#64
  have hreord :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64) ∗ (sp + 0xc0#64) ↦₆₄ x.remA ∗
        (sp + 0xe0#64) ↦₆₄ x.idA ∗ (sp + 0xe8#64) ↦₆₄ id_vt ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ stackAt sp encSubStack ∗ A.pool) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ H) ∗
      (cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗ cmScratchRest sp ∗
      encSpillsRest ss_vt id_vt sp x ∗ memRegion (sp + 0x480#64) 32 ∗ trustPollRest sp ∗
      memRegion x.ret 248 ∗ cliEncCommonRest A ctl x draws s0) =
      (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp) ∗
      (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗ encCommonPlaced A ctl x draws s0 ∗
      H ∗ memRegion x.ret 248) := by
    rw [cmScratch_eq, encSpillsAt_eq, encCommonPlaced_eq]
    change _ = _ ∗ (_ ∗ _ ∗ _ ∗ (protocolAddressAt A x.rem x.remA ∗ FromRecordCallees.lsLogOff ∗
      stackAt sp encSubStack ∗ A.pool ∗ cliEncCommonRest A ctl x draws s0) ∗ _)
    ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hpoll) ?_
  unfold cmSlotsRest takenSlots
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  have hslots := cmSlots_to_dropRecordSlots A sp g sess taken otr' pqCap' pqPtr' k m poll
  have hreord2 :
      poll ∗ (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
      (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ encCommonPlaced A ctl x draws s0 ∗
      H ∗ memRegion x.ret 248 =
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗ poll) ∗
      (H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0) := by
    ac_rfl
  rw [hreord2]
  exact sepConj_mono_left hslots

def trustActivePlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState) (sp : BitVec 64) (subStack : Nat)
    (x : WithStoresEncGhost) (k : IdentityKey) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
  ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  protocolAddressAt A x.rem x.remA ∗
  FromRecordCallees.lsLogOff ∗
  ikit.identityAt x.idA ist ∗
  stackAt sp subStack ∗
  A.pool

theorem trustBaseActive_join_extra_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (k : IdentityKey) (s0 : State)
    (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    trustBaseActivePlaced ikit.id_vt A sp x k ∗ encStoreExtraPlaced kit st0 ikit ist x s0 ⊢
    ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      trustActivePlaced ikit ist sp (encSubStackV kit ikit) x k ∗
      kit.storeAt x.ssA st0 := by
  subst hsp
  dsimp only [trustBaseActivePlaced, trustActivePlaced]
  set sp := s0.sp - 0xbe0#64
  have hpre :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
        ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        protocolAddressAt A x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp encSubStack ∗
        A.pool) ∗ encStoreExtraPlaced kit st0 ikit ist x s0 =
      ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      ((kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack) ∗
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
        ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        protocolAddressAt A x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗
        A.pool)) := by
    unfold encStoreExtraPlaced
    ac_rfl
  rw [hpre]
  refine Entails.pure_left fun hbound => Entails.pure_right hbound ?_
  have hj :
      kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit) := by
    have h1 := encSubStack_join_extra_placed kit st0 ikit ist x s0 hbound
    unfold encStoreExtraPlaced at h1
    have h0 :
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗
          memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
            (encSubStackV kit ikit - encSubStack) ∗
          stackAt sp encSubStack ⊢
        (⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
          kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗
          memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
            (encSubStackV kit ikit - encSubStack)) ∗
          stackAt sp encSubStack :=
      Entails.trans (Entails.pure_right hbound (Entails.refl _)) (Entails.of_eq (by ac_rfl))
    exact Entails.trans h0 h1
  refine Entails.trans (sepConj_mono_left hj) ?_
  exact Entails.of_eq (by ac_rfl)

theorem trustActive_split_extra_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (k : IdentityKey) (s0 : State)
    (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    trustActivePlaced ikit ist sp (encSubStackV kit ikit) x k ∗ kit.storeAt x.ssA st0 ⊢
    trustBaseActivePlaced ikit.id_vt A sp x k ∗ encStoreExtraPlaced kit st0 ikit ist x s0 := by
  subst hsp
  dsimp only [trustBaseActivePlaced, trustActivePlaced]
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra_placed kit st0 ikit ist x s0 hbound
  have hreord :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
        ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        protocolAddressAt A x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗
        ikit.identityAt x.idA ist ∗
        stackAt sp (encSubStackV kit ikit) ∗
        A.pool) ∗ kit.storeAt x.ssA st0 =
      (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit)) ∗
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
        ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        protocolAddressAt A x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗
        A.pool) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hsp_split) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Layout-independent poll output normalization after `ikit.trustPoll`: uniformly gives 6 words
`[w0, w1, w2, w3, w4, w5]` at `out = sp + 0x580`. -/
theorem trustPollPlacedOut_words (out : BitVec 64) (ans : Except Unit Bool) :
    trustPollPlacedOutAt out ans ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ H : SepProp,
      ⌜(w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) ∧
        match ans with
        | .ok t => H = emp ∧ w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1.setWidth 8 = (if t then 1#8 else 0#8)
        | .error () =>
          H = (w1 ↦ᵣ storeHookStr) ∧
          w0 = 0x800000000000001A#64 ∧ w2 = 10#64 ∧ w3 = 1#64⌝ ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗ H := by
  rcases ans with ⟨⟨⟩⟩ | t
  · dsimp only [trustPollPlacedOutAt, errTailPlacedAt]
    refine Entails.sepExists_elim fun strPtr => Entails.sepExists_elim fun vt => ?_
    rw [ProofLib.memRegion_eight (out + 0x28#64)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    refine Entails.sepExists_right 0x800000000000001A#64 ?_
    refine Entails.sepExists_right strPtr ?_
    refine Entails.sepExists_right 10#64 ?_
    refine Entails.sepExists_right 1#64 ?_
    refine Entails.sepExists_right vt ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right (strPtr ↦ᵣ storeHookStr) ?_
    refine Entails.pure_right ⟨Or.inr rfl, rfl, rfl, rfl, rfl⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · exact Entails.trans (trustPollOut_words 0#64 out (.ok t))
      (Entails.sepExists_elim fun w0 => Entails.sepExists_right w0
      (Entails.sepExists_elim fun w1 => Entails.sepExists_right w1
      (Entails.sepExists_elim fun w2 => Entails.sepExists_right w2
      (Entails.sepExists_elim fun w3 => Entails.sepExists_right w3
      (Entails.sepExists_elim fun w4 => Entails.sepExists_right w4
      (Entails.sepExists_elim fun w5 => Entails.sepExists_right w5
      (Entails.sepExists_elim fun H => Entails.sepExists_right H (Entails.refl _))))))))

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
