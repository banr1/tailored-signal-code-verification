/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon

/-!
# Poll Buffer, Frame Bundles, and Call Wrappers for `segTrust_ok`

Separation-logic poll-buffer splittings, active/passive frame bundles for `CmState`, `SaveState`,
and `EncTail`, and `SepWPp` call wrappers for `segTrust`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Poll Buffer and Slot Framing Lemmas -/

def trustPollRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x46a#64) 6 ∗
  memRegion (sp + 0x4a0#64) 0xe0 ∗
  memRegion (sp + 0x5b0#64) 0x3c0 ∗
  memRegion (sp + 0x988#64) 0x48 ∗
  memRegion (sp + 0x9e8#64) 0x198

theorem trustPoll_split (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x480#64) 32 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      trustPollRest sp := by
  unfold trustPollRest
  rw [show (0x716 : Nat) = 6 + 0x710 by decide,
      memRegion_split (sp + 0x46a#64) 6 0x710 (by decide),
      show (0x710 : Nat) = 16 + 0x700 by decide,
      memRegion_split _ 16 0x700 (by decide),
      show (0x700 : Nat) = 32 + 0x6e0 by decide,
      memRegion_split _ 32 0x6e0 (by decide),
      show (0x6e0 : Nat) = 0xe0 + 0x600 by decide,
      memRegion_split _ 0xe0 0x600 (by decide),
      show (0x600 : Nat) = 48 + 0x5d0 by decide,
      memRegion_split _ 48 0x5d0 (by decide),
      show (0x5d0 : Nat) = 0x3c0 + 0x210 by decide,
      memRegion_split _ 0x3c0 0x210 (by decide),
      show (0x210 : Nat) = 24 + 0x1f8 by decide,
      memRegion_split _ 24 0x1f8 (by decide),
      show (0x1f8 : Nat) = 0x48 + 0x1b0 by decide,
      memRegion_split _ 0x48 0x1b0 (by decide),
      show (0x1b0 : Nat) = 24 + 0x198 by decide,
      memRegion_split _ 24 0x198 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem words2_entails_memRegion16 (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ⊢ memRegion a 16 := by
  rw [memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

theorem words3_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_split a 8 16 (by decide), memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem words6_entails_memRegion48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion a 48 := by
  have h := words64At_entails_memRegion [w0, w1, w2, w3, w4, w5] a (by simp)
  dsimp only [words64At, List.length] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at h
  exact h

theorem trustPoll_merge_save (sp : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x480#64) 32 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      trustPollRest sp ⊢
    memRegion (sp + 0x46a#64) 0x716 := by
  rw [trustPoll_split sp]
  exact Entails.refl _

theorem trustPoll_merge_970 (sp w3 w4 w5 : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x480#64) 32 ∗
      memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x970#64) ↦₆₄ w3) ∗ ((sp + 0x978#64) ↦₆₄ w4) ∗ ((sp + 0x980#64) ↦₆₄ w5)) ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      trustPollRest sp ⊢
    pollWith sp 0x970 [w3, w4, w5] := by
  unfold pollWith trustPollRest
  dsimp only [words64At, List.length]
  change _ ⊢ memRegion (sp + 0x46a#64) 0x506 ∗
    (((sp + 0x970#64) ↦₆₄ w3) ∗ ((sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗
      ((sp + 0x970#64 + 8#64 + 8#64) ↦₆₄ w5) ∗ emp) ∗
    memRegion (sp + 0x988#64) 0x1f8
  rw [show (0x506 : Nat) = 6 + (16 + (32 + (0xe0 + (48 + 0x3c0)))) by decide,
      memRegion_split (sp + 0x46a#64) 6 _ (by decide),
      memRegion_split _ 16 _ (by decide),
      memRegion_split _ 32 _ (by decide),
      memRegion_split _ 0xe0 _ (by decide),
      memRegion_split _ 48 0x3c0 (by decide),
      show (0x1f8 : Nat) = 0x48 + (24 + 0x198) by decide,
      memRegion_split (sp + 0x988#64) 0x48 (24 + 0x198) (by decide),
      memRegion_split _ 24 0x198 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.of_eq

theorem trustPoll_merge_9d0 (sp w3 w4 w5 : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x480#64) 32 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
      trustPollRest sp ⊢
    pollWith sp 0x9d0 [w3, w4, w5] := by
  unfold pollWith trustPollRest
  dsimp only [words64At, List.length]
  change _ ⊢ memRegion (sp + 0x46a#64) 0x566 ∗
    (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d0#64 + 8#64) ↦₆₄ w4) ∗
      ((sp + 0x9d0#64 + 8#64 + 8#64) ↦₆₄ w5) ∗ emp) ∗
    memRegion (sp + 0x9e8#64) 0x198
  rw [show (0x566 : Nat) = 6 + (16 + (32 + (0xe0 + (48 + (0x3c0 + (24 + 0x48)))))) by decide,
      memRegion_split (sp + 0x46a#64) 6 _ (by decide),
      memRegion_split _ 16 _ (by decide),
      memRegion_split _ 32 _ (by decide),
      memRegion_split _ 0xe0 _ (by decide),
      memRegion_split _ 48 _ (by decide),
      memRegion_split _ 0x3c0 _ (by decide),
      memRegion_split _ 24 0x48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.of_eq

theorem cmSlots_to_dropRecordSlots (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (m : CiphertextMessage) (poll : SepProp) :
    sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      cmScratch sp ∗ poll ⊢
    dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) (some m) poll := by
  unfold dropRecordSlots otrSlotAt cmSlotAt
  have hk : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
    have hlen : k.publicKey.bytes.toList.length = 0x20 := k.publicKey.bytes.property
    rwa [hlen] at h
  have h280 := pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64)
  have h468 := pointsTo8_entails_memRegion (sp + 0x468#64) 0#8
  have hreord :
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        cmScratch sp ∗ poll =
      cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        (otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗
        (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8)) ∗ poll := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h280
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono hk (sepConj_mono_right h468))))))

/-! ## Seam Frame Bundles -/

def cmScratchRest (sp : BitVec 64) : SepProp :=
  memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
    memRegion (sp + 0x48#64) 8 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

theorem cmScratch_eq (sp : BitVec 64) :
    cmScratch sp = ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗ cmScratchRest sp := by
  unfold cmScratch cmScratchRest; ac_rfl

def encSpillsRest (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
  ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
  ((sp + 0xc8#64) ↦₆₄ x.locA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0x108#64) ↦₆₄ x.remA)

theorem encSpillsAt_eq (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsAtV ss_vt id_vt sp x =
      ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
      ((sp + 0xe8#64) ↦₆₄ id_vt) ∗ encSpillsRest ss_vt id_vt sp x := by
  unfold encSpillsAtV encSpillsRest; ac_rfl

def encCommonRest (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest draws ∗ encSavedRegs s0.sp s0

theorem encCommon_eq (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) :
    encCommon A ctl img x draws s0 =
      protocolAddressAt A x.rem x.remA ∗ logOff img ∗
      stackAt (s0.sp - 0xbe0#64) encSubStack ∗ A.pool ∗
      encCommonRest A ctl x draws s0 := by
  unfold encCommon encCommonRest; ac_rfl

def cmSlotsRest (A : RustAlloc) (sp : BitVec 64) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) : SepProp :=
  takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
    apiEncResultAt A (sp + 0x370#64) (.ok m)

theorem cmSlots_eq (A : RustAlloc) (sp : BitVec 64) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage) :
    cmSlots A sp sess taken otr' pqCap' pqPtr' k m =
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m := by
  unfold cmSlots cmSlotsRest; ac_rfl

def trustBaseActive (id_vt : BitVec 64) (A : RustAlloc) (img : Obj.Image) (sp : BitVec 64)
    (x : WithStoresEncGhost) (k : IdentityKey) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
  ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  protocolAddressAt A x.rem x.remA ∗
  logOff img ∗
  stackAt sp encSubStack ∗
  A.pool

def trustPassive (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
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
  encCommonRest A ctl x draws s0

theorem seam_mem_split (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    cmSlots A sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x716 ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 =
    (trustBaseActive id_vt A img sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x970#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24) ∗
    trustPassive ss_vt id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0 := by
  subst hsp
  dsimp only [trustBaseActive, trustPassive]
  rw [cmSlots_eq, cmScratch_eq, encSpillsAt_eq, encCommon_eq, trustPoll_split]
  ac_rfl

theorem seam_mem_to_tail (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (P970 P9d0 poll H : SepProp)
    (hpoll :
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp ⊢ poll) :
    (trustBaseActive id_vt A img sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      P970 ∗ P9d0 ∗ H) ∗
    trustPassive ss_vt id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0 ⊢
    ∃∗ g : RecordGhost,
      (dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) (some m)
          poll ∗ H) ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 := by
  subst hsp
  dsimp only [trustBaseActive, trustPassive] at hpoll ⊢
  set sp := s0.sp - 0xbe0#64
  have hreord :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64) ∗ (sp + 0xc0#64) ↦₆₄ x.remA ∗
        (sp + 0xe0#64) ↦₆₄ x.idA ∗ (sp + 0xe8#64) ↦₆₄ id_vt ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ stackAt sp encSubStack ∗ A.pool) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ H) ∗
      (cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗ cmScratchRest sp ∗
      encSpillsRest ss_vt id_vt sp x ∗ memRegion (sp + 0x480#64) 32 ∗ trustPollRest sp ∗
      memRegion x.ret 248 ∗ encCommonRest A ctl x draws s0) =
      (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x480#64) 32 ∗
        memRegion (sp + 0x580#64) 48 ∗ P970 ∗ P9d0 ∗ trustPollRest sp) ∗
      (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗ encCommon A ctl img x draws s0 ∗
      H ∗ memRegion x.ret 248) := by
    rw [cmScratch_eq, encSpillsAt_eq, encCommon_eq]
    change _ = _ ∗ (_ ∗ _ ∗ _ ∗ (protocolAddressAt A x.rem x.remA ∗ logOff img ∗
      stackAt sp encSubStack ∗ A.pool ∗ encCommonRest A ctl x draws s0) ∗ _)
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
      encSpillsAtV ss_vt id_vt sp x ∗ encCommon A ctl img x draws s0 ∗
      H ∗ memRegion x.ret 248 =
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗ poll) ∗
      (H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0) := by
    ac_rfl
  rw [hreord2]
  exact sepConj_mono_left hslots

theorem memRegion16_exists_words2 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 16 ∗ R) :
    ∃ w0 w1 : BitVec 64, m ⊨ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗ R := by
  rw [memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨w1, w0, hm⟩ := hm
  exact ⟨w0, w1, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm⟩

theorem memRegion24_exists_words3 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ w0 w1 w2 : BitVec 64,
      m ⊨ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ∗ R := by
  rw [memRegion_split a 8 16 (by decide), memRegion_split (a + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 8#64 + 8#64)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨w2, w1, w0, hm⟩ := hm
  exact ⟨w0, w1, w2, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm⟩

def trustActive {A : RustAlloc} (img : Obj.Image) (ikit : IdentityStoreSpec A img.base)
    (ist : ikit.IdState) (sp : BitVec 64) (subStack : Nat)
    (x : WithStoresEncGhost) (k : IdentityKey) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
  ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  protocolAddressAt A x.rem x.remA ∗
  logOff img ∗
  ikit.identityAt x.idA ist ∗
  stackAt sp subStack ∗
  A.pool

theorem trustShimStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.trustShimStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV
  omega

theorem trustPollStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.trustPollStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV
  omega

theorem saveShimStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.saveShimStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV
  omega

theorem savePollStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    ikit.savePollStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV
  omega

theorem allocHookStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    allocHookStack ≤ encSubStackV kit ikit := by
  have h1 : allocHookStack ≤ encSubStack := by decide
  have h2 := encSubStack_le_encSubStackV kit ikit
  omega

theorem trustBaseActive_join_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (k : IdentityKey) (s0 : State)
    (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    trustBaseActive ikit.id_vt A img sp x k ∗ encStoreExtra kit st0 ikit ist x s0 ⊢
    ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      trustActive img ikit ist sp (encSubStackV kit ikit) x k ∗
      kit.storeAt x.ssA st0 := by
  subst hsp
  dsimp only [trustBaseActive, trustActive]
  set sp := s0.sp - 0xbe0#64
  have hpre :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
        ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        protocolAddressAt A x.rem x.remA ∗
        logOff img ∗
        stackAt sp encSubStack ∗
        A.pool) ∗ encStoreExtra kit st0 ikit ist x s0 =
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
        logOff img ∗
        A.pool)) := by
    unfold encStoreExtra
    ac_rfl
  rw [hpre]
  refine Entails.pure_left fun hbound => Entails.pure_right hbound ?_
  have hj :
      kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
          (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit) := by
    have h1 := encSubStack_join_extra kit st0 ikit ist x s0 hbound
    unfold encStoreExtra at h1
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

theorem trustActive_split_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (k : IdentityKey) (s0 : State)
    (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    trustActive img ikit ist sp (encSubStackV kit ikit) x k ∗ kit.storeAt x.ssA st0 ⊢
    trustBaseActive ikit.id_vt A img sp x k ∗ encStoreExtra kit st0 ikit ist x s0 := by
  subst hsp
  dsimp only [trustBaseActive, trustActive]
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra kit st0 ikit ist x s0 hbound
  have hreord :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0xe0#64) ↦₆₄ x.idA) ∗
        ((sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        protocolAddressAt A x.rem x.remA ∗
        logOff img ∗
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
        logOff img ∗
        A.pool) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hsp_split) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Normalizes `trustPollOutAt` after `ikit.trustPoll` into six 64-bit words at `sp + 0x580`. -/
theorem trustPollOut_words (b out : BitVec 64) (ans : Except Unit Bool) :
    trustPollOutAt b out ans ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ H : SepProp,
      ⌜(w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) ∧
        match ans with
        | .ok t => H = emp ∧ w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1.setWidth 8 = (if t then 1#8 else 0#8)
        | .error () =>
          H = ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∧
          w0 = 0x800000000000001A#64 ∧ w1 = b + bv% (ls_reloc% 0x77cc) ∧
          w2 = 10#64 ∧ w3 = 1#64 ∧ w4 = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)⌝ ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗ H := by
  rcases ans with ⟨⟨⟩⟩ | t
  · dsimp only [trustPollOutAt, errTailAt]
    rw [ProofLib.memRegion_eight (out + 0x28#64)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    refine Entails.sepExists_right 0x800000000000001A#64 ?_
    refine Entails.sepExists_right (b + bv% (ls_reloc% 0x77cc)) ?_
    refine Entails.sepExists_right 10#64 ?_
    refine Entails.sepExists_right 1#64 ?_
    refine Entails.sepExists_right (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ?_
    refine Entails.pure_right ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [trustPollOutAt]
    rw [show (39 : Nat) = 7 + (8 + (8 + (8 + 8))) by decide,
        memRegion_split (out + 9#64) 7 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 8 (by decide),
        ProofLib.memRegion_eight (out + 9#64 + 7#64),
        ProofLib.memRegion_eight (out + 9#64 + 7#64 + 8#64),
        ProofLib.memRegion_eight (out + 9#64 + 7#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 9#64 + 7#64 + 8#64 + 8#64 + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
      Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 => ?_
    have h8 := pointsTo8_memRegion7_exists_word64 (out + 8#64) (if t then 1#8 else 0#8)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h8
    have hreord :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗
          (memRegion (out + 9#64) 7 ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
            ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
            ((out + 0x28#64) ↦₆₄ w5)) =
        (((out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗ memRegion (out + 9#64) 7) ∗
        ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
          ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
          ((out + 0x28#64) ↦₆₄ w5)) := by ac_rfl
    rw [hreord]
    refine Entails.trans (sepConj_mono_left h8) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun w1 => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hw1 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64 ?_
    refine Entails.sepExists_right w1 ?_
    refine Entails.sepExists_right w2 ?_
    refine Entails.sepExists_right w3 ?_
    refine Entails.sepExists_right w4 ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right emp ?_
    refine Entails.pure_right ⟨Or.inl rfl, rfl, rfl, hw1⟩ ?_
    rw [sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8_eq_exists_body (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  simp only [vecU8, vecU8At, vecHeader, vecU8Body, sepConj_assoc]

theorem memRegion24_exists_byte_rest (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ b0 : BitVec 8, m ⊨ ((a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ∗ memRegion (a + 8#64) 16) ∗ R := by
  rw [memRegion_split a 8 16 (by decide), memRegion_split a 1 7 (by decide),
      ProofLib.memRegion_one a] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨b0, hm⟩ := hm
  exact ⟨b0, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm⟩

theorem words4_memRegion16_entails_memRegion48 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 32#64) 16 ⊢
      memRegion a 48 := by
  rw [memRegion_split a 8 40 (by decide), memRegion_split (a + 8#64) 8 32 (by decide),
      memRegion_split (a + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))

/-! ## Call Wrappers -/

theorem call_nopanic {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  refine SegExit.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic, sepConj_assoc] at h
      exact (not_satisfies_false_sepConj h).elim)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem call_alloc {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpref0 : s0.trace <+: s.trace)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hR : R ⊢ anyHeap ∗ R0 := by exact sepConj_mono_left (entails_anyHeap _))
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  refine SegExit.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic] at h
      exact Satisfies.mono (alloc_onPanic_entails hpref0 hR) h)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (spAligned_of_sp_eq hsp hspm) hcsm hpost

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
