/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound

/-!
# Relocatable `segPreKey` `PreKeySignalMessage::new` and Result Copy (`+0x8c8..+0xa70`)

Proves `segPreKey_buildMessage_placed_ok` on Block `464` (`lsProg_464 Hk`) under
`[LibsignalPlacement]`, stepping from `PreKeyEncryptRetStatePlaced` on `.ok sm` to `CmStateVPlaced`
at `+0xa70`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Obj.MultiPlacedLib.blockProgram

/-! ## 1. Placed Frame Unpack and Pack Helpers for E6d, `preKeyMsgNewSpec`, and E6e -/

def encCommonPlacedRest [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest draws ∗ FromRecordCallees.lsLogOff ∗
    memRegion ((s0.sp - 0xbe0#64) - BitVec.ofNat 64 encSubStack) (encSubStack - preKeyMsgNewStack) ∗
    encSavedRegs s0.sp s0

theorem encCommonPlaced_eq_preKeyMsg [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    encCommonPlaced A ctl x draws s0 =
      A.pool ∗ stackAt (s0.sp - 0xbe0#64) preKeyMsgNewStack ∗ encCommonPlacedRest A ctl x draws s0 := by
  unfold encCommonPlaced encCommonPlacedRest
  have hstk : stackAt (s0.sp - 0xbe0#64) encSubStack =
      memRegion ((s0.sp - 0xbe0#64) - BitVec.ofNat 64 encSubStack) (encSubStack - preKeyMsgNewStack) ∗
        stackAt (s0.sp - 0xbe0#64) preKeyMsgNewStack := by
    show memRegion ((s0.sp - 0xbe0#64) - BitVec.ofNat 64 encSubStack) encSubStack = _
    rw [Encrypt.mr_cut' (s0.sp - 0xbe0#64) encSubStack preKeyMsgNewStack (encSubStack - preKeyMsgNewStack)
      preKeyMsgNewStack encSubStack rfl rfl (by decide) (by decide) (by decide)]
  rw [hstk]; sep_ac_rfl

def buildPreKeyMsgRestFramePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (draws : Nat) (sp : BitVec 64) (H_sm H_ky : SepProp) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗ buildPreKeyMsgScratchRest sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 128 ∗
    memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x930#64) 0x20 ∗
    memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xad4#64) 0xc ∗
    memRegion (sp + 0xb20#64) 0x60 ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x draws s0 ∗ H_sm ∗ H_ky

private structure BuildPreKeyMsgWords where
  msgG : SignalMessageGhost
  u0 : BitVec 64
  ik0 : BitVec 64
  ik1 : BitVec 64
  ik2 : BitVec 64
  ik3 : BitVec 64
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64
  w11 : BitVec 64
  w12 : BitVec 64
  w13 : BitVec 64
  w14 : BitVec 64
  d0 : BitVec 64
  d1 : BitVec 64
  d2 : BitVec 64
  d3 : BitVec 64
  d4 : BitVec 64
  d5 : BitVec 64
  d6 : BitVec 64
  d7 : BitVec 64
  d8 : BitVec 64
  d9 : BitVec 64
  d10 : BitVec 64
  d11 : BitVec 64
  d12 : BitVec 64
  d13 : BitVec 64
  d14 : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k2 : BitVec 64
  kd0 : BitVec 64
  kd1 : BitVec 64
  kd2 : BitVec 64
  bk0 : BitVec 64
  bk1 : BitVec 64
  bk2 : BitVec 64
  bk3 : BitVec 64
  bkd0 : BitVec 64
  bkd1 : BitVec 64
  bkd2 : BitVec 64
  bkd3 : BitVec 64
  ikd0 : BitVec 64
  ikd1 : BitVec 64
  ikd2 : BitVec 64
  ikd3 : BitVec 64
  H_sm : SepProp
  H_ky : SepProp

private theorem buildPreKeyMsg_placed_pre_unpack [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' kyBoxPtr : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (sm : SignalMessage)
    (draws : Nat) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hm : s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0 ∗ R) :
    let kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)
    ∃ b : BuildPreKeyMsgWords,
      b.w0 + 1#64 ≠ 0#64 ∧ sm.serialized.length < 2 ^ 40 ∧
      (∀ a : BitVec 64,
        (a ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) = words64At a [b.ik0, b.ik1, b.ik2, b.ik3]) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ items.baseKey.bytes.toList) = words64At a [b.bk0, b.bk1, b.bk2, b.bk3]) ∧
      (∀ dst : BitVec 64,
        words64At dst [b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7, b.w8, b.w9, b.w10, b.w11, b.w12, b.w13, b.w14] ∗ b.H_sm ⊢
          signalMessageAt A b.msgG dst sm) ∧
      (∀ dst : BitVec 64,
        words64At dst [b.k0, b.k1, b.k2] ∗ b.H_ky ⊢ optKyberAt A dst kyBoxPtr kp) ∧
      (s.mem ⊨
        ((sp ↦₆₄ b.u0) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
          ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
          words64At (sp + 0x2e0#64) [b.ik0, b.ik1, b.ik2, b.ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
          words64At (sp + 0x580#64) [b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7, b.w8, b.w9, b.w10, b.w11, b.w12, b.w13, b.w14] ∗
          words64At (sp + 0x8a0#64) [b.k0, b.k1, b.k2] ∗
          words64At (sp + 0x8b8#64) [b.d0, b.d1, b.d2, b.d3, b.d4, b.d5, b.d6, b.d7, b.d8, b.d9, b.d10, b.d11, b.d12, b.d13, b.d14] ∗
          words64At (sp + 0x950#64) [b.kd0, b.kd1, b.kd2] ∗
          words64At (sp + 0xab4#64) [b.bk0, b.bk1, b.bk2, b.bk3] ∗
          words64At (sp + 0xae0#64) [b.bkd0, b.bkd1, b.bkd2, b.bkd3] ∗
          words64At (sp + 0xb00#64) [b.ikd0, b.ikd1, b.ikd2, b.ikd3]) ∗
        (buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
          b.H_sm b.H_ky s0 ∗ R)) := by
  intro kp
  obtain ⟨ik0, ik1, ik2, ik3, hik⟩ :=
    bytes32_exists_words64At (bs := otr'.localIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨bk0, bk1, bk2, bk3, hbk⟩ :=
    bytes32_exists_words64At (bs := items.baseKey.bytes.toList) (List.Vector.toList_length _)
  dsimp only [signalMessageResultAt] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨msgG, hm⟩ := hm
  rw [otrAt_eq_ik_ver_rest A sp pqCap' pqPtr' otr' ik0 ik1 ik2 ik3 hik, hbk (sp + 0xab4#64)] at hm
  have h5f8 : memRegion (sp + 0x5f8#64) 0x2a8 =
      memRegion (sp + 0x5f8#64) 128 ∗ memRegion (sp + 0x678#64) 0x228 :=
    mr_cut_add sp 0x5f8 128 0x228 (by decide)
  have h8b8 : memRegion (sp + 0x8b8#64) 0x1fc =
      memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x930#64) 0x20 ∗
        memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0x968#64) 0x14c := by
    rw [mr_cut_add sp 0x8b8 120 0x184 (by decide),
        mr_cut_add sp 0x930 0x20 0x164 (by decide), mr_cut_add sp 0x950 24 0x14c (by decide)]
  have had4 : memRegion (sp + 0xad4#64) 0xac =
      memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
        memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60 := by
    rw [mr_cut_add sp 0xad4 0xc 0xa0 (by decide),
        mr_cut_add sp 0xae0 32 0x80 (by decide), mr_cut_add sp 0xb00 32 0x60 (by decide)]
  rw [h5f8, h8b8, had4] at hm
  let F_rest :=
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 128 ∗
      memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x930#64) 0x20 ∗
      memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xad4#64) 0xc ∗
      memRegion (sp + 0xb20#64) 0x60 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R
  have hm_scr : s.mem ⊨ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      (signalMessageAt A msgG (sp + 0x580#64) sm ∗ optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
        memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
        ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
        words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [F_rest]; sep_ac_rfl)) hm
  obtain ⟨u0, hm_scr⟩ := preKeyEncryptScratch'_unpack sp sess.localRegistrationId items.signedPreKeyId pkVal hm_scr
  let S_sc := (sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
    ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
    words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
    words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3]
  have hm_sm : s.mem ⊨ signalMessageAt A msgG (sp + 0x580#64) sm ∗
      (optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
        memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        S_sc ∗ buildPreKeyMsgScratchRest sp ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [S_sc]; sep_ac_rfl)) hm_scr
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    H_sm, hw0, hmsg_len, hm_sm, hpack_sm⟩ :=
    signalMessageAt_relocate A msgG (sp + 0x580#64) sm hm_sm
  let W_sm := words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
  have hm_ky : s.mem ⊨ optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
      (memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ S_sc ∗ H_sm ∗ buildPreKeyMsgScratchRest sp ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [W_sm]; sep_ac_rfl)) hm_sm
  obtain ⟨k0, k1, k2, H_ky, hm_ky, hpack_ky⟩ :=
    optKyberAt_relocate A (sp + 0x8a0#64) kyBoxPtr kp hm_ky
  let F_e6d := buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
    H_sm H_ky s0 ∗ R
  have hm_d : s.mem ⊨ memRegion (sp + 0x8b8#64) 120 ∗
      (memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ S_sc ∗ F_e6d) := by
    dsimp only [F_e6d]; unfold buildPreKeyMsgRestFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [F_rest]; sep_ac_rfl)) hm_ky
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, hm_d⟩ :=
    memRegion_120_exists_words15 (sp + 0x8b8#64) hm_d
  let W_d := words64At (sp + 0x8b8#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14]
  have hm_kd : s.mem ⊨ memRegion (sp + 0x950#64) 24 ∗
      (memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [W_d]; sep_ac_rfl)) hm_d
  obtain ⟨kd0, kd1, kd2, hm_kd⟩ := memRegion_24_exists_words3 (sp + 0x950#64) hm_kd
  have hm_bkd : s.mem ⊨ memRegion (sp + 0xae0#64) 32 ∗
      (memRegion (sp + 0xb00#64) 32 ∗ W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_kd
  obtain ⟨bkd0, bkd1, bkd2, bkd3, hm_bkd⟩ := memRegion_32_exists_words4 (sp + 0xae0#64) hm_bkd
  have hm_ikd : s.mem ⊨ memRegion (sp + 0xb00#64) 32 ∗
      (W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗
        words64At (sp + 0xae0#64) [bkd0, bkd1, bkd2, bkd3] ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_bkd
  obtain ⟨ikd0, ikd1, ikd2, ikd3, hm_ikd⟩ := memRegion_32_exists_words4 (sp + 0xb00#64) hm_ikd
  refine ⟨⟨msgG, u0, ik0, ik1, ik2, ik3,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    k0, k1, k2, kd0, kd1, kd2, bk0, bk1, bk2, bk3, bkd0, bkd1, bkd2, bkd3,
    ikd0, ikd1, ikd2, ikd3, H_sm, H_ky⟩, hw0, hmsg_len, hik, hbk, hpack_sm, hpack_ky, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [S_sc, W_sm, W_d, F_e6d]; sep_ac_rfl)) hm_ikd

def preKeyMsgCallFramePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (items : PendingPreKey) (pkVal : BitVec 32) (draws : Nat) (sp : BitVec 64) (s0 : State) :
    SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
    ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
    buildPreKeyMsgScratchRest sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x678#64) 0x228 ∗
    memRegion (sp + 0x8a0#64) 24 ∗ memRegion (sp + 0x930#64) 0x20 ∗
    memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
    memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗
    memRegion x.ret 248 ∗ encCommonPlacedRest A ctl x draws s0

theorem preKeyMsgNew_placed_pre_pack [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' kyBoxPtr : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32)
    (msgG : SignalMessageGhost) (sm : SignalMessage) (ik0 ik1 ik2 ik3 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (k0 k1 k2 bk0 bk1 bk2 bk3 : BitVec 64)
    (H_sm H_ky : SepProp) (draws : Nat) (sp : BitVec 64) (s0 s1 : State)
    (hsp_eq : sp = s0.sp - 0xbe0#64) (hs1_sp : s1.sp = sp)
    (hik : ∀ a : BitVec 64,
      (a ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) = words64At a [ik0, ik1, ik2, ik3])
    (hbk : ∀ a : BitVec 64,
      (a ↦ₛ items.baseKey.bytes.toList) = words64At a [bk0, bk1, bk2, bk3])
    (hsm_rel : ∀ dst : BitVec 64,
      words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H_sm ⊢
        signalMessageAt A msgG dst sm)
    (hky_rel : ∀ dst : BitVec 64,
      words64At dst [k0, k1, k2] ∗ H_ky ⊢
        optKyberAt A dst kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))) :
    ((sp ↦₆₄ (sp + 0x8b8#64)) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
      ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
      words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
      words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      words64At (sp + 0x8a0#64) [k0, k1, k2] ∗
      words64At (sp + 0x8b8#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
      words64At (sp + 0x950#64) [k0, k1, k2] ∗ words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗
      words64At (sp + 0xae0#64) [bk0, bk1, bk2, bk3] ∗
      words64At (sp + 0xb00#64) [ik0, ik1, ik2, ik3]) ∗
      buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
        H_sm H_ky s0 ⊢
      ((s1.sp ↦₆₄ (sp + 0x8b8#64)) ∗
        optKyberAt A (sp + 0x950#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) ∗
        signalMessageAt A msgG (sp + 0x8b8#64) sm ∗
        memRegion (sp + 0x580#64) 248 ∗ A.pool ∗ stackAt s1.sp preKeyMsgNewStack) ∗
      preKeyMsgCallFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k
        items pkVal draws sp s0 := by
  rw [hs1_sp]
  unfold buildPreKeyMsgRestFramePlaced preKeyMsgCallFramePlaced
  have h580 : memRegion (sp + 0x580#64) 248 =
      memRegion (sp + 0x580#64) 120 ∗ memRegion (sp + 0x5f8#64) 128 :=
    mr_cut_add sp 0x580 120 128 (by decide)
  rw [encCommonPlaced_eq_preKeyMsg A ctl x draws s0, ← hsp_eq,
      otrAt_eq_ik_ver_rest A sp pqCap' pqPtr' otr' ik0 ik1 ik2 ik3 hik,
      hbk (sp + 0xae0#64), hik (sp + 0xb00#64), h580]
  have hw_ret := words64At_entails_mr (sp + 0x580#64)
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] 120 rfl (by decide)
  have hw_8a0 := words64At_entails_mr (sp + 0x8a0#64) [k0, k1, k2] 24 rfl (by decide)
  have hw_ab4 := words64At_entails_mr (sp + 0xab4#64) [bk0, bk1, bk2, bk3] 32 rfl (by decide)
  refine Entails.trans (Entails.of_eq (show _ =
      ((words64At (sp + 0x950#64) [k0, k1, k2] ∗ H_ky) ∗
        (words64At (sp + 0x8b8#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H_sm) ∗
        words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3]) ∗
      ((sp ↦₆₄ (sp + 0x8b8#64)) ∗ words64At (sp + 0xae0#64) [bk0, bk1, bk2, bk3] ∗
        words64At (sp + 0xb00#64) [ik0, ik1, ik2, ik3] ∗ memRegion (sp + 0x5f8#64) 128 ∗
        A.pool ∗ stackAt sp preKeyMsgNewStack ∗
        sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        (words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
          ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗ otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗ ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗
        ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x678#64) 0x228 ∗
        memRegion (sp + 0x930#64) 0x20 ∗ memRegion (sp + 0x968#64) 0x14c ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗
        memRegion x.ret 248 ∗ encCommonPlacedRest A ctl x draws s0) by sep_ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left
      (sepConj_mono (hky_rel (sp + 0x950#64))
        (sepConj_mono (hsm_rel (sp + 0x8b8#64))
          (sepConj_mono hw_ret (sepConj_mono hw_8a0 hw_ab4))))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

def cmCopyRestFramePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (draws : Nat) (sp : BitVec 64) (H_psm : SepProp) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x678#64) 0x2b8 ∗
    memRegion (sp + 0x948#64) 0x238 ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x draws s0 ∗ H_psm

private structure CmCopyWords where
  psmG : PreKeyMsgGhost
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64
  w11 : BitVec 64
  w12 : BitVec 64
  w13 : BitVec 64
  w14 : BitVec 64
  w15 : BitVec 64
  w16 : BitVec 64
  w17 : BitVec 64
  w18 : BitVec 64
  w19 : BitVec 64
  w20 : BitVec 64
  w21 : BitVec 64
  w22 : BitVec 64
  w23 : BitVec 64
  w24 : BitVec 64
  w25 : BitVec 64
  w26 : BitVec 64
  w27 : BitVec 64
  w28 : BitVec 64
  w29 : BitVec 64
  w30 : BitVec 64
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  d0 : BitVec 64
  d1 : BitVec 64
  d2 : BitVec 64
  d3 : BitVec 64
  d4 : BitVec 64
  d5 : BitVec 64
  d6 : BitVec 64
  d7 : BitVec 64
  d8 : BitVec 64
  d9 : BitVec 64
  d10 : BitVec 64
  d11 : BitVec 64
  d12 : BitVec 64
  d13 : BitVec 64
  d14 : BitVec 64
  d15 : BitVec 64
  d16 : BitVec 64
  d17 : BitVec 64
  d18 : BitVec 64
  d19 : BitVec 64
  d20 : BitVec 64
  d21 : BitVec 64
  d22 : BitVec 64
  d23 : BitVec 64
  d24 : BitVec 64
  d25 : BitVec 64
  d26 : BitVec 64
  d27 : BitVec 64
  d28 : BitVec 64
  d29 : BitVec 64
  d30 : BitVec 64
  H_psm : SepProp

private theorem cmCopy_placed_pre_unpack [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32)
    (psm : PreKeySignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hm2 : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) psm) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k
        items pkVal draws sp s0 ∗ R) :
    ∃ u : CmCopyWords,
      u.w0 + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [u.w0, u.w1, u.w2, u.w3, u.w4, u.w5, u.w6, u.w7, u.w8, u.w9, u.w10, u.w11, u.w12, u.w13, u.w14,
          u.w15, u.w16, u.w17, u.w18, u.w19, u.w20, u.w21, u.w22, u.w23, u.w24, u.w25, u.w26, u.w27, u.w28, u.w29, u.w30] ∗
          u.H_psm ⊢ preKeyMsgAt A u.psmG dst psm) ∧
      (s2.mem ⊨
        (words64At (sp + 0x580#64) [u.w0, u.w1, u.w2, u.w3, u.w4, u.w5, u.w6, u.w7, u.w8, u.w9, u.w10, u.w11, u.w12, u.w13,
            u.w14, u.w15, u.w16, u.w17, u.w18, u.w19, u.w20, u.w21, u.w22, u.w23, u.w24, u.w25, u.w26, u.w27, u.w28, u.w29, u.w30] ∗
          words64At (sp + 0x930#64) [u.v0, u.v1, u.v2] ∗
          words64At (sp + 0x370#64) [u.d0, u.d1, u.d2, u.d3, u.d4, u.d5, u.d6, u.d7, u.d8, u.d9, u.d10, u.d11, u.d12, u.d13,
            u.d14, u.d15, u.d16, u.d17, u.d18, u.d19, u.d20, u.d21, u.d22, u.d23, u.d24, u.d25, u.d26, u.d27, u.d28, u.d29, u.d30]) ∗
        (cmCopyRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
          u.H_psm s0 ∗ R)) := by
  unfold preKeyMsgCallFramePlaced at hm2
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨psmG, hm2⟩ := hm2
  have hcm := preKeyEncryptScratch'_to_cmScratch sp (sp + 0x8b8#64)
    sess.localRegistrationId items.signedPreKeyId pkVal
  have hbk_ae0 := bytes32_entails_memRegion (sp + 0xae0#64) items.baseKey.bytes.toList
    (List.Vector.toList_length _)
  have hik_b00 := bytes32_entails_memRegion (sp + 0xb00#64)
    otr'.localIdentityKey.publicKey.bytes.toList (List.Vector.toList_length _)
  let F_core :=
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗ memRegion x.ret 248 ∗ R
  have hm2_sub : s2.mem ⊨
      (((sp ↦₆₄ (sp + 0x8b8#64)) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
        ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp) ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList)) ∗
      (preKeyMsgAt A psmG (sp + 0x580#64) psm ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x8b8#64) 120 ∗
        (A.pool ∗ stackAt sp preKeyMsgNewStack ∗ encCommonPlacedRest A ctl x draws s0) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗ memRegion (sp + 0x678#64) 0x228 ∗
        memRegion (sp + 0x8a0#64) 24 ∗ memRegion (sp + 0x930#64) 0x20 ∗
        memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗ F_core) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [F_core]; sep_ac_rfl)) hm2
  have hm2_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hcm (sepConj_mono hbk_ae0 hik_b00))) hm2_sub
  have h930 : memRegion (sp + 0x930#64) 0x20 =
      memRegion (sp + 0x930#64) 24 ∗ memRegion (sp + 0x948#64) 8 :=
    mr_cut_add sp 0x930 24 8 (by decide)
  have henc_psm : A.pool ∗ stackAt sp preKeyMsgNewStack ∗ encCommonPlacedRest A ctl x draws s0 =
      encCommonPlaced A ctl x draws s0 := by
    rw [hsp_eq, ← encCommonPlaced_eq_preKeyMsg A ctl x draws s0]
  rw [henc_psm, h930] at hm2_mono
  have hmerge_678 :
      memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗
        memRegion (sp + 0x8b8#64) 120 = memRegion (sp + 0x678#64) 0x2b8 := by
    rw [mr_cut_add sp 0x678 0x228 0x90 (by decide), mr_cut_add sp 0x8a0 24 120 (by decide)]
  have hmerge_948 :
      memRegion (sp + 0x948#64) 8 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
        memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60 =
      memRegion (sp + 0x948#64) 0x238 := by
    rw [mr_cut_add sp 0x948 8 0x230 (by decide), mr_cut_add sp 0x950 24 0x218 (by decide),
        mr_cut_add sp 0x968 0x14c 0xcc (by decide), mr_cut_add sp 0xab4 32 0xac (by decide),
        mr_cut_add sp 0xad4 0xc 0xa0 (by decide), mr_cut_add sp 0xae0 32 0x80 (by decide),
        mr_cut_add sp 0xb00 32 0x60 (by decide)]
  have hm2_merged : s2.mem ⊨
      preKeyMsgAt A psmG (sp + 0x580#64) psm ∗
      (memRegion (sp + 0x930#64) 24 ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        (memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗
          memRegion (sp + 0x8b8#64) 120) ∗
        (memRegion (sp + 0x948#64) 8 ∗ memRegion (sp + 0x950#64) 24 ∗
          memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
          memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
          memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60) ∗
        cmScratch sp ∗ encCommonPlaced A ctl x draws s0 ∗ F_core) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm2_mono
  rw [hmerge_678, hmerge_948] at hm2_merged
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    H_psm, hw0, hm2_psm, hpsm_rel⟩ :=
    preKeyMsgAt_relocate A psmG (sp + 0x580#64) psm hm2_merged
  let W_psm := words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]
  let F_e6e := cmCopyRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
    H_psm s0 ∗ R
  have hm2_930 : s2.mem ⊨ memRegion (sp + 0x930#64) 24 ∗
      (memRegion (sp + 0x370#64) 0xf8 ∗ W_psm ∗ F_e6e) := by
    dsimp only [W_psm, F_e6e]; unfold cmCopyRestFramePlaced
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [F_core]; sep_ac_rfl)) hm2_psm
  obtain ⟨v0, v1, v2, hm2_930⟩ := memRegion_24_exists_words3 (sp + 0x930#64) hm2_930
  have hm2_370 : s2.mem ⊨ memRegion (sp + 0x370#64) 248 ∗
      (W_psm ∗ words64At (sp + 0x930#64) [v0, v1, v2] ∗ F_e6e) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm2_930
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, hm2_370⟩ :=
    memRegion_248_exists_words31 (sp + 0x370#64) hm2_370
  exact ⟨⟨psmG, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30,
    H_psm⟩, hw0, hpsm_rel, Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [W_psm, F_e6e]; sep_ac_rfl)) hm2_370⟩

theorem cmCopy_placed_post_pack [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (psmG : PreKeyMsgGhost) (psm : PreKeySignalMessage)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20
      w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : BitVec 64)
    (H_psm : SepProp) (draws : Nat) (sp : BitVec 64) (s0 : State)
    (hpsm_rel : ∀ dst : BitVec 64,
      words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
        w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        H_psm ⊢ preKeyMsgAt A psmG dst psm) :
    (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
      words64At (sp + 0x930#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]) ∗
      cmCopyRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
        H_psm s0 ⊢
    cmSlots A sp sess taken otr' pqCap' pqPtr' k (.preKeySignalMessage psm) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0 := by
  unfold cmCopyRestFramePlaced cmSlots takenSlots
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ⊢
        ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) :=
    Entails.sepExists_right ⟨prevCap, prevPtr, some G⟩ (Entails.refl _)
  have hcm_msg :
      words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        H_psm ⊢ apiEncResultAt A (sp + 0x370#64) (.ok (.preKeySignalMessage psm)) :=
    Entails.sepExists_right psmG (hpsm_rel (sp + 0x370#64))
  have hw_580 := words64At_entails_mr (sp + 0x580#64)
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
      w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]
    0xf8 rfl (by decide)
  have hw_930 := words64At_entails_mr (sp + 0x930#64) [w4, w5, w6] 24 rfl (by decide)
  have hmerge_46a :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 0xf8 ∗
        memRegion (sp + 0x678#64) 0x2b8 ∗ memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x948#64) 0x238 := by
    rw [mr_cut_add sp 0x46a 0x116 0x600 (by decide), mr_cut_add sp 0x580 0xf8 0x508 (by decide),
        mr_cut_add sp 0x678 0x2b8 0x250 (by decide), mr_cut_add sp 0x930 24 0x238 (by decide)]
  rw [hmerge_46a]
  refine Entails.trans (Entails.of_eq (show _ =
      (sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        (words64At (sp + 0x370#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
          H_psm) ∗
        words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        words64At (sp + 0x930#64) [w4, w5, w6]) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x678#64) 0x2b8 ∗ memRegion (sp + 0x948#64) 0x238 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0) by sep_ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono hrec_ex (sepConj_mono hcm_msg (sepConj_mono hw_580 hw_930)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. `segPreKey_buildMessage_placed_ok` (`+0x8c8..+0xa70` → `CmStateVPlaced`) -/

set_option linter.unusedVariables false in
theorem segPreKey_buildMessage_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (sm : SignalMessage)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hok : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm)
    (hret : PreKeyEncryptRetStatePlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          R s0 sf) := by
  rcases hret with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx22, hx24, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp_eq : sp = s0.sp - 0xbe0#64 := rfl
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have hok' : res.1 = .ok sm := hok
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  let R' := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R
  change s.mem ⊨
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
    signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
    optKyberAt A (sp + 0x8a0#64) kyBoxPtr
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
    memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x (S.draws otr.pqrState x.rest) s0 ∗ R' at hm
  rw [hok'] at hm
  obtain ⟨b, hw0, hmsg_len, hik, hbk, hsm_rel, hky_rel, hm_e6d⟩ :=
    buildPreKeyMsg_placed_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
      items pkVal sm (S.draws otr.pqrState x.rest) sp R' s0 s hm
  refine Pf.SegFrom.SegExitPlaced.of_sepWP hm_e6d
    (buildPreKeyMsg_placed_step_bl hs_pc hrun hsp hal hx22 hx25 hx26 hx29' hw0) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8,
      hs1_x19, hs1_x20, hs1_x22, _, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  let call : PreKeyMsgNewCall :=
    { ret := sp + 0x580#64, ver := res.2.sessionVersion, regId := sess.localRegistrationId,
      preKeyId := items.preKeyId, spk := items.signedPreKeyId, kyA := sp + 0x950#64,
      kyPtr := kyBoxPtr,
      kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload),
      bkA := sp + 0xae0#64, baseKey := items.baseKey, ikA := sp + 0xb00#64,
      ik := res.2.localIdentityKey, msgA := sp + 0x8b8#64, msgG := b.msgG, msg := sm }
  have hm1_sub : s1.mem ⊨
      (Pm1 ∗ buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp b.H_sm b.H_ky s0) ∗ R' :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm1_pack := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm1)
        (preKeyMsgNew_placed_pre_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
          items pkVal b.msgG sm b.ik0 b.ik1 b.ik2 b.ik3
          b.w0 b.w1 b.w2 b.w3 b.w4 b.w5 b.w6 b.w7 b.w8 b.w9 b.w10 b.w11 b.w12 b.w13 b.w14
          b.k0 b.k1 b.k2 b.bk0 b.bk1 b.bk2 b.bk3 b.H_sm b.H_ky (S.draws otr.pqrState x.rest) sp s0 s1
          hsp_eq hs1_sp hik hbk hsm_rel hky_rel)))
    hm1_sub
  have hcall_len : call.model.serialized.length < 2 ^ 42 :=
    call.model_serialized_length_lt hmsg_len
      (kyber_ciphertext_length_lt (env.scopeIn r hscope) hcur)
  have hcall_pure :
      (s1.readReg64 .x0).setWidth 8 = call.ver ∧ (s1.readReg64 .x1).setWidth 32 = call.regId ∧
      (s1.readReg64 .x2).setWidth 32 = (if call.preKeyId.isSome then 1#32 else 0#32) ∧
      (∀ v, call.preKeyId = some v → (s1.readReg64 .x3).setWidth 32 = v) ∧
      (s1.readReg64 .x4).setWidth 32 = call.spk ∧ s1.readReg64 .x5 = call.kyA ∧
      s1.readReg64 .x6 = call.bkA ∧ s1.readReg64 .x7 = call.ikA ∧
      s1.readReg64 .x8 = call.ret ∧ call.model.serialized.length < 2 ^ 42 :=
    ⟨hs1_x0, hs1_x1, hs1_x2.trans hx24, fun v hv => hs1_x3.trans (hpkVal v hv),
      hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8, hcall_len⟩
  have hm1_pre : s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec A)).pre call s1 ∗
      (preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R') := by
    change s1.mem ⊨ ((preKeyMsgNewSpec A).pre call s1 ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝) ∗ _
    rw [sepConj_comm ((preKeyMsgNewSpec A).pre call s1), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcrl1, ?_⟩
    unfold preKeyMsgNewSpec
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcall_pure, Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1_pack⟩
  clear hw0 hik hbk hsm_rel hky_rel hm_e6d Pm1 hm1 hPm1 hm1_sub hm1_pack hcall_len hcall_pure
  have hpref01 : s0.trace <+: s1.trace := by
    rw [hs1_tr, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩
  refine Pf.SegFrom.SegExitPlaced.call env.callees.psmNew call hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec A)).onExit call code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      have hp : sf.mem ⊨ (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗
          (preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
            items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ encStoreExtraPlaced kit st0 ikit ist0 x s0) ∗ R := by
        dsimp only [StoreKit.withLsRoCl, preKeyMsgNewSpec, R'] at hpost
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
      exact onPanic_of_alloc_placed hpref01 hp)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  rcases hcs12 with ⟨hx19_2, hx20_2, _, hx22_2, _, _, hx25_2, hx26_2, _, hx28_2, hx29_2, hvregs_2⟩
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x22 : s2.readReg64 .x22 = sp + 0x8b8#64 := hx22_2.trans (hs1_x22.trans hx22)
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := hx25_2.trans (hs1_x25.trans hx25)
  unfold StoreKit.withLsRoCl preKeyMsgNewSpec at hpost2
  dsimp only [call] at hpost2
  rw [hs1_sp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost2
  rcases hpost2 with ⟨hcrl2, hs2_tr, hm2⟩
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  have hm2' : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) call.model) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ res.2.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R' :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm2
  clear hm2 hm1_pre
  obtain ⟨u, hpw0, hpsm_rel, hm2_e6e⟩ :=
    cmCopy_placed_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
      items pkVal call.model (S.draws otr.pqrState x.rest) sp R' s0 s2 hsp_eq hm2'
  refine Pf.SegFrom.SegExitPlaced.of_sepWP hm2_e6e
    (cmCopy_placed_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x22 hs2_x25 hpw0) ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_sub : s3.mem ⊨
      (Pm3 ∗ cmCopyRestFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp u.H_psm s0) ∗ R' :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm3
  have hm3_cm := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm3)
        (cmCopy_placed_post_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
          u.psmG call.model
          u.w0 u.w1 u.w2 u.w3 u.w4 u.w5 u.w6 u.w7 u.w8 u.w9 u.w10 u.w11 u.w12 u.w13 u.w14
          u.w15 u.w16 u.w17 u.w18 u.w19 u.w20 u.w21 u.w22 u.w23 u.w24 u.w25 u.w26 u.w27 u.w28 u.w29 u.w30
          u.H_psm (S.draws otr.pqrState x.rest) sp s0 hpsm_rel)))
    hm3_sub
  clear u hpw0 hpsm_rel hm2' hm2_e6e Pm3 hm3 hPm3 hm3_sub
  have hsteps15 := stepsThroughEncrypt_of_preKey_ok_placed hcur hscope hfrom hrem hpk hts hexp hlt hok'
  refine Pf.SegFrom.SegExitPlaced.next ⟨.preKeySignalMessage call.model, res.2, pqCap', pqPtr',
    hsteps15, ?_⟩
  refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al,
      hs3_x29.trans (hx29_2.trans (hs1_x29.trans hx29)),
      hs3_x19.trans (hx19_2.trans (hs1_x19.trans hx19)),
      hcrl3,
      hs3_vregs.trans (hvregs_2.trans (hs1_vregs.trans hvregs))⟩,
    hs3_tr.trans hs2_tr',
    ⟨hs3_x20.trans (hx20_2.trans (hs1_x20.trans hx20)),
      hs3_x25.trans hs2_x25,
      hs3_x26.trans (hx26_2.trans (hs1_x26.trans hx26)),
      hs3_x28.trans (hx28_2.trans (hs1_x28.trans hx28))⟩,
    hpt, hrest, hloc, hnow, hstk,
    Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [sp, call, PreKeyMsgNewCall.model, R']; sep_ac_rfl)) hm3_cm⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
