/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `segSignal` Items Check (`Key` → `Ack`)

Defines `SegSignalAckStateVPlaced` at `+0x348` and proves `segSignal_placed_to_ack` on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnackPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- **Ack** (`+0x348`) under `[LibsignalPlacement]`: the items getter returned `None` (tag 2) at
`segSignal`. -/
def SegSignalAckStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
    (FromKeyEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k) ∧
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧ sess.pendingPreKey = none ∧
  s.pc = encEntryPlaced + 0x348#64 ∧ encMidMetaPlaced x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x23 = sp + 0x58#64 ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = sp + 0xc0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    (takenSlots (A.atState lim st s) sp sess taken ∗
      otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0))

private def segSignalUnackRestFramePlaced [LibsignalPlacement] {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_keyState_mem_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 : State)
    {m : Memory} (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ g G,
      m ⊨ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp unackItemsStack ∗
          segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗
        R) := by
  unfold takenSlots encCommonPlaced at hm
  rw [hsp0] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨g, hm⟩ := hm
  have hm_rec := Satisfies.mono (sepConj_mono_left (segSignal_rec_unpack A sp g sess taken)) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm_rec
  obtain ⟨G, hm_rec⟩ := hm_rec
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x5a8 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 88 0x5a8 (by decide)]
  rw [h46a, stackAt_sub sp encSubStack unackItemsStack] at hm_rec
  refine ⟨g, G, ?_⟩
  unfold segSignalUnackRestFramePlaced
  exact Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm_rec

private theorem segSignal_placed_unack_pre_frame [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm : Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))
    (hm : s1.mem ⊨ Pm ∗
      ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp unackItemsStack ∗
        segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗
      R)) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)).pre
        ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 ∗
      ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗
      R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  dsimp only [StoreKit.withLsRoCl, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec]
  rw [hsp1]
  have hpure : (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ : SepProp) ∗
      ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp unackItemsStack ∗
          segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗
        R)) =
      (((⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp unackItemsStack) ∗
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝) ∗
        ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗
        R)) := by
    sep_ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hcrl1, ⟨hx0, hx8⟩, hm'⟩

private theorem segSignal_placed_unack_panic_absurd [LibsignalPlacement] (A : RustAlloc)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (sp : BitVec 64) (F R : SepProp) (s1 sf : State)
    (hpk : sess.pendingPreKey = none)
    (hpost : sf.mem ⊨ ((StoreKit.withLsRoCl lsmpl (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)).onPanic
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 sf ∗ F) ∗ R) :
    False := by
  unfold StoreKit.withLsRoCl CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec at hpost
  dsimp only at hpost
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost.1.1 with ⟨items, hsome, _⟩
  change sess.pendingPreKey = some items at hsome
  rw [hpk] at hsome
  cases hsome

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_unack_post_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpk : sess.pendingPreKey = none)
    (hpost : s2.mem ⊨ ((StoreKit.withLsRoCl lsmpl (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)).post
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 s2 ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0)) ∗
      R) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧
    s2.trace = s1.trace ∧
    (s2.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) := by
  have hout : unackOutAt (sp + 0x580#64) G.kyber
      ({ sess with state := taken }).pendingKyberPreKey
      ({ sess with state := taken }).pendingPreKey =
      ((sp + 0x580#64) ↦₃₂ 2#32) ∗ memRegion (sp + 0x584#64) 84 := by
    change unackOutAt (sp + 0x580#64) G.kyber sess.pendingKyberPreKey sess.pendingPreKey = _
    rw [hpk]
    unfold unackOutAt
    have h584 : (sp + 0x580#64) + 4#64 = sp + 0x584#64 := by bv_omega
    rw [h584]
  dsimp only [StoreKit.withLsRoCl, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec] at hpost
  rw [hsp1, hout] at hpost
  simp only [sepConj_assoc] at hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨hcrl2, htr, hmem⟩
  refine ⟨hcrl2, htr, ?_⟩
  unfold segSignalUnackRestFramePlaced at hmem
  have hrec :
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.trans (segSignal_rec_pack A sp g.prevCap g.prevPtr G sess taken)
      (Entails.sepExists_right ⟨g.prevCap, g.prevPtr, some G⟩ (Entails.refl _))
  have hmem_rearr : s2.mem ⊨
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
        stackAt sp unackItemsStack) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack unackItemsStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold takenSlots encCommonPlaced
  rw [hsp0]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem_fold

/-- **Key → Ack** (`+0x344 bl` `lsmpl.base 36`) under `[LibsignalPlacement]`:
`unackItemsPlacedSpec` with `pendingPreKey = none`. -/
theorem segSignal_placed_to_ack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun s' => SegSignalAckStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st
        r sess otr taken pqCap pqPtr k R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hbud, hcur, hsc, hfrom, hrem, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, _hx22, hx23, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  dsimp only [retagSessionStore, retagIdentityStore] at hsc htr hm
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  obtain ⟨g, G, hm_unp⟩ :=
    segSignal_placed_keyState_mem_unpack (A.atState lim st s) ctl x sess otr taken pqCap pqPtr k sp R s0 hsp0 hm
  refine SegExitBudget.of_sepWP hm_unp (segSignal_placed_step_bl hs_pc hrun hsp hal) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x23, hs1_x25, hs1_x26, hs1_x27,
      hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := segSignal_placed_unack_pre_frame (A.atState lim st s) ctl x g G sess otr taken pqCap pqPtr k sp R Pm1 s0 s1
    hcrl1 hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegExitBudget.call env.callees.unack
    ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (unackItemsBudgetSpec A.repAlloc)).onExit
        ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      (segSignal_placed_unack_panic_absurd (A.atState lim st s) G sess taken sp _ R s1 sf hpk hpost).elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_al : s2.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hpost_eq : ∀ xc s1' s2',
      (StoreKit.withLsRoCl lsmpl (unackItemsBudgetSpec A.repAlloc)).post xc s1' s2' =
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2'.mem⌝ ∗
          (⌜VmPreserved s1' s2'⌝ ∗ (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec (A.atState lim st s)).post xc s1' s2') :=
    fun _ _ _ => rfl
  rw [hpost_eq] at hpost2
  have hpost2_vm : s2.mem ⊨ ⌜VmPreserved s1 s2⌝ ∗
      (((StoreKit.withLsRoCl lsmpl (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec (A.atState lim st s))).post
          ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 s2 ∗
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          segSignalUnackRestFramePlaced (ss_vt := kit.ss_vt) (id_vt := ikit.id_vt)
            (A.atState lim st s) ctl x g otr pqCap pqPtr k sp s0)) ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost2
  rw [satisfies_pure_sepConj] at hpost2_vm
  rcases hpost2_vm with ⟨hvm12, hpost2'⟩
  have ⟨hcrl2, hs2_tr, hm2⟩ := segSignal_placed_unack_post_pack (A.atState lim st s) ctl x g G sess otr taken pqCap pqPtr k sp R
    s0 s1 s2 hsp0 hs1_sp hpk hpost2'
  rw [(A.atState_eq_of_vmPreserved lim st (hvm01.trans hvm12)).symm] at hm2
  refine SegExitBudget.next ⟨hbud, hcur, hsc, hfrom, hrem, hpk, hs2_pc,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hcrl2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    hpt, hrest, hloc, hnow, hstk, hm2⟩

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnackPlacedBudget
