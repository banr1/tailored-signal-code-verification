/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncryptPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncrypt
public import ProofLib.RegChain
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale

/-!
# Budget-Threaded Relocatable `segPreKey` `OTR::encrypt` Call and Error Branch (`+0x8b4..+0x8ec`)

Proves `segPreKey_encrypt_call_placed_ok` and `segPreKey_encrypt_err_placed_ok` on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncryptPlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey hiding
  segPreKey_encrypt_call_placed_ok segPreKey_encrypt_err_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailSymPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Budget Pre/Post Helpers for `segPreKey_encrypt_call_placed_ok` (`+0x8b4..+0x8c8`) -/

private theorem otrEnc_budget_pre_frame [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop}
    (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr)))
    (hQ : Q otr.pqrState)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x580#64)
    (hx1 : s1.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s1.readReg64 .x2 = x.ptA)
    (hx3 : s1.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hptlen : x.ptext.length < 2 ^ 32)
    (hx4 : s1.readReg64 .x4 = x.locA)
    (hlocA : x.locA ≠ 0#64)
    (hx5 : s1.readReg64 .x5 = x.remA)
    (hPm : Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
      ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA))
    (hm : s1.mem ⊨ Pm ∗
      ((otrAt (A.atState lim st s1) (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt (A.atState lim st s1) x.loc x.locA ∗
        protocolAddressAt (A.atState lim st s1) x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ (A.atState lim st s1).pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt (A.atState lim st s1) x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl uuidTryParse S sendEnv)).pre
        (preKeyOtrGhost x sp pqCap pqPtr otr, st) s1 ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) := by
  have hm_pl := otrEnc_placed_pre_frame (Q := Q) ss_vt id_vt C (A.atState lim st s1) ctl S
    x prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R Pm s0 s1
    hQ hcrl1 hsp1 hx0 hx1 hx2 hx3 hptlen hx4 hlocA hx5 hPm hm
  rw [show preKeyEncryptCallRestFrame ss_vt id_vt (A.atState lim st s1) =
      preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc from rfl] at hm_pl
  unfold StoreKit.withLsRoCl at hm_pl
  unfold StoreKit.withLsRoCl otrEncryptBudgetSpecQ
  dsimp only at hm_pl ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfit, Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm_pl⟩

private theorem otrEnc_budget_post_unpack [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop}
    (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨ ((StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl uuidTryParse S sendEnv)).post
        (preKeyOtrGhost x sp pqCap pqPtr otr, st) s1 s2 ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0)) ∗ R) :
    let res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
    ∃ (evs : List AllocEvent) (pqCap' pqPtr' : BitVec 64),
      OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr) evs ∧
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧
      res.1 ≠ .error .panic ∧ s2.trace = s1.trace ∧
      (s2.mem ⊨
        sessionRecordAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗
        preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
        encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt (A.atState lim (M.stepEvents evs st) s2) (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
        memRegion (sp + 0x5f8#64) 0x2a8 ∗
        optKyberAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x8a0#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗
        ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
        memRegion (sp + 0xad4#64) 0xac ∗
        memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim (M.stepEvents evs st) s2) ctl x (S.draws otr.pqrState x.rest) s0 ∗ R) := by
  intro res
  unfold StoreKit.withLsRoCl otrEncryptBudgetSpecQ otrEncryptBudgetSpec at hpost
  dsimp only at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨evs, hpost⟩ := hpost
  let A' := A.atState lim (M.stepEvents evs st) s2
  have h0 : s2.mem ⊨ ⌜OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr) evs⌝ ∗
      (((StoreKit.withLsRoCl lsmpl (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ Q C A' ctl uuidTryParse S)).post
          (preKeyOtrGhost x sp pqCap pqPtr otr) s1 s2 ∗
        ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
          ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
          ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
          preKeyEncryptCallRestFrame ss_vt id_vt A' x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0)) ∗ R) := by
    unfold StoreKit.withLsRoCl CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ
    dsimp only
    rw [show preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc =
        preKeyEncryptCallRestFrame ss_vt id_vt A' from rfl] at hpost
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h0
  rcases h0 with ⟨hevs, hpost_pl⟩
  obtain ⟨pqCap', pqPtr', hcrl2, hne, htr, hmem⟩ :=
    otrEnc_placed_post_unpack (Q := Q) ss_vt id_vt C A' ctl S
      x prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R s0 s1 s2
      hsp0 hsp1 hpost_pl
  exact ⟨evs, pqCap', pqPtr', hevs, hcrl2, hne, htr, hmem⟩

/-! ## 2. `segPreKey_encrypt_call_placed_ok` (`+0x8b4..+0x8c8`) -/

theorem segPreKey_encrypt_call_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState'Budget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun s' => ∃ st',
        PreKeyEncryptRetStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st' r sess otr taken pqCap pqPtr k items R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hst with ⟨hbud, prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr,
    hts, hexp, hlt, hpkVal, hpc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr,
    hx20, hx22, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  have hQ : Q otr.pqrState := env.toEncEnvBudget.q_otr hcur hscope hfrom
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr)) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud.1
  have hm_unp := preKeyEncrypt_placed_mem_unpack kit.ss_vt ikit.id_vt (A.atState lim st s) ctl
    x prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R s0 hsp0 hrestlen hmem
  refine SegExitBudget.of_sepWP hm_unp (preKeyEncrypt_placed_step_bl_vm hpc hrun hsp hal) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5,
      hs1_x19, hs1_x20, hs1_x22, hs1_x24, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  rw [← A.atState_eq_of_vmPreserved lim st hvm01] at hm1
  have hm1_pre := otrEnc_budget_pre_frame (Q := Q) kit.ss_vt ikit.id_vt C A lim ctl S sendEnv
    x st prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R Pm1 s0 s1
    hfit hQ hcrl1 hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_x3 hptlen hs1_x4 hlocA hs1_x5 hPm1 hm1
  refine SegExitBudget.call env.callees.otrEnc (preKeyOtrGhost x sp pqCap pqPtr otr, st)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl uuidTryParse S sendEnv)).onExit
            (preKeyOtrGhost x sp pqCap pqPtr otr, st) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      change sf.mem ⊨ ((⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
          S.sendPanics otr.pqrState x.rest) ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ _) ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) at hpost
      rw [sepConj_assoc] at hpost
      exact onPanicBudget_absorb_extra
        (onPanic_of_otrEnc_budget (hs1_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt hpost))
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x24 : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    rw [hcs12.2.2.2.2.2.1, hs1_x24]; exact hx24
  obtain ⟨evs, pqCap', pqPtr', hevs, hcrl2, hne2, hs2_tr, hm2⟩ :=
    otrEnc_budget_post_unpack (Q := Q) kit.ss_vt ikit.id_vt C A lim ctl S sendEnv
      x st prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R s0 s1 s2
      hsp0 hs1_sp hpost2
  exact SegExitBudget.next ⟨M.stepEvents evs st, hbud.advance hevs,
    prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, hne2, hs2_pc,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hcrl2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩,
    hs2_tr.trans (hs1_tr.trans htr),
    by reg_chain, by reg_chain, hs2_x24, by reg_chain, by reg_chain, by reg_chain,
    hptlen, hrestlen, hlocA, hnow, hstack, hm2⟩

/-! ## 3. `segPreKey_encrypt_err_placed_ok` (`+0x8c8..+0x8ec` → `env.tailPreKeyEncryptErr`) -/

theorem segPreKey_encrypt_err_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (e : SignalProtocolError)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (herr : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .error e)
    (hret : PreKeyEncryptRetStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hret with ⟨hbud, prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, _hpkVal, hnp, hpc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr,
    _hx20, _hx22, _hx24, hx25, hx26, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  have hbud_err : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      FreeOnlyEvs :=
    hbud.narrow fun _ => Or.inl
  set sp := s0.sp - 0xbe0#64
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have herr' : res.1 = .error e := herr
  rw [herr'] at hnp hmem
  have he_np : e ≠ .panic := fun h => hnp (congrArg Except.error h)
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl he_np
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, ← sp_sub_60_eq_add_b80 s0.sp]
  obtain ⟨w0, w1, w2, w3, w4, w5, v0, v1, v2, H, hst, hm_err⟩ :=
    preKeyEncrypt_placed_err_unpack kit.ss_vt ikit.id_vt (A.atState lim st s) ctl
      x prevCap prevPtr G sess taken res.2 pqCap' pqPtr' k items pkVal kyBoxPtr e
      (S.draws otr.pqrState x.rest) sp R s0 s hnp hmem
  refine SegExitBudget.of_sepWP hm_err (preKeyEncrypt_placed_step_err_vm hpc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hvm23, hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 := hcrl.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  rw [← A.atState_eq_of_vmPreserved lim st hvm23] at hm3
  have hm3_tail := preKeyEncrypt_placed_err_tail_mem kit.ss_vt ikit.id_vt (A.atState lim st s3) ctl
    x prevCap prevPtr G sess taken res.2 pqCap' pqPtr' k items pkVal kyBoxPtr w0 w1 w2 w3 w4 w5
    (S.draws otr.pqrState x.rest) sp H R Pm3 s0 s3 hPm3 hm3
  have htm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (.protocol e)) s0 s3 := by
    rw [← hprot]
    exact tailModel_of_otr_err_placed (hs3_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt herr
  have hexec := execOk_of_preKeyOtrGhost_error herr
  have hmod_err : x.model C S uuidTryParse (preKeyErrAnswers r) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    rw [EncryptGhost.model, messageEncrypt_eq_flat]
    simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
      hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec]
  have hfinal :
      kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
    rw [congrArg Prod.snd hmod_err]; rfl
  have hidfinal :
      ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
    rw [congrArg Prod.snd hmod_err]; rfl
  have hdraws := draws_of_not_stale (S := S) hcur hfrom hrem hpk hts hexp hlt
  have hst_rep : SpeStaged A.repAlloc x.ret (.protocol e) [w0, w1, w2, w3, w4, w5] H := hst
  refine env.tailPreKeyEncryptErr x st_init st R0 s0 s3
    (preKeyErrAnswers r) (.protocol e)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
    (some (pqCap', pqPtr', res.2)) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
    htm hst_rep ⟨hbud_err, hs3_pc,
      ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hcrl3, hs3_vregs.trans hvregs⟩,
      ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstack, ?_⟩
  rw [preKey_encTail_mem_retag_eq (A' := A.atState lim st s3)
    kit st0 ikit ist0 C ctl S x (preKeyErrAnswers r) _ R0 s0]
  rw [hdraws, hfinal, hidfinal,
      show dropRecordSlots A.repAlloc = dropRecordSlots (A.atState lim st s3) from rfl,
      show optKyberAt A.repAlloc = optKyberAt (A.atState lim st s3) from rfl]
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [R])) hm3_tail

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncryptPlacedBudget
