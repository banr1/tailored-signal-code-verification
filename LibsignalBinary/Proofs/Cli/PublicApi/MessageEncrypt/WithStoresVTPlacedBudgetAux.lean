/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux2
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncryptPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessagePlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncrypt
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.RegChain
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Aux): `SegPreKey` Tail (`+0x8b4..+0xa70`)

Proves the `SegPreKey` tail lemmas (`h45_segPreKey_encrypt_call_placed_ok`,
`h45_segPreKey_encrypt_err_placed_ok`, `h45_segPreKey_buildMessage_placed_ok`,
`h45_segPreKey_tail_placed_ok`) and assembles `h45_segPreKey_placed_okVT` on Block `464`
(`lsProg_464 H`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailSymPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1 (
  h45_envTBudget_of_placed h45_envTFullBudget_of_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux2 (
  h45_segPreKey_unackItems_to_dur_placed_ok h45_segPreKey_staleness_to_add_placed_ok
  h45_segPreKey_stale_placed_ok h45_segPreKey_regId_kyber_placed_ok
)

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey hiding
  segPreKey_encrypt_call_placed_ok segPreKey_encrypt_err_placed_ok segPreKey_buildMessage_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding
  ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced
  EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced
  SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced
  SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced
  SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName
  cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced
  encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym
  lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec
  otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced
  withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed
  withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding
  EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok
  tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok
  tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Obj.MultiPlacedLib.blockProgram

/-! ## 1. `VT` `OTR::encrypt` Call Helpers & `h45_segPreKey_encrypt_call_placed_ok` (`+0x8b4..+0x8c8`) -/

private theorem h45_segExitVT_of_sepWP_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop}
    {mid : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R)) (hwp : SepWP (lsProg_464 Hk) mid s P post)
    (hcont : ∀ sm Pm, (lsProg_464 Hk).CodeLoaded s.mem → Steps (lsProg_464 Hk) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) → post sm Pm →
      WithStoresVT.Seg4PlacedBudget.h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 sm next) :
    WithStoresVT.Seg4PlacedBudget.h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

private theorem h45_otrEnc_budget_pre_frame [LibsignalPlacement] {M : AllocCostModel}
    (F0 : SepProp) (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr sp : BitVec 64)
    (R Pm : SepProp) (s0 s1 : State)
    (hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr)))
    (h64 : 64 ≤ x.rest.length) (hQ : otr.pqrState.length < 2 ^ 32)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem) (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x580#64) (hx1 : s1.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s1.readReg64 .x2 = x.ptA) (hx3 : s1.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hptlen : x.ptext.length < 2 ^ 32) (hx4 : s1.readReg64 .x4 = x.locA) (hlocA : x.locA ≠ 0#64)
    (hx5 : s1.readReg64 .x5 = x.remA)
    (hPm : Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
      ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA))
    (hm : s1.mem ⊨ Pm ∗ ((otrAt (A.atState lim st s1) (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt (A.atState lim st s1) x.loc x.locA ∗
        protocolAddressAt (A.atState lim st s1) x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ (A.atState lim st s1).pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt (A.atState lim st s1) x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (F0 ∗ R))) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl
        (WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQT F0 C A lim ctl uuidTryParse S sendEnv)).pre
        (preKeyOtrGhost x sp pqCap pqPtr otr, st) s1 ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
        ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  rw [show preKeyEncryptCallRestFrame ss_vt id_vt (A.atState lim st s1) =
      preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc from rfl] at hm'
  unfold StoreKit.withLsRoCl WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQT
    WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQF
  dsimp only
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hfit, ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec
    preKeyOtrGhost optAddrAt
  dsimp only
  rw [hsp1]
  have hx3_nat : (s1.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3]; exact bitvec_ofNat_toNat_lt_32 hptlen
  have hgoal : s1.mem ⊨
      (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ : SepProp) ∗
      ⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
      ⌜s1.readReg64 .x0 = sp + 0x580#64 ∧ s1.readReg64 .x1 = sp + 0x288#64 ∧
        s1.readReg64 .x2 = x.ptA ∧ (s1.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
        s1.readReg64 .x4 = (if (some x.loc).isSome then x.locA else 0#64) ∧
        ((some x.loc).isSome → x.locA ≠ 0#64) ∧ s1.readReg64 .x5 = x.remA⌝ ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
        ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      ((otrAt (A.atState lim st s1) (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt (A.atState lim st s1) x.loc x.locA ∗
        protocolAddressAt (A.atState lim st s1) x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ (A.atState lim st s1).pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (F0 ∗ R))) := by
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hcrl1, ⟨hQ, h64⟩, ⟨hx0, hx1, hx2, hx3_nat, hptlen, hx4, fun _ => hlocA, hx5⟩, hm'⟩
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hgoal

private theorem h45_otrEnc_budget_post_unpack [LibsignalPlacement] {M : AllocCostModel}
    (F0 : SepProp) (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr sp : BitVec 64)
    (R : SepProp) (s0 s1 s2 : State) (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨
      ((StoreKit.withLsRoCl lsmpl
          (WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQT F0 C A lim ctl uuidTryParse S sendEnv)).post
          (preKeyOtrGhost x sp pqCap pqPtr otr, st) s1 s2 ∗
        ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
          ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
          preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0)) ∗ R) :
    let res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
    ∃ (evs : List AllocEvent) (pqCap' pqPtr' : BitVec 64),
      OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr) evs ∧
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧ res.1 ≠ .error .panic ∧ s2.trace = s1.trace ∧
      (s2.mem ⊨
        sessionRecordAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt (A.atState lim (M.stepEvents evs st) s2) (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
        memRegion (sp + 0x5f8#64) 0x2a8 ∗
        optKyberAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x8a0#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
        memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim (M.stepEvents evs st) s2) ctl x (S.draws otr.pqrState x.rest) s0 ∗
        (F0 ∗ R)) := by
  intro res
  unfold StoreKit.withLsRoCl WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQT
    WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQF
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF at hpost
  dsimp only at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨evs, hpost⟩ := hpost
  let A' := A.atState lim (M.stepEvents evs st) s2
  have h0 : s2.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗
      ⌜OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr) evs⌝ ∗
      (((F0 ∗ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec C A' ctl uuidTryParse S).post
          (preKeyOtrGhost x sp pqCap pqPtr otr) s1 s2) ∗
        ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
          ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
          preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0)) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h0
  rcases h0 with ⟨hcrl2, hevs, hpost⟩
  refine ⟨evs, ?_⟩
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec at hpost
  dsimp only [optAddrAt] at hpost
  rw [hsp1] at hpost
  change s2.mem ⊨ ((F0 ∗
    (⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64, otrAt A' (sp + 0x288#64) pqCap' pqPtr' res.2) ∗
      signalMessageResultAt A' (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A' x.loc x.locA ∗ protocolAddressAt A' x.rem x.remA ∗
      cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
      FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A'.pool)) ∗ _) ∗ R at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨pqCap', pqPtr', hpost⟩ := hpost
  have h1 : s2.mem ⊨ ⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      ((otrAt A' (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
        signalMessageResultAt A' (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A' x.loc x.locA ∗ protocolAddressAt A' x.rem x.remA ∗
        cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A'.pool ∗
        (((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
          ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (F0 ∗ R)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨pqCap', pqPtr', hevs, hcrl2, hne, htr, ?_⟩
  rw [show preKeyEncryptCallRestFrame ss_vt id_vt A.repAlloc =
      preKeyEncryptCallRestFrame ss_vt id_vt A' from rfl] at hmem
  unfold preKeyEncryptCallRestFrame at hmem
  rw [preKeyEncryptScratch'_eq, encSpillsAt_eq]; unfold encCommonPlaced
  rw [hsp0, stackAt_sub sp encSubStack rootStack]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem

theorem h45_segPreKey_encrypt_call_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg4PlacedBudget.EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length) (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState'Budget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s) :
    WithStoresVT.Seg4PlacedBudget.h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun s' => ∃ st',
        PreKeyEncryptRetStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st' r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hst with ⟨hbud, prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr,
    hts, hexp, hlt, hpkVal, hpc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr,
    hx20, hx22, hx24, hx25, hx26, _hx27, hx28, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  have hQ : otr.pqrState.length < 2 ^ 32 := fromSessionState_pqrState hfrom ▸ hEnv.scopeQ r sess hscope hcur
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (preKeyOtrGhost x sp pqCap pqPtr otr)) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud.1
  have hmem' : s.mem ⊨
      sessionRecordAt (A.atState lim st s) (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ pollE6c' (A.atState lim st s) sp kyBoxPtr items sess.pendingKyberPreKey ∗
      memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗ (F0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hmem
  have hm_unp := preKeyEncrypt_placed_mem_unpack kit.ss_vt ikit.id_vt (A.atState lim st s) ctl
    x prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp (F0 ∗ R) s0 hsp0 hrestlen hmem'
  refine h45_segExitVT_of_sepWP_placed hm_unp (preKeyEncrypt_placed_step_bl_vm hpc hrun hsp hal) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5,
      hs1_x19, hs1_x20, hs1_x22, hs1_x24, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  rw [← A.atState_eq_of_vmPreserved lim st hvm01] at hm1
  have hm1_pre := h45_otrEnc_budget_pre_frame F0 kit.ss_vt ikit.id_vt C A lim ctl S sendEnv
    x st prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R Pm1 s0 s1
    hfit h64 hQ hcrl1 hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_x3 hptlen hs1_x4 hlocA hs1_x5 hPm1 hm1
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_call_sub_placed hEnv.callees.otrEnc
    (preKeyOtrGhost x sp pqCap pqPtr otr, st)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl
            (WithStoresVT.Seg4PlacedBudget.otrEncryptBudgetSpecQT F0 C A lim ctl uuidTryParse S sendEnv)).onExit
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
    h45_otrEnc_budget_post_unpack F0 kit.ss_vt ikit.id_vt C A lim ctl S sendEnv
      x st prevCap prevPtr G sess otr taken pqCap pqPtr k items pkVal kyBoxPtr sp R s0 s1 s2
      hsp0 hs1_sp hpost2
  have hm2' : s2.mem ⊨
      sessionRecordAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x288#64) pqCap' pqPtr'
        ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt (A.atState lim (M.stepEvents evs st) s2) (utf8 "encrypt") (sp + 0x580#64)
        ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt (A.atState lim (M.stepEvents evs st) s2) (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim (M.stepEvents evs st) s2) ctl x (S.draws otr.pqrState x.rest) s0 ∗
      (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ (F0 ∗ R0)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hm2
  exact WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
    (SegExitBudget.next ⟨M.stepEvents evs st, hbud.advance hevs,
      prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
      hts, hexp, hlt, hpkVal, hne2, hs2_pc,
      ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hcrl2,
        (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩,
      hs2_tr.trans (hs1_tr.trans htr),
      by reg_chain, by reg_chain, hs2_x24, by reg_chain, by reg_chain, by reg_chain,
      hptlen, hrestlen, hlocA, hnow, hstack, hm2'⟩)

/-! ## 2. `h45_segPreKey_encrypt_err_placed_ok` (`+0x8c8..+0x8ec` → `hEnv.tailPreKeyEncryptErr`) -/

theorem h45_segPreKey_encrypt_err_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
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
  refine hEnv.tailPreKeyEncryptErr x st_init st R0 s0 s3
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

/-! ## 3. Unpack Helpers & `h45_segPreKey_buildMessage_placed_ok` (`+0x8c8..+0xa70` → `CmStateVBudget`) -/

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

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_buildMessage_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
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
    (hret : PreKeyEncryptRetStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R s0 s
      (fun sf => ∃ st' m otr' pqCap' pqPtr',
        CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 sf) := by
  rcases hret with ⟨hbud, prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx22, hx24, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hm
  set sp := s0.sp - 0xbe0#64
  have hsp_eq : sp = s0.sp - 0xbe0#64 := rfl
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have hok' : res.1 = .ok sm := hok
  have hok_mut : (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
      (serializeAddresses (serviceIdParse uuidTryParse) x.loc x.rem) x.rest) otr).1 = .ok sm := hok'
  have hbud_psm : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (PreKeyMsgNewRawEnv (pendingKyberPayload sess) sm.serialized.length
          (preKeyMsgFromItems sess items res.2 sm).serialized.length)
        (fun evs'' =>
          FreeOnlyEvs evs'' ∨
          FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess res.2 taken k evs'')) :=
    hbud.narrow fun _ h => Or.inr (by
      rw [hok_mut]
      exact h)
  have hfit_raw : FitsEnv M lim st
      (PreKeyMsgNewRawEnv (pendingKyberPayload sess) sm.serialized.length
        (preKeyMsgFromItems sess items res.2 sm).serialized.length) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_psm.1
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  let R' := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R
  change s.mem ⊨
    sessionRecordAt (A.atState lim st s) (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt (A.atState lim st s) (sp + 0x288#64) pqCap' pqPtr' res.2 ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
    signalMessageResultAt (A.atState lim st s) (utf8 "encrypt") (sp + 0x580#64) res.1 ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
    optKyberAt (A.atState lim st s) (sp + 0x8a0#64) kyBoxPtr
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
    memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (S.draws otr.pqrState x.rest) s0 ∗ R' at hm
  rw [hok'] at hm
  obtain ⟨b, hw0, hmsg_len, hik, hbk, hsm_rel, hky_rel, hm_e6d⟩ :=
    buildPreKeyMsg_placed_pre_unpack (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) ctl x sess taken res.2
      prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k items pkVal sm (S.draws otr.pqrState x.rest)
      sp R' s0 s hm
  refine SegExitBudget.of_sepWP hm_e6d
    (buildPreKeyMsg_placed_step_bl_vm hs_pc hrun hsp hal hx22 hx25 hx26 hx29' hw0) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8,
      hs1_x19, hs1_x20, hs1_x22, _, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  rw [← A.atState_eq_of_vmPreserved lim st hvm01] at hm1 hsm_rel hky_rel
  let call : PreKeyMsgNewCall :=
    { ret := sp + 0x580#64, ver := res.2.sessionVersion, regId := sess.localRegistrationId,
      preKeyId := items.preKeyId, spk := items.signedPreKeyId, kyA := sp + 0x950#64,
      kyPtr := kyBoxPtr,
      kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload),
      bkA := sp + 0xae0#64, baseKey := items.baseKey, ikA := sp + 0xb00#64,
      ik := res.2.localIdentityKey, msgA := sp + 0x8b8#64, msgG := b.msgG, msg := sm }
  have hfit_psm : FitsEnv M lim st (PreKeyMsgNewEnv call) := hfit_raw
  have hm1_sub : s1.mem ⊨
      (Pm1 ∗ buildPreKeyMsgRestFramePlaced (retagSessionStore (A' := A.atState lim st s1) kit)
        (retagIdentityStore (A' := A.atState lim st s1) ikit)
        ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp b.H_sm b.H_ky s0) ∗ R' :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm1_pack := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm1)
        (preKeyMsgNew_placed_pre_pack (retagSessionStore (A' := A.atState lim st s1) kit)
          (retagIdentityStore (A' := A.atState lim st s1) ikit)
          ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
          items pkVal b.msgG sm b.ik0 b.ik1 b.ik2 b.ik3
          b.w0 b.w1 b.w2 b.w3 b.w4 b.w5 b.w6 b.w7 b.w8 b.w9 b.w10 b.w11 b.w12 b.w13 b.w14
          b.k0 b.k1 b.k2 b.bk0 b.bk1 b.bk2 b.bk3 b.H_sm b.H_ky (S.draws otr.pqrState x.rest) sp s0 s1
          hsp_eq hs1_sp hik hbk hsm_rel hky_rel)))
    hm1_sub
  rw [show preKeyMsgCallFramePlaced (retagSessionStore (A' := A.atState lim st s1) kit)
        (retagIdentityStore (A' := A.atState lim st s1) ikit) =
      preKeyMsgCallFramePlaced kit ikit from rfl] at hm1_pack
  have hcall_len : call.model.serialized.length < 2 ^ 42 :=
    call.model_serialized_length_lt hmsg_len
      (kyber_ciphertext_length_lt (hEnv.toEncEnvTBudget.scopeIn r hscope) hcur)
  have hcall_pure :
      (s1.readReg64 .x0).setWidth 8 = call.ver ∧ (s1.readReg64 .x1).setWidth 32 = call.regId ∧
      (s1.readReg64 .x2).setWidth 32 = (if call.preKeyId.isSome then 1#32 else 0#32) ∧
      (∀ v, call.preKeyId = some v → (s1.readReg64 .x3).setWidth 32 = v) ∧
      (s1.readReg64 .x4).setWidth 32 = call.spk ∧ s1.readReg64 .x5 = call.kyA ∧
      (s1.readReg64 .x6 = call.bkA ∧ s1.readReg64 .x7 = call.ikA ∧
      s1.readReg64 .x8 = call.ret ∧ call.model.serialized.length < 2 ^ 42) :=
    ⟨hs1_x0, hs1_x1, hs1_x2.trans hx24, fun v hv => hs1_x3.trans (hpkVal v hv),
      hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8, hcall_len⟩
  have hm1_pre : s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (preKeyMsgNewBudgetSpec M A lim)).pre (call, st) s1 ∗
      (preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R') := by
    have hpre_p : ∀ {P : Prop} {Q : SepProp}, P → (s1.mem ⊨ Q) → (s1.mem ⊨ ⌜P⌝ ∗ Q) := by
      intro P Q hP hQ; rw [satisfies_pure_sepConj]; exact ⟨hP, hQ⟩
    have hm1_both := hpre_p hcrl1 (hpre_p hcall_pure hm1_pack)
    unfold StoreKit.withLsRoCl preKeyMsgNewBudgetSpec preKeyMsgNewSpec
    dsimp only
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfit_psm, by rw [hs1_lr]; simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩,
      Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1_both⟩
  clear hw0 hik hbk hsm_rel hky_rel hm_e6d Pm1 hm1 hPm1 hm1_sub hm1_pack hcall_len hcall_pure
  refine SegExitBudget.call hEnv.calleesFull.psmNew (call, st) hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (preKeyMsgNewBudgetSpec M A lim)).onExit (call, st) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      rw [show (StoreKit.withLsRoCl lsmpl (preKeyMsgNewBudgetSpec M A lim)).onPanic (call, st) s1 sf = ⌜False⌝ from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact hpost.1.elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  rcases hcs12 with ⟨hx19_2, hx20_2, _, hx22_2, _, _, hx25_2, hx26_2, _, hx28_2, hx29_2, hvregs_2⟩
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x22 : s2.readReg64 .x22 = sp + 0x8b8#64 := hx22_2.trans (hs1_x22.trans hx22)
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := hx25_2.trans (hs1_x25.trans hx25)
  unfold StoreKit.withLsRoCl preKeyMsgNewBudgetSpec at hpost2
  dsimp only [call] at hpost2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost2
  obtain ⟨evs_psm, hpost2⟩ := hpost2
  set st' := M.stepEvents evs_psm st
  unfold preKeyMsgNewSpec at hpost2
  dsimp only at hpost2
  have hpost2_rearr : s2.mem ⊨ ⌜PreKeyMsgNewEnv call evs_psm⌝ ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗
      ⌜s2.trace = s1.trace⌝ ∗
      (((∃∗ g : PreKeyMsgGhost, preKeyMsgAt (A.atState lim st' s2) g (sp + 0x580#64) call.model) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ res.2.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ (A.atState lim st' s2).pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFramePlaced (retagSessionStore (A' := A.atState lim st' s2) kit)
        (retagIdentityStore (A' := A.atState lim st' s2) ikit)
        ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R') := by
    rw [hs1_sp] at hpost2
    rw [show preKeyMsgCallFramePlaced kit ikit =
        preKeyMsgCallFramePlaced (retagSessionStore (A' := A.atState lim st' s2) kit)
          (retagIdentityStore (A' := A.atState lim st' s2) ikit) from rfl] at hpost2
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [sp, res, call, st', R']; sep_ac_rfl)) hpost2
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost2_rearr
  rcases hpost2_rearr with ⟨hevs_psm, hcrl2, hs2_tr, hm2'⟩
  have hbud_cm : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st'
      (FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess res.2 taken k) :=
    (hbud_psm.advance hevs_psm).narrow fun _ => Or.inr
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  clear hpost2 hm1_pre
  obtain ⟨u, hpw0, hpsm_rel, hm2_e6e⟩ :=
    cmCopy_placed_pre_unpack (retagSessionStore (A' := A.atState lim st' s2) kit)
      (retagIdentityStore (A' := A.atState lim st' s2) ikit)
      ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
      items pkVal call.model (S.draws otr.pqrState x.rest) sp R' s0 s2 hsp_eq hm2'
  refine SegExitBudget.of_sepWP hm2_e6e
    (cmCopy_placed_step_ok_vm hs2_pc hs2_run hs2_sp' hs2_al hs2_x22 hs2_x25 hpw0) ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hvm23, hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  rw [← A.atState_eq_of_vmPreserved lim st' hvm23] at hm3 hpsm_rel
  have hm3_sub : s3.mem ⊨
      (Pm3 ∗ cmCopyRestFramePlaced (retagSessionStore (A' := A.atState lim st' s3) kit)
        (retagIdentityStore (A' := A.atState lim st' s3) ikit)
        ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp u.H_psm s0) ∗ R' :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm3
  have hm3_cm := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm3)
        (cmCopy_placed_post_pack (retagSessionStore (A' := A.atState lim st' s3) kit)
          (retagIdentityStore (A' := A.atState lim st' s3) ikit)
          ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
          u.psmG call.model
          u.w0 u.w1 u.w2 u.w3 u.w4 u.w5 u.w6 u.w7 u.w8 u.w9 u.w10 u.w11 u.w12 u.w13 u.w14
          u.w15 u.w16 u.w17 u.w18 u.w19 u.w20 u.w21 u.w22 u.w23 u.w24 u.w25 u.w26 u.w27 u.w28 u.w29 u.w30
          u.H_psm (S.draws otr.pqrState x.rest) sp s0 hpsm_rel)))
    hm3_sub
  clear u hpw0 hpsm_rel hm2' hm2_e6e Pm3 hm3 hPm3 hm3_sub
  have hsteps15 := stepsThroughEncrypt_of_preKey_ok_placed hcur hscope hfrom hrem hpk hts hexp hlt hok'
  refine SegExitBudget.next ⟨st', .preKeySignalMessage call.model, res.2, pqCap', pqPtr',
    hbud_cm, hsteps15, ?_⟩
  dsimp only [retagSessionStore, retagIdentityStore]
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
    Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [retagSessionStore, retagIdentityStore, sp, call, PreKeyMsgNewCall.model, R']; sep_ac_rfl)) hm3_cm⟩

/-! ## 4. `h45_segPreKey_tail_placed_ok` & `h45_segPreKey_placed_okVT` -/

theorem h45_segPreKey_tail_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length) (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState'Budget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s) :
    WithStoresVT.Seg4PlacedBudget.h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun sf => ∃ st' m otr' pqCap' pqPtr',
        CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R0) s0 sf) := by
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
    (h45_segPreKey_encrypt_call_placed_ok hEnv.toEncEnvTBudget x st_init st r sess otr taken pqCap pqPtr k items R0 s0 s
      h64 hcur hscope hfrom hrem hpk hst) fun s2 ⟨st2, hret⟩ => ?_
  rcases hres : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 with e | sm
  · exact WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_false_placed
      (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
        (h45_segPreKey_encrypt_err_placed_ok hEnv x st_init st2 r sess otr taken pqCap pqPtr k items e (F0 ∗ R0) s0 s2
          hcur hscope hfrom hrem hpk hres hret))
  · exact WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
      (h45_segPreKey_buildMessage_placed_ok hEnv x st_init st2 r sess otr taken pqCap pqPtr k items sm (F0 ∗ R0) s0 s2
        hcur hscope hfrom hrem hpk hres hret)

theorem h45_segPreKey_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg1PlacedBudgetAux.EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : WithStoresVT.Seg1PlacedBudgetAux.EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length) (his : sess.pendingPreKey.isSome = true)
    (hkey : PlacedDefsBudget.KeyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr k (F0 ∗ R0) s0 s) :
    WithStoresVT.Seg4PlacedBudget.h45_SegExitVTPlaced F0 A lim kit (PlacedDefsBudget.toTempTwinsKitEnv kitEnv) st0
      ikit (PlacedDefsBudget.toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun sf => ∃ st' m otr' pqCap' pqPtr',
        PlacedDefsBudget.CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R0) s0 sf) := by
  let envT := h45_envTBudget_of_placed hEnv
  let envFull := h45_envTFullBudget_of_placed hEnv hTails
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.2.1; have hscope := hkey.2.2.1; have hfrom := hkey.2.2.2.1; have hrem := hkey.2.2.2.2.1
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
    (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
      (h45_segPreKey_unackItems_to_dur_placed_ok envT x st_init st r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s hpk hkey)) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
    (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
      (h45_segPreKey_staleness_to_add_placed_ok envFull x st_init st r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen (F0 ∗ R0) s0 s1 hcur hscope hfrom hrem hpk hdur)) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_false_placed
      (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
        (h45_segPreKey_stale_placed_ok envFull x st_init st r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen (F0 ∗ R0) s0 s2 hcur hscope hfrom hrem hpk hlt hadd))
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
      (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
        (h45_segPreKey_regId_kyber_placed_ok envFull x st_init st r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen (F0 ∗ R0) s0 s2 hcur hscope hpk hlt_f hadd)) ?_
    rintro s3 ⟨st3, he6c⟩
    exact h45_segPreKey_tail_placed_ok envFull x st_init st3 r sess otr taken pqCap pqPtr k items R0 s0 s3
      h64 hcur hscope hfrom hrem hpk he6c

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux
