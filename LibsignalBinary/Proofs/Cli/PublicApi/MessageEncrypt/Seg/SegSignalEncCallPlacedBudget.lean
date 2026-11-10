/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `segSignal` `OTR::encrypt` Call (`Enc` → `Ret`)

Proves `segSignal_placed_enc_to_ret_pf` across `bl OTR::encrypt` returning to `+0x3a4` on
Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncCallPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnackPlacedBudget
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
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
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

private theorem tapeAfter_zero_entails_tapeAt_placed [LibsignalPlacement] (ctl cur : BitVec 64) (rest : List (BitVec 8))
    (hrest : rest.length < 2 ^ 63) :
    cliTapeAfter ctl cur rest 0 ⊢ cliTapeAt ctl cur rest :=
  cliTapeAfter_zero_entails_cliTapeAt ctl cur rest hrest

/-- Frame around `OTR::encrypt` at `segSignal` under `[LibsignalPlacement]`. -/
private def segSignalEncCallFramePlaced {ss_vt id_vt : BitVec 64} (A : RustAlloc)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
  memRegion x.ret 248 ∗
  protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_enc_pre_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    {M : AllocCostModel} {Q : List (BitVec 8) → Prop}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x)))
    (hQ : Q otr.pqrState) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = sp + 0x580#64) (hx1 : s.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s.readReg64 .x2 = x.ptA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hx4 : s.readReg64 .x4 = 0#64) (hx5 : s.readReg64 .x5 = x.remA)
    (hpt : x.ptext.length < 2 ^ 32) (hrest : x.rest.length < 2 ^ 63)
    (hm : s.mem ⊨
      (takenSlots (A.atState lim st s) sp sess taken ∗
        otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗ R) :
    ∃ g : RecordGhost,
      s.mem ⊨ (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl uuidTryParse S sendEnv)).pre
          (segSignalEncGhost sp pqCap pqPtr otr x, st) s ∗
        (segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0 ∗ R) := by
  unfold takenSlots encCommonPlaced at hm
  rw [hsp0, stackAt_sub sp encSubStack rootStack] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  refine ⟨g, ?_⟩
  rw [show sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc from rfl,
    show protocolAddressAt (A.atState lim st s) x.loc x.locA = protocolAddressAt A.repAlloc x.loc x.locA from rfl] at hm
  have htape := tapeAfter_zero_entails_tapeAt_placed ctl x.cur x.rest hrest
  have hm_rearr : s.mem ⊨
      cliTapeAfter ctl x.cur x.rest 0 ∗
      (otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗
        (A.atState lim st s).pool ∗
        segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0 ∗ R) := by
    unfold segSignalEncCallFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
  have hm_tape := Satisfies.mono (sepConj_mono_left htape) hm_rearr
  have hx3_nat : (s.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold StoreKit.withLsRoCl otrEncryptBudgetSpecQ
  dsimp only
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hfit, ?_⟩
  unfold otrEncryptPlacedSpecQ otrEncryptPlacedSpec segSignalEncGhost optAddrAt
  dsimp only
  rw [hsp, emp_sepConj]
  have hgoal : s.mem ⊨
      (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ : SepProp) ∗
      ⌜Q otr.pqrState⌝ ∗
      ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
        s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧
        s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
        ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
        s.readReg64 .x5 = x.remA⌝ ∗
      (cliTapeAt ctl x.cur x.rest ∗
        (otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗
          (A.atState lim st s).pool ∗
          segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0 ∗ R)) := by
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hcrl, hQ, ⟨hx0, hx1, hx2, hx3_nat, hpt, hx4, (by intro h; cases h), hx5⟩, hm_tape⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hgoal

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_enc_post_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    {M : AllocCostModel} {Q : List (BitVec 8) → Prop}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s sm : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hpost : sm.mem ⊨
      ((StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl uuidTryParse S sendEnv)).post
          (segSignalEncGhost sp pqCap pqPtr otr x, st) s sm ∗
        segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0) ∗ R) :
    ∃ evs : List AllocEvent,
      OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x) evs ∧
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem ∧
      (segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace ∧
      (sm.mem ⊨
        (sessionRecordAt (A.atState lim (M.stepEvents evs st) sm) (sp + 0x110#64) g (takenRecord sess taken) ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
            otrAt (A.atState lim (M.stepEvents evs st) sm) (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        (memRegion (sp + 0x46a#64) 0x116 ∗
          signalMessageResultAt (A.atState lim (M.stepEvents evs st) sm) (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
          memRegion (sp + 0x5f8#64) 0x588) ∗
        memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim (M.stepEvents evs st) sm) ctl x (S.draws otr.pqrState x.rest) s0 ∗ R) := by
  unfold StoreKit.withLsRoCl otrEncryptBudgetSpecQ otrEncryptBudgetSpec at hpost
  dsimp only at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨evs, hpost⟩ := hpost
  let A' := A.atState lim (M.stepEvents evs st) sm
  have h0 : sm.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
      ⌜OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x) evs⌝ ∗
      (((otrEncryptPlacedSpec C A' ctl uuidTryParse S).post
          (segSignalEncGhost sp pqCap pqPtr otr x) s sm ∗
        segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0) ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h0
  rcases h0 with ⟨hcrlm, hevs, hpost⟩
  refine ⟨evs, hevs, hcrlm, ?_⟩
  unfold otrEncryptPlacedSpec at hpost
  dsimp only at hpost
  rw [segSignalEncGhost_model, hsp] at hpost
  unfold segSignalEncGhost optAddrAt at hpost
  dsimp only at hpost
  rw [emp_sepConj] at hpost
  have h1 : sm.mem ⊨
      ⌜(segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace⌝ ∗
      (((∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A' (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        signalMessageResultAt A' (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A' x.rem x.remA ∗
        cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A'.pool ∗
        segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0) ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨hne, htr, ?_⟩
  unfold segSignalEncCallFramePlaced at hmem
  rw [show sessionRecordAt A.repAlloc = sessionRecordAt A' from rfl,
    show protocolAddressAt A.repAlloc x.loc x.locA = protocolAddressAt A' x.loc x.locA from rfl] at hmem
  have hmem_rearr : sm.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
        stackAt sp rootStack) ∗
      (sessionRecordAt A' (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A' (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A' (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A' x.rem x.remA ∗ protocolAddressAt A' x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ encSavedRegs s0.sp s0 ∗ A'.pool ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack rootStack] at hmem_rearr
  unfold encCommonPlaced
  rw [hsp0]
  exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmem_rearr

/-- **Enc → Ret** (`bl OTR::encrypt` returns to `+0x3a4`) under `[LibsignalPlacement]`:
`otrEncryptBudgetSpecQ Q` on `(segSignalEncGhost sp pqCap pqPtr otr x, st)`, `Q otr.pqrState` from
`env.q_otr`, panic via `segSignal_panic_bridge_placed`. -/
theorem segSignal_placed_enc_to_ret_pf [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (hs : SegSignalEncStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun s' => ∃ st',
        SegSignalRetStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st' r sess otr taken k R0 s0
          s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hs_pc, hs_lr,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx0, hx1, hx2, hx3, hx4, hx5, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hbud_seq : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x))
        (fun evs' =>
          FreeOnlyEvs evs' ∨
          FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess (segSignalRes C S x otr).2 taken k evs')) :=
    hbud.narrow fun _ hseq => Or.inl ⟨hnone, hseq⟩
  have hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x)) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_seq.1
  have hQ : Q otr.pqrState := env.q_otr hcur hsc hfrom
  obtain ⟨g, hm_pre⟩ := segSignal_placed_enc_pre_unpack C A lim ctl S sendEnv x st sess otr taken pqCap pqPtr k sp R
    s0 s hsp0.symm hsp hfit hQ hcrl hx0 hx1 hx2 hx3 hx4 hx5 hpt hrest hm
  refine SegExitBudget.call env.callees.otrEnc (segSignalEncGhost sp pqCap pqPtr otr x, st)
    hs_pc hrun hal hs_lr hm_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ Q C A lim ctl uuidTryParse S sendEnv)).onExit
            (segSignalEncGhost sp pqCap pqPtr otr x, st) code s _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => segSignal_panic_bridge_placed hcur hsc hnone hfrom hrem htr hpost)
    ?_
  intro sm _hL1 _hsteps12 hsm_pc hsm_run hsm_sp hcsm hpost
  have hsm_sp' : sm.sp = sp := hsm_sp.trans hsp
  have hsm_al : sm.spAligned = true := spAligned_of_sp_eq hal hsm_sp
  have hsm_x19 : sm.readReg64 .x19 = x.ret := (hcsm.1).trans hx19
  have hsm_x20 : sm.readReg64 .x20 = sp + 0x58#64 := (hcsm.2.1).trans hx20
  have hsm_x25 : sm.readReg64 .x25 = sp + 0x580#64 := (hcsm.2.2.2.2.2.2.1).trans hx25
  have hsm_x26 : sm.readReg64 .x26 = sp + 0x9d0#64 := (hcsm.2.2.2.2.2.2.2.1).trans hx26
  have hsm_x28 : sm.readReg64 .x28 = sp + 0x4a0#64 := (hcsm.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsm_x29 : sm.readReg64 .x29 = s0.sp - 0x60#64 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.1).trans hx29
  have hsm_vregs : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.2).trans hvregs
  obtain ⟨evs, hevs, hcrlm, hne, hsm_tr, hm_ret⟩ :=
    segSignal_placed_enc_post_pack C A lim ctl S sendEnv x st g sess otr taken pqCap pqPtr k sp R s0 s sm
      hsp0.symm hsp hpost
  refine SegExitBudget.next ⟨M.stepEvents evs st, hbud_seq.advance hevs, hcur, hsc, hfrom, hrem, hnone, hne, hsm_pc,
    ⟨hsm_run, hsm_sp', hal0, hsm_al, hsm_x29, hsm_x19, hcrlm, hsm_vregs⟩,
    hsm_tr.trans htr, hsm_x20, hsm_x25, hsm_x26, hsm_x28,
    hpt, hrest, hloc, hnow, hstk, g, hm_ret⟩

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncCallPlacedBudget
