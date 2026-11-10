/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec

/-!
# Tight `fineCostModel` Credit and Group Specifications for SPQR `spqr::send::<Coins>`

Combines the tight `spqr::send` sub-phase credit bounds (`SpqrSendPeakSpec`), `spqr::recv` credit
and group instances (`SpqrRecvC09aWire`), and `FineScale` slot-group accounting (`spqrSendTightGroupS =
281,542,656` = `4,296` groups across `≤ 1,432` non-free operations) into closed `fineCostModel`
credit, group, and `1 GiB` `FitsEnv` specs for `spqr::send::<Coins>` and `StoresGhost.opened`
encrypt.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord execOk)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB PqRatchetState States V1State VersionNegotiationPB spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainSendKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (otrEncryptStepEnv_groupSpec spqrNonFreeCount_eq withStoresEncTightEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (w1CliOpenedCustomSendCum w1CliOpenedCustomSendLive w1CliOpenedCustomSendMaxReq
   w1CliOpenedCustomSendPeak w1CliOpenedCustomSend_live_le_peak w1CliOpenedCustomSend_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSmallStorePollEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
  (c09aStatesRecvTightCreditSpec_inst c09aStatesRecvTightGroupSpec_inst
   spqrRecvParts_c07_128_c09a_phaseGroupSpec_tight
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist
   spqrRecvParts_c07_c09a_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (SpqrSendC07TightEnv SpqrSendTightCapEnv SpqrSendTightLargeEnv
   spqrSendLarge_nonFreeCount_le_tight spqrSendParts_c07_fineCredit_le_tight
   spqrSendParts_c07_nonFreeCount_le spqrSendParts_c07_phaseCreditSpec_tight
   spqrSendParts_c07_phaseCreditSpec_tight_largeEncode spqrSendTight79236DeltaCum
   spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
   spqrSendTightFineCreditCap spqrSendTightLargeDeltaCum spqrSendTightMaxReq
   spqrSend_evalLog_footprint_le_tight spqrSend_fineCredit_le_tight
   spqrSend_nonFreeCount_le_tight spqrSend_phaseCreditSpec_tight
   spqrSend_phaseCreditSpec_tight_largeEncode)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
  (SpqrSendTightDomain SpqrSendTightDomain707)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (ValidChainParams ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec (OtrEncryptStepEnv WithStoresEncTightEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak (otrAfterNone otrAfterSome)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak
   preKeyMsgNewMaxReq signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

/-! ## `spqr::send` and `spqr::recv` Tight Re-Exports -/

export SpqrSendPeakSpec
  (SpqrSendTightCapEnv SpqrSendTightLargeEnv SpqrSendC07TightEnv spqrSendTightDeltaCum)
export SpqrSendPeakSpec
  (spqrSendTightLargeDeltaCum spqrSendTight79236DeltaCum spqrSendTightDeltaLive
   spqrSendTightDeltaPeak)
export SpqrSendPeakSpec
  (spqrSendTightMaxReq spqrSendTightFineCreditCap spqrSend_phaseCreditSpec_tight
   spqrSend_phaseCreditSpec_tight_largeEncode)
export SpqrSendPeakSpec
  (spqrSendParts_c07_phaseCreditSpec_tight spqrSendParts_c07_phaseCreditSpec_tight_largeEncode
   spqrSend_fineCredit_le_tight spqrSend_evalLog_footprint_le_tight)
export SpqrSendPeakSpec
  (spqrSendParts_c07_fineCredit_le_tight)
export SpqrSendRodataCaps
  (SpqrSendTightDomain SpqrSendTightDomain707)

export SpqrRecvC09aWire
  (c09aStatesRecvTightCreditSpec_inst c09aStatesRecvTightGroupSpec_inst
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight spqrRecvParts_c07_c09a_phaseGroupSpec_tight)
export SpqrRecvC09aWire
  (spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist
   spqrRecvParts_c07_128_c09a_phaseGroupSpec_tight)

/-! ## `PhaseGroupSpec` and `1 GiB` `FitsEnv` Bounds for `spqr::send` -/

/-- Upper bound on non-`.free` allocator operations across all 10 `spqr::send` sub-phases (`1,432`).
-/
def spqrSendTightMaxNonFree : Nat := 1432

/-- `FineScale`-scaled slot-group bound (`3 * FineScale * 1432 = 281,542,656` = `4,296` groups) for tight `spqr::send` envelopes.
-/
def spqrSendTightGroupS : Nat := 3 * FineScale * spqrSendTightMaxNonFree

theorem spqrSendTightGroupS_val :
    spqrSendTightGroupS = 281542656 ∧
    (spqrSendTightGroupS + FineScale - 1) / FineScale = 4296 := by
  decide

theorem spqrSendTightCap_nonFreeBound (stBytes ptext : Bytes) :
    NonFreeBound (SpqrSendTightCapEnv stBytes ptext) spqrSendTightMaxNonFree :=
  fun evs h => by
    rw [← spqrNonFreeCount_eq]
    exact spqrSend_nonFreeCount_le_tight h

theorem spqrSendTightCap_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (stBytes ptext : Bytes) :
    PhaseGroupSpec M (SpqrSendTightCapEnv stBytes ptext) spqrSendTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound M (spqrSendTightCap_nonFreeBound stBytes ptext)

theorem spqrSendTightLarge_nonFreeBound (stBytes ptext : Bytes) :
    NonFreeBound (SpqrSendTightLargeEnv stBytes ptext) spqrSendTightMaxNonFree :=
  fun evs h => by
    rw [← spqrNonFreeCount_eq]
    exact spqrSendLarge_nonFreeCount_le_tight h

theorem spqrSendTightLarge_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (stBytes ptext : Bytes) :
    PhaseGroupSpec M (SpqrSendTightLargeEnv stBytes ptext) spqrSendTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound M (spqrSendTightLarge_nonFreeBound stBytes ptext)

theorem spqrSendParts_c07_nonFreeBound (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain707 F stBytes pb st0 xAdd xSInto xCInto postSt) :
    NonFreeBound
      (SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      spqrSendTightMaxNonFree :=
  fun evs h => by
    rw [← spqrNonFreeCount_eq]
    exact spqrSendParts_c07_nonFreeCount_le F dom h

theorem spqrSendParts_c07_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (F : ShaCompress)
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB} {vn : Option VersionNegotiationPB}
    {xAdd : ChainAddEpochGhost} {xSk : ChainSendKeyGhost}
    {xCInto : ChainIntoPbCall} {xSInto : StatesIntoPbGhost F}
    {postSt : PqRatchetState}
    (dom : SpqrSendTightDomain707 F stBytes pb st0 xAdd xSInto xCInto postSt) :
    PhaseGroupSpec M
      (SpqrSendC07TightEnv F stBytes pb st0 chainPb vn xAdd xSk xCInto xSInto postSt)
      spqrSendTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound M (spqrSendParts_c07_nonFreeBound F dom)

/-- `FitsEnv fineCostModel` bound for `SpqrSendTightCapEnv` under a `1 GiB` (`< 2 ^ 30`) budget. -/
theorem spqrSendTightCap_fitsEnv_1GiB
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {stBytes ptext : Bytes}
    (hPts : ValidEncoderPts640 stBytes)
    (hChain : ValidChainParams stBytes) :
    FitsEnv fineCostModel lim fineCostModel.init (SpqrSendTightCapEnv stBytes ptext) := by
  have hram0 :
      cliDecoupledRamNeed cliDefaultStaticBytes
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ cliOneGiB := by
    decide
  have hva0 :
      cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ 2 ^ 48 := by
    decide
  have hram :
      cliDecoupledRamNeed lim.staticBytes
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap)
  have hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        spqrSendTightDeltaCum spqrSendTightDeltaPeak spqrSendTightMaxReq 4296 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    (spqrSend_phaseCreditSpec_tight (ptext := ptext) hPts hChain)
    (spqrSendTightCap_groupSpec fineCostModel stBytes ptext)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (by decide)
    henf hram hva

theorem spqrSendTightCap_fitsEnv_cliBudgetLimits
    {stBytes ptext : Bytes}
    (hPts : ValidEncoderPts640 stBytes)
    (hChain : ValidChainParams stBytes) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (SpqrSendTightCapEnv stBytes ptext) :=
  spqrSendTightCap_fitsEnv_1GiB rfl (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hPts hChain

/-! ## `StoresGhost.opened` Encrypt Tight Credit and Group Corollaries -/

def w1CliOpenedTightSendCum
    (ptextLen nameCum fileCap deserCum c_sig c_pk c_st : Nat) : Nat :=
  w1CliOpenedCustomSendCum fineCostModel spqrSendTightDeltaCum
    ptextLen nameCum fileCap deserCum c_sig c_pk c_st

def w1CliOpenedTightSendLive
    (ptextLen fileCap deserLive l_sig l_pk l_st : Nat) : Nat :=
  w1CliOpenedCustomSendLive fineCostModel spqrSendTightDeltaLive
    ptextLen fileCap deserLive l_sig l_pk l_st

def w1CliOpenedTightSendPeak
    (ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st : Nat) : Nat :=
  w1CliOpenedCustomSendPeak fineCostModel
    spqrSendTightDeltaLive spqrSendTightDeltaPeak
    ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st

def w1CliOpenedTightSendMaxReq
    (ptextLen fileCap deserMaxReq r_sig r_pk r_st : Nat) : Nat :=
  w1CliOpenedCustomSendMaxReq spqrSendTightMaxReq
    ptextLen fileCap deserMaxReq r_sig r_pk r_st

theorem w1CliOpenedTightSend_live_le_peak
    {ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk l_st p_st : Nat}
    (hSig : l_sig ≤ p_sig)
    (hPk : l_pk ≤ p_pk)
    (hSt : l_st ≤ p_st) :
    w1CliOpenedTightSendLive ptextLen fileCap deserLive l_sig l_pk l_st ≤
      w1CliOpenedTightSendPeak ptextLen fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st :=
  w1CliOpenedCustomSend_live_le_peak fineCostModel hSig hPk hSt

private theorem fineSmallAlloc_le_of_le_40 {nameCum : Nat} (hNameCum : 9619 ≤ nameCum) :
    ∀ n, 0 < n → n ≤ 40 →
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallAllocCost
        fineCostModel n ≤ nameCum := by
  intro n _ hn40
  have hsm :
      n ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
        fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    omega
  have haff := fineCostModel_modelHyps.smallAlloc_le hsm
  omega

/-- `PhaseCreditSpec fineCostModel` for `StoresGhost.opened` encrypt instantiated with tight `spqr::send` bounds (`4,355,111 / 294,391 / 294,391 / 286,196`).
-/
theorem w1CliOpenedTightSend_fine_phaseCredit
    (B : RunBudgets) (img : Arm64.Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (C : Crypto) (S : SpqrModel) (x : WithStoresEncGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv (w1SessKit B img F peer))
    (ikitEnv : IdentityStoreBudgetEnv (w1IdKit B img F peer))
    (E_send : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (SigNoneGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      SignalMessageNewGhost → Prop)
    (SigSomeGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      SignalMessageNewGhost → Prop)
    (PkCallGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      PreKeyMsgNewCall → Prop)
    {nameCum fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    {c_sig l_sig p_sig r_sig c_pk l_pk p_pk r_pk c_st l_st p_st r_st : Nat}
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hNameCum : 9619 ≤ nameCum)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .sending evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv
        ((w1IdKit B img F peer).trustUpdate StoresGhost.opened.identity x.rem.val k
          .sending (.ok true))
        x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSend : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec fineCostModel (E_send otr.pqrState x.rest)
        spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak spqrSendTightMaxReq)
    (hSigNone : ∀ r sess otr taken g, SigNoneGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hSigSome : ∀ r sess otr taken g, SigSomeGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hPkCap : ∀ r sess otr taken call, PkCallGuard r sess otr taken call →
      preKeyMsgNewDeltaCum call ≤ c_pk ∧
      preKeyMsgNewDeltaLive call ≤ l_pk ∧
      preKeyMsgNewDeltaPeak call ≤ p_pk ∧
      preKeyMsgNewMaxReq call ≤ r_pk)
    (hStoreNone : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome C S uuidTryParse x otr) taken))
        c_st l_st p_st r_st) :
    PhaseCreditSpec fineCostModel
      (WithStoresEncTightEnv scopeKit
        (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
        (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
        C S uuidTryParse x
        (fun r sess otr taken =>
          OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧
              SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken =>
          OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧
              SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken evs =>
          ∃ call, PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs))
      (w1CliOpenedTightSendCum x.ptext.length nameCum fileCap deserCum c_sig c_pk c_st)
      (w1CliOpenedTightSendLive x.ptext.length fileCap deserLive l_sig l_pk l_st)
      (w1CliOpenedTightSendPeak x.ptext.length fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st)
      (w1CliOpenedTightSendMaxReq x.ptext.length fileCap deserMaxReq r_sig r_pk r_st) :=
  w1CliOpenedCustomSend_phaseCredit
    fineCostModel_modelHyps
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    B img F peer C S x DeserEnv peerIdKeyName kitEnv ikitEnv E_send
    SigNoneGuard SigSomeGuard PkCallGuard
    hpeer hremName (fineSmallAlloc_le_of_le_40 hNameCum) hidKeyLen hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hSend hSigNone hSigSome hPkCap hStoreNone hStoreSome

private theorem w1Group_sum_le
    (fs gs g_ld g_sig g_pk g_tr g_sv g_st : Nat) :
    18 * fs + g_ld + (gs + 6 * fs + g_sig) + g_pk + g_tr + g_sv + g_st ≤
      24 * fs + gs + g_ld + g_sig + g_pk + g_tr + g_sv + g_st := by
  omega

/-- `PhaseGroupSpec fineCostModel` for `StoresGhost.opened` encrypt instantiated with `spqrSendTightGroupS`.
-/
theorem w1CliOpenedTightSend_fine_groupSpec
    (B : RunBudgets) (img : Arm64.Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (C : Crypto) (S : SpqrModel) (x : WithStoresEncGhost)
    (kitEnv : SessionStoreBudgetEnv (w1SessKit B img F peer))
    (ikitEnv : IdentityStoreBudgetEnv (w1IdKit B img F peer))
    (E_send : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    {E_sigNone E_sigSome E_pksmNew :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      List AllocEvent → Prop}
    {g_ld g_sig g_pk g_tr g_sv g_st : Nat}
    (hLoad : PhaseGroupSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) g_ld)
    (hSend : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec fineCostModel (E_send otr.pqrState x.rest) spqrSendTightGroupS)
    (hSigNone : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec fineCostModel (E_sigNone r sess otr taken) g_sig)
    (hSigSome : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec fineCostModel (E_sigSome r sess otr taken) g_sig)
    (hPksmNew : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec fineCostModel (E_pksmNew r sess otr taken) g_pk)
    (hTrust : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel
        (ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .sending) g_tr)
    (hSave : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel
        (ikitEnv.savePollEnv
          ((w1IdKit B img F peer).trustUpdate StoresGhost.opened.identity x.rem.val k
            .sending (.ok true))
          x.rem.val k)
        g_sv)
    (hStoreNone : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone C S x otr) taken))
        g_st)
    (hStoreSome : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome C S uuidTryParse x otr) taken))
        g_st) :
    PhaseGroupSpec fineCostModel
      (WithStoresEncTightEnv scopeKit
        (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
        (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
        C S uuidTryParse x
        (fun r sess otr taken =>
          OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length
            (E_sigNone r sess otr taken))
        (fun r sess otr taken =>
          OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length
            (E_sigSome r sess otr taken))
        E_pksmNew)
      (24 * FineScale + spqrSendTightGroupS + g_ld + g_sig + g_pk + g_tr + g_sv + g_st) := by
  have h := withStoresEncTightEnv_groupSpec fineCostModel scopeKit
    (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
    (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
    C S uuidTryParse x
    (E_otrNone := fun r sess otr taken =>
      OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length (E_sigNone r sess otr taken))
    (E_otrSome := fun r sess otr taken =>
      OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length (E_sigSome r sess otr taken))
    hLoad
    (fun r sess otr taken hsc hcur hex =>
      otrEncryptStepEnv_groupSpec fineCostModel
        (hSend r sess otr taken hsc hcur hex) (hSigNone r sess otr taken hsc hcur hex))
    (fun r sess otr taken hsc hcur hex =>
      otrEncryptStepEnv_groupSpec fineCostModel
        (hSend r sess otr taken hsc hcur hex) (hSigSome r sess otr taken hsc hcur hex))
    hPksmNew hTrust hSave hStoreNone hStoreSome
  exact h.mono (w1Group_sum_le FineScale spqrSendTightGroupS g_ld g_sig g_pk g_tr g_sv g_st)

end LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
