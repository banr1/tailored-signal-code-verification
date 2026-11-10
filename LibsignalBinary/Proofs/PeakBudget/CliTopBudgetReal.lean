/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Real-Instance Whole-`main` Peak Budget (`< 90%` / `≤ 1 GiB`)

Instantiates `CliTopBudgetSpec`'s whole-`main` `fineCostModel` budget machinery across all five
concrete CLI callee slots (`W3` `initiate`, `W1` `encrypt`, `W2` `decryptSignal`, canonical-outer
`PreKeySignalMessage::try_from`, and `W4` `decryptPrekey`) with `RecordDeserializeCancelEnv` and
linked `spqr::recv`:
- Under `CliPqRealCallDomain` (canonical-outer pre-key wire via `CliPqxdhInputs` plus
  `SessionRecordCapInDomain`, single-session records with zero `previousSessions`, `DEV-C-PREV`),
  whole-`main` physical RAM is bounded by `965,445,342` B (`89.91%`, `≤ 90%` of `1 GiB`) and
  `VA ≤ 2 ^ 48`.
- With unmodified outer `PksmTryFromSliceEnv` (`204,355,676` B `Δcum`), whole-`main` physical RAM
  is bounded by `1,066,568,753` B (`99.33%`, `≤ 1 GiB`) and `VA ≤ 2 ^ 48`.
- Includes a concrete allocating `recv-prekey` (`3#8`) non-vacuity witness.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal

open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields wirePrekey wireWhisper)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs PqParty PqxdhPartyInSpecDomain pqInitInputs pqRecvInputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open LibsignalBinary.Heap
  (AllocEvent BudgetLimits FitsEnv FitsTrace FreeOnlyEvs)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (CliPqDomainCaps PqPartyBaseKeysCap SessionRecordCapInDomain cliPqDomainCaps_of_pqParty_caps)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (CliMainEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunOpenedEnv CliRunSlotCalleeSpecs CliRunWrapperEnvs
   R3bEnv RecvArmEnv RunArmEnv cliRunOpenedDeltaLive cliRunOpenedDeltaPeak
   cliRunOpenedMaxReq cliRunOpenedTightDeltaCum cliRunOpened_tight_phaseCredit
   fineCostModel_cliRunTightHyps initArmDeltaCum initArmDeltaLive initArmDeltaPeak
   initArmMaxReq pksmSliceCum pksmSliceLive pksmSliceLive_le_peak pksmSliceMaxReq
   pksmSlicePeak r2DeltaLive r2DeltaPeak r2MaxReq r2TightDeltaCum sigSliceCum
   sigSliceLive sigSliceMaxReq sigSlicePeak sigTryFromSlice_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (CliRunTightEnv CliRunTightSpqrCaps cliIo_rd_runFiles_length_le_of_filesBounded
   cliRun1MiBSlotLive cliRun1MiBSlotMaxReq cliRun1MiBSlotPeak
   cliRunSpqrAndInitCaps_of_cliPqInputs r0Opened1MiBCum r0Opened1MiBLive
   r0Opened1MiBMaxReq r0Opened1MiBPeak)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
export LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (CliRunFineSlotSpecs cliInitSlotCumCap cliInitSlotGrpSCap cliInitSlotLiveCap
   cliInitSlotPeakCap cliInitSlotReqCap cliMainTightRamNeedOf cliMainTightStepReserveOf
   cliMainTightVaNeedOf cliMain_fitsEnv_of_runFineBounds cliMain_fitsTrace_of_runFineBounds
   cliRecvPrekeySlotCumCap cliRecvPrekeySlotGrpSCap cliRecvPrekeySlotLiveCap
   cliRecvPrekeySlotPeakCap cliRecvPrekeySlotReqCap cliRecvWhisperSlotCumCap
   cliRecvWhisperSlotGrpSCap cliRecvWhisperSlotLiveCap cliRecvWhisperSlotPeakCap
   cliRecvWhisperSlotReqCap cliRunOfR0_fine_groupSpec cliSendSlotCumCap cliSendSlotGrpSCap
   cliSendSlotLiveCap cliSendSlotPeakCap cliSendSlotReqCap initArmEnv_fine_groupSpec
   pksmTryFromSlice_fine_groupSpec r0OpenedEnv_fine_groupSpec r2Env_fine_groupSpec
   r3aEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (W1SendRealDom W1SendRealParams W1SendRealSlotEnv
   w1SendRealSlot_dcan_singleSlotFineSpec w1SendReal_dcan_caps_le)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (W2RecvWhisperRealDom W2RecvWhisperRealParams W2RecvWhisperRealSlotEnv
   w2RecvWhisperRealSlot_dcan_singleSlotFineSpec w2RecvWhisperReal_dcan_caps_le)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealDom W4RecvPrekeyRealEnv W4RecvPrekeyRealParams w4RecvPrekeyReal_caps_le
   w4RecvPrekeyReal_singleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (fineCostModel_wireLowInterceptHyps sigTryFromCapDeltaGrpS)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (pksmTryFromCapDeltaGrpS)

/-! ## 1. Canonical-Outer PKSM Constants and Whole-`main` Summary -/

/-- `90%` of `1 GiB` (`(2 ^ 30 * 9) / 10 = 966,367,641` B). -/
def cliRealNinetyPctOneGiB : Nat := (cliOneGiB * 9) / 10

-- Canonical-outer `PreKeySignalMessage::try_from`: `103,232,265` B `Δcum`.
def cliRealPksmCumCap : Nat := 103232265
def cliRealPksmLiveCap : Nat := pksmSliceLive msgCapBytes
def cliRealPksmPeakCap : Nat := pksmSlicePeak msgCapBytes
def cliRealPksmReqCap : Nat := pksmSliceMaxReq msgCapBytes
def cliRealPksmGrpSCap : Nat := pksmTryFromCapDeltaGrpS msgCapBytes

/-- Parametric `1 MiB` whole-`run` `Δcum` allowing a custom `pksmCum` alongside the four slot caps. -/
def cliRun1MiBCustomPksmCum (pksmCum initCum encCum decSigCum decPkCum : Nat) : Nat :=
  r0Opened1MiBCum +
    max (initArmDeltaCum (pathDeltaCum 26 16) 1637 initCum)
      (max (r2TightDeltaCum encCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + decSigCum)
          (pksmCum + decPkCum)))

/-- Parametric `1 MiB` whole-`run` `Δlive` allowing a custom `pksmLive`. -/
def cliRun1MiBCustomPksmLive (pksmLive initLive encLive decSigLive decPkLive : Nat) : Nat :=
  r0Opened1MiBLive +
    max (initArmDeltaLive (pathDeltaLive 26 16) initLive)
      (max (r2DeltaLive fineCostModel encLive sessionCapBytes)
        (max (sigSliceLive msgCapBytes + decSigLive)
          (pksmLive + decPkLive)))

/-- Parametric `1 MiB` whole-`run` `Δpeak` allowing custom `(pksmLive, pksmPeak)`. -/
def cliRun1MiBCustomPksmPeak
    (pksmLive pksmPeak initPeak encLive encPeak decSigPeak decPkPeak : Nat) : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      max (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 initPeak)
        (max (r2DeltaPeak fineCostModel encLive encPeak sessionCapBytes)
          (max (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + decSigPeak))
            (max pksmPeak (pksmLive + decPkPeak)))))

/-- Parametric `1 MiB` whole-`run` `maxReq` allowing a custom `pksmMaxReq`. -/
def cliRun1MiBCustomPksmMaxReq
    (pksmMaxReq initMaxReq encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max r0Opened1MiBMaxReq
    (max (initArmMaxReq (pathMaxReq 26 16) 1637 initMaxReq)
      (max (r2MaxReq encMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) decSigMaxReq)
          (max pksmMaxReq decPkMaxReq))))

/-- Parametric whole-`run` scaled group count `grpS` allowing a custom `g_pksm`. -/
def cliRunOpenedCustomPksmGrpS
    (stdinCap g_pksm g_init g_enc g_decSig g_decPk : Nat) : Nat :=
  15 * FineScale +
    max (84 * FineScale + g_init)
      (max (g_enc + 3 * FineScale)
        (max (sigTryFromCapDeltaGrpS stdinCap + g_decSig)
          (g_pksm + g_decPk)))

def cliRealRunCumCap : Nat :=
  cliRun1MiBCustomPksmCum cliRealPksmCumCap
    cliInitSlotCumCap cliSendSlotCumCap
    cliRecvWhisperSlotCumCap cliRecvPrekeySlotCumCap

def cliRealUnmodPksmRunCumCap : Nat :=
  cliRun1MiBCustomPksmCum (pksmSliceCum msgCapBytes)
    cliInitSlotCumCap cliSendSlotCumCap
    cliRecvWhisperSlotCumCap cliRecvPrekeySlotCumCap

def cliRealRunLiveCap : Nat :=
  cliRun1MiBSlotLive
    cliInitSlotLiveCap cliSendSlotLiveCap
    cliRecvWhisperSlotLiveCap cliRecvPrekeySlotLiveCap

def cliRealRunPeakCap : Nat :=
  cliRun1MiBSlotPeak
    cliInitSlotPeakCap cliSendSlotLiveCap cliSendSlotPeakCap
    cliRecvWhisperSlotPeakCap cliRecvPrekeySlotPeakCap

def cliRealRunReqCap : Nat :=
  cliRun1MiBSlotMaxReq
    cliInitSlotReqCap cliSendSlotReqCap
    cliRecvWhisperSlotReqCap cliRecvPrekeySlotReqCap

def cliRealRunGrpSCap : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes cliRealPksmGrpSCap
    cliInitSlotGrpSCap cliSendSlotGrpSCap
    cliRecvWhisperSlotGrpSCap cliRecvPrekeySlotGrpSCap

/-- Whole-`main` `stepReserve` bound (`244,277,248` B) for the canonical-outer PKSM profile. -/
def cliRealMainStepReserve : Nat :=
  cliMainTightStepReserveOf cliRealRunReqCap cliRealRunGrpSCap

/-- Closed-numeral check that canonical-outer PKSM (`≤ 90%` = `965,445,342 ≤ 966,367,641`,
`≤ 1 GiB`, `VA ≤ 2 ^ 48`) and unmodified-PKSM (`1,066,568,753 ≤ 1 GiB`, `VA ≤ 2 ^ 48`) profiles fit. -/
theorem cliRealR2_fits_90pct_and_oneGiB :
    cliMainTightRamNeedOf cliRealRunCumCap cliRealRunLiveCap cliRealRunPeakCap
      cliRealRunReqCap cliRealRunGrpSCap ≤ cliRealNinetyPctOneGiB ∧
    cliMainTightRamNeedOf cliRealRunCumCap cliRealRunLiveCap cliRealRunPeakCap
      cliRealRunReqCap cliRealRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightVaNeedOf cliRealRunCumCap cliRealRunLiveCap cliRealRunPeakCap
      cliRealRunReqCap cliRealRunGrpSCap ≤ 2 ^ 48 ∧
    cliMainTightRamNeedOf cliRealUnmodPksmRunCumCap cliRealRunLiveCap cliRealRunPeakCap
      cliRealRunReqCap cliRealRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightVaNeedOf cliRealUnmodPksmRunCumCap cliRealRunLiveCap cliRealRunPeakCap
      cliRealRunReqCap cliRealRunGrpSCap ≤ 2 ^ 48 := by
  decide

/-! ## 2. `CliPqxdhInputs` Domain Bridges -/

/-- Reachable CLI PQXDH call-domain bundle at `1 MiB` (`msgCapBytes`) / `2 MiB` (`sessionCapBytes`),
packaging `CliPqxdhInputs P g.i` with `SessionRecordCapInDomain`, `PqPartyBaseKeysCap`, and
`parseArgs` agreement. -/
def CliPqRealCallDomain (P : PEParams) (g : RunCall) : Prop :=
  ∃ party : PqParty,
    PqxdhPartyInSpecDomain P party ∧
    ((party.session = none ∧ ∃ b t, g.i = pqInitInputs P party b t) ∨
     (∃ m r, m.length < 2 ^ 32 ∧ g.i = pqSendInputs P party m r) ∨
     (∃ c rc, c.length < 2 ^ 32 ∧ g.i = pqRecvInputs P party (wireWhisper :: c) rc) ∨
     (∃ (m : PreKeyMessageFields) (rc : BitVec 256),
       m.inner.length + 2048 < 2 ^ 32 ∧ g.i = pqRecvInputs P party (wirePrekey :: m.bytes) rc) ∨
     (∃ c rc, c.length < 2 ^ 32 ∧ c.head? ≠ some wireWhisper ∧ c.head? ≠ some wirePrekey ∧
       g.i = pqRecvInputs P party c rc)) ∧
    SessionRecordCapInDomain P sessionCapBytes ∧
    PqPartyBaseKeysCap sessionCapBytes party ∧
    g.i.stdin.length ≤ msgCapBytes ∧
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
    (∀ peer dir, g.c = .init peer dir → dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637))

theorem CliPqRealCallDomain.toCliPqxdhInputs {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g) :
    CliPqxdhInputs P g.i := by
  rcases hd with ⟨party, hwf, hcase, _⟩
  exact ⟨party, hwf, hcase⟩

/-- Derives `CliPqDomainCaps msgCapBytes sessionCapBytes g.i` from `CliPqRealCallDomain P g`. -/
theorem CliPqRealCallDomain.toCliPqDomainCaps {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g) :
    CliPqDomainCaps msgCapBytes sessionCapBytes g.i := by
  rcases hd with ⟨party, hwf, hcase, hsess, hbk, hstdin, _⟩
  have h := cliPqDomainCaps_of_pqParty_caps hwf hsess hbk hstdin hcase
  rwa [Nat.max_self] at h

theorem CliPqRealCallDomain.parseArgs_eq {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g) :
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c := by
  rcases hd with ⟨_, _, _, _, _, _, hparse, _⟩
  exact hparse

/-- Derives `CliRunTightSpqrCaps g` from `CliPqRealCallDomain P g`. -/
theorem CliPqRealCallDomain.toCliRunTightSpqrCaps {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g) :
    CliRunTightSpqrCaps g := by
  have hi := hd.toCliPqxdhInputs
  exact cliRunSpqrAndInitCaps_of_cliPqInputs hi hd.parseArgs_eq (by
    rcases hd with ⟨_, _, _, _, _, _, _, hinit⟩
    exact hinit)

/-- Derives `FilesOkPeer Slots.scopeKit` (`= DeserializeScopeP_Q NonEmptyV1Q`) on `runFiles g.i`
for any call in `CliPqRealCallDomain P g` targeting `peer` (`PqxdhPartyInSpecDomain` encodes
single-session records with zero `previousSessions`, `DEV-C-PREV`). -/
theorem CliPqRealCallDomain.filesOkPeer_scopeKit
    {P : PEParams} {g : RunCall} {peer : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    (hd : CliPqRealCallDomain P g)
    (hpeer : CryptoVerification.SignalSession.Cli.RunCompose.callPeer g.c = some peer) :
    CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer
      CryptoVerification.SignalSession.Cli.Slots.scopeKit
      (runFiles g.i)
      (CryptoVerification.SignalSession.Cli.RunCompose.addrValOf peer) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.filesOkPeer_scopeKit_of_cliPqxdhInputs
    hd.toCliPqxdhInputs hd.parseArgs_eq hpeer

/-- Any peer session read `StoresGhost.opened.sessions.get cliIo.rd (runFiles g.i) ... = .ok bs`
under `CliPqRealCallDomain P g` is either empty (`bs = []`) or decodes a `DeserializeScopeP_Q NonEmptyV1Q`
record `r` (`bs = encodeRecord r`) whose `sessDeserEvents r` trace belongs to
`RecordDeserializeCancelEnv bs`, `SessDeserSetBEnv bs`, and `SessDeserSetAEnv bs`. -/
theorem CliPqRealCallDomain.sessGet_recordDeserializeCancelEnv
    {P : PEParams} {g : RunCall} {peer : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    {bs : List (BitVec 8)}
    (hd : CliPqRealCallDomain P g)
    (hpeer : CryptoVerification.SignalSession.Cli.RunCompose.callPeer g.c = some peer)
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles g.i)
      (CryptoVerification.SignalSession.Cli.addressText
        (CryptoVerification.SignalSession.Cli.RunCompose.addrValOf peer)) = .ok bs) :
    (bs = [] ∧
      LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv bs []) ∨
      ∃ r : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)),
        bs = CryptoVerification.E2E.Record.encodeRecord r ∧
        Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q r ∧
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv bs
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r) ∧
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.SessDeserSetBEnv bs
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r) ∧
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.SessDeserSetAEnv bs
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r) := by
  rcases LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.cliPqxdhInputs_sessGet_empty_or_scopeKit
      hd.toCliPqxdhInputs hd.parseArgs_eq hpeer hget with
    rfl | ⟨r, hbs, hr, hB, hA⟩
  · exact Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact Or.inr ⟨r, hbs, hr, Or.inr ⟨r, hbs, hr, rfl⟩, hB, hA⟩

/-- Combines `cliPqxdhInputs_sessGet_dcan_and_profiles` on `CliPqRealCallDomain P g` with
`cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight` (`17,495,245` B `Δcum`) and
`cliSessLoadPollEnv_dcan_fine_groupSpec` (`347,214,604` `grpS`) at the CLI `LoadPoll` site. -/
theorem CliPqRealCallDomain.sessLoadPoll_dcan_credit_and_groups
    {P : PEParams} {g : RunCall} {peer : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    {bs : List (BitVec 8)}
    (hd : CliPqRealCallDomain P g)
    (hpeer : CryptoVerification.SignalSession.Cli.RunCompose.callPeer g.c = some peer)
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles g.i)
      (CryptoVerification.SignalSession.Cli.addressText
        (CryptoVerification.SignalSession.Cli.RunCompose.addrValOf peer)) = .ok bs)
    {rdL : ReadRule} {filesL : FsFiles}
    {dirL : CryptoVerification.SignalSession.Cli.DirGhost}
    {peerL : CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : CliDomainCaps.DirDomainCaps maxDir maxEntries maxVal dirL)
    (hdir : maxDir ≤ 64)
    (hpeerLen : peerL.name.bytes.length ≤ 40)
    (hcap : ∀ bsL, rdL filesL (pathOf dirL.path
      (CryptoVerification.SignalSession.Cli.addressText peerL.val)) = .ok bsL → bsL.length ≤ fileCap)
    (hfc : max maxVal fileCap ≤ 2097152) :
    ((bs = [] ∧
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv bs []) ∨
      ∃ r : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)),
        bs = CryptoVerification.E2E.Record.encodeRecord r ∧
        CryptoVerification.SignalSession.Cli.Slots.scopeKit r ∧
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.SessDeserializeCancelEnv r
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r) ∧
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv bs
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r) ∧
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.SessDeserSetBEnv bs
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r) ∧
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.SessDeserSetAEnv bs
          (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget.sessDeserEvents r)) ∧
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec.CliSessLoadPollEnv rdL
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
        filesL dirL peerL)
      LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.sessLoadPollCancel2MiBCum
      LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.loadPollCancel2MiBLive
      LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.loadPollCancel2MiBPeak
      LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.loadPollCancel2MiBMaxReq ∧
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec.CliSessLoadPollEnv rdL
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
        filesL dirL peerL)
      LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.cliSessLoadPollCancelGrpS :=
  ⟨LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.cliPqxdhInputs_sessGet_dcan_and_profiles
     hd.toCliPqxdhInputs hd.parseArgs_eq hpeer hget,
   LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.cliSessLoadPollEnv_dcan_2MiB_fine_phaseCredit_tight
     hdc hdir hpeerLen hcap hfc,
   LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.cliSessLoadPollEnv_dcan_fine_groupSpec
     filesL dirL peerL⟩

/-! ## 3. Five-Callee `fineCostModel` Bundle (`W1`–`W4` + Canonical-Outer `PksmEnv`) & Whole-`run` Specs -/

/-- Five-callee `fineCostModel` credit and group bundle for `CliRunCalleeEnvs`
(`initiate`, `encrypt`, `decryptSignal`, `pksmTryFrom`, `decryptPrekey`). -/
structure CliRealCalleeFineSpecs (E : CliRunCalleeEnvs) where
  (initCum initLive initPeak initMaxReq initGrpS : Nat)
  init_spec : PhaseCreditSpec fineCostModel E.initEnv initCum initLive initPeak initMaxReq
  init_lp : initLive ≤ initPeak
  init_grp : PhaseGroupSpec fineCostModel E.initEnv initGrpS
  (encCum encLive encPeak encMaxReq encGrpS : Nat)
  enc_spec : PhaseCreditSpec fineCostModel E.encEnv encCum encLive encPeak encMaxReq
  enc_lp : encLive ≤ encPeak
  enc_grp : PhaseGroupSpec fineCostModel E.encEnv encGrpS
  (decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat)
  decSig_spec : PhaseCreditSpec fineCostModel E.decSigEnv decSigCum decSigLive decSigPeak decSigMaxReq
  decSig_lp : decSigLive ≤ decSigPeak
  decSig_grp : PhaseGroupSpec fineCostModel E.decSigEnv decSigGrpS
  (pksmCum pksmLive pksmPeak pksmMaxReq pksmGrpS : Nat)
  pksm_spec : ∀ rest, rest.length ≤ msgCapBytes →
    PhaseCreditSpec fineCostModel (E.pksmEnv rest) pksmCum pksmLive pksmPeak pksmMaxReq
  pksm_lp : pksmLive ≤ pksmPeak
  pksm_grp : ∀ rest, rest.length ≤ msgCapBytes →
    PhaseGroupSpec fineCostModel (E.pksmEnv rest) pksmGrpS
  (decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat)
  decPk_spec : PhaseCreditSpec fineCostModel E.decPkEnv decPkCum decPkLive decPkPeak decPkMaxReq
  decPk_lp : decPkLive ≤ decPkPeak
  decPk_grp : PhaseGroupSpec fineCostModel E.decPkEnv decPkGrpS

def CliRealCalleeFineSpecs.toSlotCalleeSpecs {E : CliRunCalleeEnvs}
    (SE : CliRealCalleeFineSpecs E) :
    CliRunSlotCalleeSpecs fineCostModel E msgCapBytes where
  initCum := SE.initCum
  initLive := SE.initLive
  initPeak := SE.initPeak
  initMaxReq := SE.initMaxReq
  init_spec := SE.init_spec
  init_lp := SE.init_lp
  encCum := SE.encCum
  encLive := SE.encLive
  encPeak := SE.encPeak
  encMaxReq := SE.encMaxReq
  enc_spec := SE.enc_spec
  enc_lp := SE.enc_lp
  decSigCum := SE.decSigCum
  decSigLive := SE.decSigLive
  decSigPeak := SE.decSigPeak
  decSigMaxReq := SE.decSigMaxReq
  decSig_spec := SE.decSig_spec
  decSig_lp := SE.decSig_lp
  pksmCum := SE.pksmCum
  pksmLive := SE.pksmLive
  pksmPeak := SE.pksmPeak
  pksmMaxReq := SE.pksmMaxReq
  pksm_spec := SE.pksm_spec
  pksm_lp := SE.pksm_lp
  decPkCum := SE.decPkCum
  decPkLive := SE.decPkLive
  decPkPeak := SE.decPkPeak
  decPkMaxReq := SE.decPkMaxReq
  decPk_spec := SE.decPk_spec
  decPk_lp := SE.decPk_lp

/-- Lifts a 4-slot `CliRunFineSlotSpecs W` together with a custom `PksmEnv` into `CliRealCalleeFineSpecs`. -/
def CliRealCalleeFineSpecs.ofWrapperWithPksm
    {W : CliRunWrapperEnvs} (SW : CliRunFineSlotSpecs W)
    {PksmEnv : List (BitVec 8) → List AllocEvent → Prop}
    {pksmCum pksmLive pksmPeak pksmMaxReq pksmGrpS : Nat}
    (hpksm_spec : ∀ rest, rest.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (PksmEnv rest) pksmCum pksmLive pksmPeak pksmMaxReq)
    (hpksm_lp : pksmLive ≤ pksmPeak)
    (hpksm_grp : ∀ rest, rest.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (PksmEnv rest) pksmGrpS) :
    CliRealCalleeFineSpecs
      { initEnv := W.initEnv
        encEnv := W.encEnv
        decSigEnv := W.decSigEnv
        pksmEnv := PksmEnv
        decPkEnv := W.decPkEnv } where
  initCum := SW.initCum
  initLive := SW.initLive
  initPeak := SW.initPeak
  initMaxReq := SW.initMaxReq
  initGrpS := SW.initGrpS
  init_spec := SW.init_spec
  init_lp := SW.init_lp
  init_grp := SW.init_grp
  encCum := SW.encCum
  encLive := SW.encLive
  encPeak := SW.encPeak
  encMaxReq := SW.encMaxReq
  encGrpS := SW.encGrpS
  enc_spec := SW.enc_spec
  enc_lp := SW.enc_lp
  enc_grp := SW.enc_grp
  decSigCum := SW.decSigCum
  decSigLive := SW.decSigLive
  decSigPeak := SW.decSigPeak
  decSigMaxReq := SW.decSigMaxReq
  decSigGrpS := SW.decSigGrpS
  decSig_spec := SW.decSig_spec
  decSig_lp := SW.decSig_lp
  decSig_grp := SW.decSig_grp
  pksmCum := pksmCum
  pksmLive := pksmLive
  pksmPeak := pksmPeak
  pksmMaxReq := pksmMaxReq
  pksmGrpS := pksmGrpS
  pksm_spec := hpksm_spec
  pksm_lp := hpksm_lp
  pksm_grp := hpksm_grp
  decPkCum := SW.decPkCum
  decPkLive := SW.decPkLive
  decPkPeak := SW.decPkPeak
  decPkMaxReq := SW.decPkMaxReq
  decPkGrpS := SW.decPkGrpS
  decPk_spec := SW.decPk_spec
  decPk_lp := SW.decPk_lp
  decPk_grp := SW.decPk_grp

/-- Lifts a 4-slot `CliRunFineSlotSpecs W` directly to `W.toCalleeEnvs` using unmodified
`PksmTryFromSliceEnv` (`204,355,676` B `Δcum`). -/
def CliRealCalleeFineSpecs.ofWrapperUnmodPksm
    {W : CliRunWrapperEnvs} (SW : CliRunFineSlotSpecs W) :
    CliRealCalleeFineSpecs W.toCalleeEnvs :=
  CliRealCalleeFineSpecs.ofWrapperWithPksm SW
    (fun _ hrest =>
      CliRunArmsPeak.pksmTryFromSlice_phaseCredit fineCostModel_modelHyps
        fineCostModel_wireLowInterceptHyps hrest)
    (pksmSliceLive_le_peak msgCapBytes)
    (fun _ hrest => pksmTryFromSlice_fine_groupSpec hrest)

/-- Numerical cap predicate on `CliRealCalleeFineSpecs E` (20 slot caps from `CliTopBudgetSpec` plus 5 canonical-outer `PksmEnv` caps). -/
def CliRealR2CalleeCaps {E : CliRunCalleeEnvs} (SE : CliRealCalleeFineSpecs E) : Prop :=
  SE.initCum ≤ cliInitSlotCumCap ∧
  SE.initLive ≤ cliInitSlotLiveCap ∧
  SE.initPeak ≤ cliInitSlotPeakCap ∧
  SE.initMaxReq ≤ cliInitSlotReqCap ∧
  SE.initGrpS ≤ cliInitSlotGrpSCap ∧
  SE.encCum ≤ cliSendSlotCumCap ∧
  SE.encLive ≤ cliSendSlotLiveCap ∧
  SE.encPeak ≤ cliSendSlotPeakCap ∧
  SE.encMaxReq ≤ cliSendSlotReqCap ∧
  SE.encGrpS ≤ cliSendSlotGrpSCap ∧
  SE.decSigCum ≤ cliRecvWhisperSlotCumCap ∧
  SE.decSigLive ≤ cliRecvWhisperSlotLiveCap ∧
  SE.decSigPeak ≤ cliRecvWhisperSlotPeakCap ∧
  SE.decSigMaxReq ≤ cliRecvWhisperSlotReqCap ∧
  SE.decSigGrpS ≤ cliRecvWhisperSlotGrpSCap ∧
  SE.pksmCum ≤ cliRealPksmCumCap ∧
  SE.pksmLive ≤ cliRealPksmLiveCap ∧
  SE.pksmPeak ≤ cliRealPksmPeakCap ∧
  SE.pksmMaxReq ≤ cliRealPksmReqCap ∧
  SE.pksmGrpS ≤ cliRealPksmGrpSCap ∧
  SE.decPkCum ≤ cliRecvPrekeySlotCumCap ∧
  SE.decPkLive ≤ cliRecvPrekeySlotLiveCap ∧
  SE.decPkPeak ≤ cliRecvPrekeySlotPeakCap ∧
  SE.decPkMaxReq ≤ cliRecvPrekeySlotReqCap ∧
  SE.decPkGrpS ≤ cliRecvPrekeySlotGrpSCap

/-- Companion numerical cap predicate for `CliRunFineSlotSpecs W` (`unmod pksm`, 20 slot caps). -/
def CliRealUnmodPksmSlotCaps {W : CliRunWrapperEnvs} (SW : CliRunFineSlotSpecs W) : Prop :=
  SW.initCum ≤ cliInitSlotCumCap ∧
  SW.initLive ≤ cliInitSlotLiveCap ∧
  SW.initPeak ≤ cliInitSlotPeakCap ∧
  SW.initMaxReq ≤ cliInitSlotReqCap ∧
  SW.initGrpS ≤ cliInitSlotGrpSCap ∧
  SW.encCum ≤ cliSendSlotCumCap ∧
  SW.encLive ≤ cliSendSlotLiveCap ∧
  SW.encPeak ≤ cliSendSlotPeakCap ∧
  SW.encMaxReq ≤ cliSendSlotReqCap ∧
  SW.encGrpS ≤ cliSendSlotGrpSCap ∧
  SW.decSigCum ≤ cliRecvWhisperSlotCumCap ∧
  SW.decSigLive ≤ cliRecvWhisperSlotLiveCap ∧
  SW.decSigPeak ≤ cliRecvWhisperSlotPeakCap ∧
  SW.decSigMaxReq ≤ cliRecvWhisperSlotReqCap ∧
  SW.decSigGrpS ≤ cliRecvWhisperSlotGrpSCap ∧
  SW.decPkCum ≤ cliRecvPrekeySlotCumCap ∧
  SW.decPkLive ≤ cliRecvPrekeySlotLiveCap ∧
  SW.decPkPeak ≤ cliRecvPrekeySlotPeakCap ∧
  SW.decPkMaxReq ≤ cliRecvPrekeySlotReqCap ∧
  SW.decPkGrpS ≤ cliRecvPrekeySlotGrpSCap

theorem r3bEnv_of_pksm_fine_groupSpec {PksmEnv DecPkEnv : List AllocEvent → Prop}
    {g_pksm g_decPk : Nat}
    (hpksm : PhaseGroupSpec fineCostModel PksmEnv g_pksm)
    (hdec : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel (R3bEnv PksmEnv DecPkEnv) (g_pksm + g_decPk) := by
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((hdec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _)))).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or (hpksm.seq htail)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem recvArmEnv_customPksm_fine_groupSpec
    {stdin : List (BitVec 8)}
    {DecSigEnv : List AllocEvent → Prop}
    {PksmEnv : List (BitVec 8) → List AllocEvent → Prop}
    {DecPkEnv : List AllocEvent → Prop}
    {stdinCap g_decSig g_pksm g_decPk : Nat}
    (hstdin : stdin.length ≤ stdinCap)
    (hdecSig : PhaseGroupSpec fineCostModel DecSigEnv g_decSig)
    (hpksm : ∀ rest, rest.length ≤ stdinCap → PhaseGroupSpec fineCostModel (PksmEnv rest) g_pksm)
    (hdecPk : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel (RecvArmEnv stdin DecSigEnv PksmEnv DecPkEnv)
      (max (sigTryFromCapDeltaGrpS stdinCap + g_decSig) (g_pksm + g_decPk)) := by
  unfold RecvArmEnv
  rcases stdin with _ | ⟨b, rest⟩
  · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  · have hrest : rest.length ≤ stdinCap := Nat.le_of_succ_le hstdin
    by_cases hb2 : b = 2#8
    · simp only [hb2, ↓reduceIte]
      exact (r3aEnv_fine_groupSpec hrest hdecSig).mono (Nat.le_max_left _ _)
    · simp only [hb2, ↓reduceIte]
      by_cases hb3 : b = 3#8
      · simp only [hb3, ↓reduceIte]
        exact (r3bEnv_of_pksm_fine_groupSpec (hpksm rest hrest) hdecPk).mono
          (Nat.le_max_right _ _)
      · simp only [hb3, ↓reduceIte]
        exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

/-- Whole-`run` `PhaseGroupSpec fineCostModel` for `CliRunOpenedEnv cliIo.rd (E g) wireOutCap g` with custom `PksmEnv`. -/
theorem cliRunOpened_real_fine_groupSpec
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall} {wireOutCap : Nat}
    (SE : CliRealCalleeFineSpecs (E g))
    (hstdin : g.i.stdin.length ≤ msgCapBytes) :
    PhaseGroupSpec fineCostModel (CliRunOpenedEnv cliIo.rd (E g) wireOutCap g)
      (cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
        SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS) := by
  have harm : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (E g) wireOutCap g.i.stdin g.c)
      (max (84 * FineScale + SE.initGrpS)
        (max (SE.encGrpS + 3 * FineScale)
          (max (sigTryFromCapDeltaGrpS msgCapBytes + SE.decSigGrpS)
            (SE.pksmGrpS + SE.decPkGrpS)))) := by
    cases g.c with
    | keygen _ _ =>
      exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | init _ dir =>
      exact (initArmEnv_fine_groupSpec cliIo.rd (runFiles g.i) dir SE.init_grp).mono
        (Nat.le_max_left _ _)
    | send _ =>
      exact (r2Env_fine_groupSpec wireOutCap SE.enc_grp).mono
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    | recv _ =>
      exact (recvArmEnv_customPksm_fine_groupSpec hstdin SE.decSig_grp SE.pksm_grp SE.decPk_grp).mono
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  exact cliRunOfR0_fine_groupSpec (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm

/-- Whole-`run` `1 MiB` `PhaseCreditSpec fineCostModel` for `CliRunOpenedEnv cliIo.rd (E g) sessionCapBytes g` with custom `PksmEnv`. -/
theorem cliRunOpened_real_1MiB_fine_phaseCredit
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (SE : CliRealCalleeFineSpecs (E g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g) :
    PhaseCreditSpec fineCostModel (CliRunOpenedEnv cliIo.rd (E g) sessionCapBytes g)
      (cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum)
      (cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive)
      (cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
        SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak)
      (cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
        SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq) := by
  have h := cliRunOpened_tight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
    fineCostModel_wireLowInterceptHyps SE.toSlotCalleeSpecs sessionCapBytes
    hcaps.stdin_le
    (fun bs hrd => cliIo_rd_runFiles_length_le_of_filesBounded hcaps.files_bounded _ bs hrd)
    hspqr.init_caps
  exact h

private theorem max4_mono {a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (ha : a1 ≤ a2) (hb : b1 ≤ b2) (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    max a1 (max b1 (max c1 d1)) ≤ max a2 (max b2 (max c2 d2)) :=
  Nat.max_le.mpr
    ⟨Nat.le_trans ha (Nat.le_max_left _ _),
     Nat.le_trans
       (Nat.max_le.mpr
         ⟨Nat.le_trans hb (Nat.le_max_left _ _),
          Nat.le_trans
            (Nat.max_le.mpr
              ⟨Nat.le_trans hc (Nat.le_max_left _ _),
               Nat.le_trans hd (Nat.le_max_right _ _)⟩)
            (Nat.le_max_right _ _)⟩)
       (Nat.le_max_right _ _)⟩

private theorem cliRealRun_bounds_mono {E : CliRunCalleeEnvs} {SE : CliRealCalleeFineSpecs E}
    (hCaps : CliRealR2CalleeCaps SE) :
    cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRealRunCumCap ∧
    cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRealRunLiveCap ∧
    cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
      SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤ cliRealRunPeakCap ∧
    cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
      SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤ cliRealRunReqCap ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤ cliRealRunGrpSCap := by
  rcases hCaps with
    ⟨hic, hil, hip, hir, hig,
     hec, hel, hep, her, heg,
     hsc, hsl, hsp, hsr, hsg,
     hkc, hkl, hkp, hkr, hkg,
     hpc, hpl, hpp, hpr, hpg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cliRun1MiBCustomPksmCum, cliRealRunCumCap, initArmDeltaCum, r2TightDeltaCum]
    exact Nat.add_le_add_left (max4_mono (by omega) (by omega) (by omega) (by omega)) _
  · simp only [cliRun1MiBCustomPksmLive, cliRealRunLiveCap, cliRun1MiBSlotLive,
      cliRealPksmLiveCap, initArmDeltaLive, r2DeltaLive] at hkl ⊢
    exact Nat.add_le_add_left (max4_mono (by omega) (by omega) (by omega) (by omega)) _
  · unfold cliRun1MiBCustomPksmPeak cliRealRunPeakCap cliRun1MiBSlotPeak
    unfold cliRealPksmLiveCap at hkl
    unfold cliRealPksmPeakCap at hkp
    have hp_init :
        initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SE.initPeak ≤
          initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637
            cliInitSlotPeakCap := by
      unfold initArmDeltaPeak
      have h1 :
          max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
            (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + SE.initPeak) ≤
          max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
            (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + cliInitSlotPeakCap) :=
        Nat.max_le.mpr
          ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hip _) (Nat.le_max_right _ _)⟩
      exact Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)⟩
    have hp_enc :
        r2DeltaPeak fineCostModel SE.encLive SE.encPeak sessionCapBytes ≤
          r2DeltaPeak fineCostModel cliSendSlotLiveCap cliSendSlotPeakCap
            sessionCapBytes := by
      unfold r2DeltaPeak
      exact Nat.max_le.mpr
        ⟨Nat.le_trans hep (Nat.le_max_left _ _),
         Nat.le_trans (Nat.add_le_add_right hel _) (Nat.le_max_right _ _)⟩
    have hp_sig :
        max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SE.decSigPeak) ≤
          max (sigSlicePeak msgCapBytes)
            (sigSliceLive msgCapBytes + cliRecvWhisperSlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hsp _) (Nat.le_max_right _ _)⟩
    have hp_pk :
        max SE.pksmPeak (SE.pksmLive + SE.decPkPeak) ≤
          max (pksmSlicePeak msgCapBytes)
            (pksmSliceLive msgCapBytes + cliRecvPrekeySlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_trans hkp (Nat.le_max_left _ _),
         Nat.le_trans (Nat.add_le_add hkl hpp) (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (Nat.add_le_add_left (max4_mono hp_init hp_enc hp_sig hp_pk) _)
         (Nat.le_max_right _ _)⟩
  · unfold cliRun1MiBCustomPksmMaxReq cliRealRunReqCap cliRun1MiBSlotMaxReq initArmMaxReq r2MaxReq
    unfold cliRealPksmReqCap at hkr
    have hr_init :
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) SE.initMaxReq) ≤
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) cliInitSlotReqCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans
           (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hir (Nat.le_max_right _ _)⟩)
           (Nat.le_max_right _ _)⟩
    have hr_enc :
        max SE.encMaxReq (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) ≤
          max cliSendSlotReqCap (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) :=
      Nat.max_le.mpr ⟨Nat.le_trans her (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    have hr_sig :
        max (sigSliceMaxReq msgCapBytes) SE.decSigMaxReq ≤
          max (sigSliceMaxReq msgCapBytes) cliRecvWhisperSlotReqCap :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hsr (Nat.le_max_right _ _)⟩
    have hr_pk :
        max SE.pksmMaxReq SE.decPkMaxReq ≤
          max (pksmSliceMaxReq msgCapBytes) cliRecvPrekeySlotReqCap :=
      Nat.max_le.mpr
        ⟨Nat.le_trans hkr (Nat.le_max_left _ _), Nat.le_trans hpr (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (max4_mono hr_init hr_enc hr_sig hr_pk) (Nat.le_max_right _ _)⟩
  · unfold cliRunOpenedCustomPksmGrpS cliRealRunGrpSCap
    exact Nat.add_le_add_left
      (max4_mono
        (Nat.add_le_add_left hig _)
        (Nat.add_le_add_right heg _)
        (Nat.add_le_add_left hsg _)
        (Nat.add_le_add hkg hpg)) _

/-! ## 4. Parametric Whole-`main` `FitsTrace` and `FitsEnv` Corollaries -/

private theorem cliMainDeltaCum_tight_mono_priv {c1 c2 d1 d2 maxDir maxName : Nat}
    (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    CliMainPeakSpec.cliMainDeltaCum_tight c1 d1 maxDir maxName ≤
      CliMainPeakSpec.cliMainDeltaCum_tight c2 d2 maxDir maxName := by
  unfold CliMainPeakSpec.cliMainDeltaCum_tight
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_left hc _) (Nat.mul_le_mul_right _ hd))
    _

private theorem cliMainDeltaLive_le_tightPeak_priv
    {stdinCap fileCap l1 l2 p2 maxDir maxName : Nat} (hl : l1 ≤ l2) :
    CliMainPeakSpec.cliMainDeltaLive_tight stdinCap fileCap l1 ≤
      CliMainPeakSpec.cliMainDeltaPeak_tight stdinCap fileCap l2 p2 maxDir maxName := by
  unfold CliMainPeakSpec.cliMainDeltaLive_tight CliMainPeakSpec.cliMainDeltaPeak_tight
  have h1 : l1 ≤ max p2 (l2 + CliMainPeakSpec.m5DirStepDeltaPeak maxDir maxName) :=
    Nat.le_trans hl (Nat.le_trans (Nat.le_add_right l2 _) (Nat.le_max_right _ _))
  exact Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)

private theorem cliMainDeltaPeak_tight_mono_priv
    {stdinCap fileCap l1 l2 p1 p2 maxDir maxName : Nat}
    (hl : l1 ≤ l2) (hp : p1 ≤ p2) :
    CliMainPeakSpec.cliMainDeltaPeak_tight stdinCap fileCap l1 p1 maxDir maxName ≤
      CliMainPeakSpec.cliMainDeltaPeak_tight stdinCap fileCap l2 p2 maxDir maxName := by
  unfold CliMainPeakSpec.cliMainDeltaPeak_tight
  have hinner :
      max p1 (l1 + CliMainPeakSpec.m5DirStepDeltaPeak maxDir maxName) ≤
        max p2 (l2 + CliMainPeakSpec.m5DirStepDeltaPeak maxDir maxName) :=
    Nat.max_le.mpr
      ⟨Nat.le_trans hp (Nat.le_max_left _ _),
       Nat.le_trans (Nat.add_le_add_right hl _) (Nat.le_max_right _ _)⟩
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans (Nat.add_le_add_left hinner _) (Nat.le_max_right _ _)⟩

private theorem cliMainMaxReq_mono_priv {stdinCap fileCap r1 r2 maxDir maxName : Nat}
    (hr : r1 ≤ r2) :
    CliMainPeakSpec.cliMainMaxReq stdinCap fileCap r1 maxDir maxName ≤
      CliMainPeakSpec.cliMainMaxReq stdinCap fileCap r2 maxDir maxName := by
  unfold CliMainPeakSpec.cliMainMaxReq
  have hinner :
      max r1 (max 1024 (CliMainPeakSpec.m5DirStepMaxReq maxDir maxName)) ≤
        max r2 (max 1024 (CliMainPeakSpec.m5DirStepMaxReq maxDir maxName)) :=
    Nat.max_le.mpr ⟨Nat.le_trans hr (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _, Nat.le_trans hinner (Nat.le_max_right _ _)⟩

private theorem cliMainGrpCount_le_of_le_priv {gRun gCap numDirty : Nat}
    (hg : gRun ≤ gCap) (hd : numDirty ≤ cliMaxDirtyEntries) :
    (CliGroupBounds.cliMainSetupFineGrpS + gRun + numDirty * (12 * FineScale) + 3 * FineScale +
      FineScale - 1) / FineScale ≤ CliTopBudgetSpec.cliMainTightGrpCountOf gCap := by
  unfold CliTopBudgetSpec.cliMainTightGrpCountOf CliTopBudgetSpec.cliMainTightGrpSOf
  exact Nat.div_le_div_right
    (Nat.sub_le_sub_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add (Nat.add_le_add_left hg _) (Nat.mul_le_mul_right _ hd))
          _)
        _)
      _)

/-- Parametric whole-`main` `FitsTrace fineCostModel` (`≤ 90%` = `965,445,342 ≤ 966,367,641` B, `VA ≤ 2 ^ 48`) over `SE : CliRealCalleeFineSpecs (E g)` and `CliRealR2CalleeCaps SE`. -/
theorem cliMain_realR2_90pct_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (SE : CliRealCalleeFineSpecs (E g))
    (hSlots : CliRealR2CalleeCaps SE)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse
      (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
      g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRealMainStepReserve fullLog := by
  have hcaps := hd.toCliPqDomainCaps
  have hspqr := hd.toCliRunTightSpqrCaps
  have hcr := cliRunOpened_real_1MiB_fine_phaseCredit SE hcaps hspqr
  have hgr := cliRunOpened_real_fine_groupSpec (wireOutCap := sessionCapBytes) SE hcaps.stdin_le
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliRealRun_bounds_mono hSlots
  have hcrMain := CliMainPeakSpec.cliMain_phaseCredit_fine
    (uuidParse := uuidParse) (needStdin := needStdin) (ok := ok)
    fineCostModel_modelHyps hcaps haddr hdirs.2 hcr
  have hgrMain := CliGroupBounds.cliMainEnv_groupSpec fineCostModel (dirs := dirs) (ok := ok)
    (CliGroupBounds.cliMainSetupEnv_le_3_fine_groupSpec uuidParse hcaps.argv_le addrOpt needStdin)
    hgr
  have hram90 :
      CliFitsTraceArith.cliDecoupledRamNeed lim.staticBytes
        (CliTopBudgetSpec.cliMainTightCumOf cliRealRunCumCap)
        (CliTopBudgetSpec.cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap)
        (CliTopBudgetSpec.cliMainTightReqOf cliRealRunReqCap)
        (CliTopBudgetSpec.cliMainTightGrpCountOf cliRealRunGrpSCap) ≤ lim.physCap :=
    Nat.le_trans
      (CliFitsTraceArith.cliDecoupledRamNeed_mono hsb
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliRealR2_fits_90pct_and_oneGiB.1 hcap90)
  have hva :
      CliFitsTraceArith.cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (CliTopBudgetSpec.cliMainTightCumOf cliRealRunCumCap)
        (CliTopBudgetSpec.cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap)
        (CliTopBudgetSpec.cliMainTightReqOf cliRealRunReqCap)
        (CliTopBudgetSpec.cliMainTightGrpCountOf cliRealRunGrpSCap) ≤ 2 ^ 48 :=
    Nat.le_trans
      (CliFitsTraceArith.cliDecoupledVaNeed_mono hsb hsc
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliRealR2_fits_90pct_and_oneGiB.2.2.1
  exact CliFitsTraceArith.fitsTrace_fineCostModel_of_group_literal_bounds
    hcrMain hgrMain
    (cliMainDeltaCum_tight_mono_priv h1 hdirs.1)
    (cliMainDeltaLive_le_tightPeak_priv h2)
    (cliMainDeltaPeak_tight_mono_priv h2 h3)
    (cliMainMaxReq_mono_priv h4)
    (cliMainGrpCount_le_of_le_priv h5 hdirs.1)
    henf hram90 hva hEnv

/-- Parametric whole-`main` `FitsEnv fineCostModel` (`≤ 90%`, `VA ≤ 2 ^ 48`) over `SE : CliRealCalleeFineSpecs (E g)` and `CliRealR2CalleeCaps SE`. -/
theorem cliMain_realR2_90pct_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (SE : CliRealCalleeFineSpecs (E g))
    (hSlots : CliRealR2CalleeCaps SE)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse
        (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
        g addrOpt needStdin dirs ok) := by
  have hcaps := hd.toCliPqDomainCaps
  have hspqr := hd.toCliRunTightSpqrCaps
  have hcr := cliRunOpened_real_1MiB_fine_phaseCredit SE hcaps hspqr
  have hgr := cliRunOpened_real_fine_groupSpec (wireOutCap := sessionCapBytes) SE hcaps.stdin_le
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliRealRun_bounds_mono hSlots
  have hcrMain := CliMainPeakSpec.cliMain_phaseCredit_fine
    (uuidParse := uuidParse) (needStdin := needStdin) (ok := ok)
    fineCostModel_modelHyps hcaps haddr hdirs.2 hcr
  have hgrMain := CliGroupBounds.cliMainEnv_groupSpec fineCostModel (dirs := dirs) (ok := ok)
    (CliGroupBounds.cliMainSetupEnv_le_3_fine_groupSpec uuidParse hcaps.argv_le addrOpt needStdin)
    hgr
  have hram90 :
      CliFitsTraceArith.cliDecoupledRamNeed lim.staticBytes
        (CliTopBudgetSpec.cliMainTightCumOf cliRealRunCumCap)
        (CliTopBudgetSpec.cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap)
        (CliTopBudgetSpec.cliMainTightReqOf cliRealRunReqCap)
        (CliTopBudgetSpec.cliMainTightGrpCountOf cliRealRunGrpSCap) ≤ lim.physCap :=
    Nat.le_trans
      (CliFitsTraceArith.cliDecoupledRamNeed_mono hsb
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliRealR2_fits_90pct_and_oneGiB.1 hcap90)
  have hva :
      CliFitsTraceArith.cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (CliTopBudgetSpec.cliMainTightCumOf cliRealRunCumCap)
        (CliTopBudgetSpec.cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap)
        (CliTopBudgetSpec.cliMainTightReqOf cliRealRunReqCap)
        (CliTopBudgetSpec.cliMainTightGrpCountOf cliRealRunGrpSCap) ≤ 2 ^ 48 :=
    Nat.le_trans
      (CliFitsTraceArith.cliDecoupledVaNeed_mono hsb hsc
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliRealR2_fits_90pct_and_oneGiB.2.2.1
  exact CliFitsTraceArith.fitsEnv_fineCostModel_of_group_literal_bounds
    hcrMain hgrMain
    (cliMainDeltaCum_tight_mono_priv h1 hdirs.1)
    (cliMainDeltaLive_le_tightPeak_priv h2)
    (cliMainDeltaPeak_tight_mono_priv h2 h3)
    (cliMainMaxReq_mono_priv h4)
    (cliMainGrpCount_le_of_le_priv h5 hdirs.1)
    henf hram90 hva

/-- `1 GiB` (`cliOneGiB ≤ lim.physCap`) specialization of `cliMain_realR2_90pct_fitsTrace_fineCostModel`. -/
theorem cliMain_realR2_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (SE : CliRealCalleeFineSpecs (E g))
    (hSlots : CliRealR2CalleeCaps SE)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse
      (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
      g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRealMainStepReserve fullLog :=
  cliMain_realR2_90pct_fitsTrace_fineCostModel henf hsb hsc
    (Nat.le_trans (by decide : cliRealNinetyPctOneGiB ≤ cliOneGiB) hcap)
    hd SE hSlots haddr hdirs hEnv

/-- `cliBudgetLimits` (`1 GiB`) specialization of `cliMain_realR2_90pct_fitsEnv_fineCostModel`. -/
theorem cliMain_realR2_fitsEnv_cliBudgetLimits
    {P : PEParams} {uuidParse : UuidParser}
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (SE : CliRealCalleeFineSpecs (E g))
    (hSlots : CliRealR2CalleeCaps SE)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (CliMainEnv uuidParse
        (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
        g addrOpt needStdin dirs ok) :=
  cliMain_realR2_90pct_fitsEnv_fineCostModel rfl (Nat.le_refl _) (Nat.le_refl _)
    (by decide : cliRealNinetyPctOneGiB ≤ cliBudgetLimits.physCap)
    hd SE hSlots haddr hdirs

/-- Unmodified-PKSM (`CliRunTightEnv W`, `pksmSliceCum msgCapBytes = 204,355,676` B, `≤ 1 GiB`) companion `FitsEnv fineCostModel` bridge. -/
theorem cliMain_realUnmodPksm_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRealUnmodPksmSlotCaps SW)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  have hcaps := hd.toCliPqDomainCaps
  have hspqr := hd.toCliRunTightSpqrCaps
  let SE := CliRealCalleeFineSpecs.ofWrapperUnmodPksm SW
  have hcr := cliRunOpened_real_1MiB_fine_phaseCredit (E := fun g' => (W g').toCalleeEnvs)
    SE hcaps hspqr
  have hgr := cliRunOpened_real_fine_groupSpec (E := fun g' => (W g').toCalleeEnvs)
    (wireOutCap := sessionCapBytes) SE hcaps.stdin_le
  rcases hSlots with
    ⟨hic, hil, hip, hir, hig,
     hec, hel, hep, her, heg,
     hsc', hsl, hsp, hsr, hsg,
     hpc, hpl, hpp, hpr, hpg⟩
  have h1 :
      cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
        cliRealUnmodPksmRunCumCap := by
    dsimp only [SE, CliRealCalleeFineSpecs.ofWrapperUnmodPksm,
      CliRealCalleeFineSpecs.ofWrapperWithPksm]
    simp only [cliRun1MiBCustomPksmCum, cliRealUnmodPksmRunCumCap, initArmDeltaCum, r2TightDeltaCum]
    exact Nat.add_le_add_left (max4_mono (by omega) (by omega) (by omega) (by omega)) _
  have h2 :
      cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
        cliRealRunLiveCap := by
    dsimp only [SE, CliRealCalleeFineSpecs.ofWrapperUnmodPksm,
      CliRealCalleeFineSpecs.ofWrapperWithPksm]
    simp only [cliRun1MiBCustomPksmLive, cliRealRunLiveCap, cliRun1MiBSlotLive,
      initArmDeltaLive, r2DeltaLive]
    exact Nat.add_le_add_left (max4_mono (by omega) (by omega) (by omega) (by omega)) _
  have h3 :
      cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
        SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤ cliRealRunPeakCap := by
    dsimp only [SE, CliRealCalleeFineSpecs.ofWrapperUnmodPksm,
      CliRealCalleeFineSpecs.ofWrapperWithPksm]
    unfold cliRun1MiBCustomPksmPeak cliRealRunPeakCap cliRun1MiBSlotPeak
    have hp_init :
        initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SW.initPeak ≤
          initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637
            cliInitSlotPeakCap := by
      unfold initArmDeltaPeak
      have hm :
          max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
            (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + SW.initPeak) ≤
          max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
            (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + cliInitSlotPeakCap) :=
        Nat.max_le.mpr
          ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hip _) (Nat.le_max_right _ _)⟩
      exact Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hm _) (Nat.le_max_right _ _)⟩
    have hp_enc :
        r2DeltaPeak fineCostModel SW.encLive SW.encPeak sessionCapBytes ≤
          r2DeltaPeak fineCostModel cliSendSlotLiveCap cliSendSlotPeakCap
            sessionCapBytes := by
      unfold r2DeltaPeak
      exact Nat.max_le.mpr
        ⟨Nat.le_trans hep (Nat.le_max_left _ _),
         Nat.le_trans (Nat.add_le_add_right hel _) (Nat.le_max_right _ _)⟩
    have hp_sig :
        max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SW.decSigPeak) ≤
          max (sigSlicePeak msgCapBytes)
            (sigSliceLive msgCapBytes + cliRecvWhisperSlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hsp _) (Nat.le_max_right _ _)⟩
    have hp_pk :
        max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + SW.decPkPeak) ≤
          max (pksmSlicePeak msgCapBytes)
            (pksmSliceLive msgCapBytes + cliRecvPrekeySlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hpp _) (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (Nat.add_le_add_left (max4_mono hp_init hp_enc hp_sig hp_pk) _)
         (Nat.le_max_right _ _)⟩
  have h4 :
      cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
        SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤ cliRealRunReqCap := by
    dsimp only [SE, CliRealCalleeFineSpecs.ofWrapperUnmodPksm,
      CliRealCalleeFineSpecs.ofWrapperWithPksm]
    unfold cliRun1MiBCustomPksmMaxReq cliRealRunReqCap cliRun1MiBSlotMaxReq initArmMaxReq r2MaxReq
    have hr_init :
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) SW.initMaxReq) ≤
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) cliInitSlotReqCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans
           (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hir (Nat.le_max_right _ _)⟩)
           (Nat.le_max_right _ _)⟩
    have hr_enc :
        max SW.encMaxReq (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) ≤
          max cliSendSlotReqCap (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) :=
      Nat.max_le.mpr ⟨Nat.le_trans her (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    have hr_sig :
        max (sigSliceMaxReq msgCapBytes) SW.decSigMaxReq ≤
          max (sigSliceMaxReq msgCapBytes) cliRecvWhisperSlotReqCap :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hsr (Nat.le_max_right _ _)⟩
    have hr_pk :
        max (pksmSliceMaxReq msgCapBytes) SW.decPkMaxReq ≤
          max (pksmSliceMaxReq msgCapBytes) cliRecvPrekeySlotReqCap :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hpr (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (max4_mono hr_init hr_enc hr_sig hr_pk) (Nat.le_max_right _ _)⟩
  have h5 :
      cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
        SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤ cliRealRunGrpSCap := by
    dsimp only [SE, CliRealCalleeFineSpecs.ofWrapperUnmodPksm,
      CliRealCalleeFineSpecs.ofWrapperWithPksm]
    unfold cliRunOpenedCustomPksmGrpS cliRealRunGrpSCap cliRealPksmGrpSCap
    exact Nat.add_le_add_left
      (max4_mono
        (Nat.add_le_add_left hig _)
        (Nat.add_le_add_right heg _)
        (Nat.add_le_add_left hsg _)
        (Nat.add_le_add_left hpg _)) _
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5
    cliRealR2_fits_90pct_and_oneGiB.2.2.2.1
    cliRealR2_fits_90pct_and_oneGiB.2.2.2.2

/-! ## 5. Concrete Five-Slot Instantiation and Whole-`main` Corollaries -/

/-- Scaled `fineCostModel` group bound (`42 * FineScale` = `2,752,512`) for `SegCloneEnv G sess.state`
under `AliceInitiatedAnyCkBounds G sess` (`0` or `1` receiver chain with `messageKeys = []` and
arbitrary `chainKey`, requiring zero `SessionCloneDom` / `RecordGhostValid` hypotheses). -/
theorem segCloneEnv_aliceInitiated_fine_groupSpec
    {G : CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost}
    {sess : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hb : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.AliceInitiatedAnyCkBounds G sess) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv G sess.state)
      (42 * FineScale) := by
  have hloc := CliGroupBounds.vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := CliGroupBounds.vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, sess.state.senderChain with
           | some gs, some sc =>
             LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.senderChainCloneEvents gs sc
           | _, _ => [])
      (9 * FineScale) := by
    cases hgs : G.sender <;> cases sess.state.senderChain
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rename_i gs sc
      obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
      exact (CliGroupBounds.senderChainCloneEnv_dom_fine_groupSpec sc hsrk hpriv).mono (by decide)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if sess.state.receiverChains = [] then []
           else LibsignalBinary.Heap.rustAllocEvents (104 * sess.state.receiverChains.length) 8 ++
             (G.chains.zip sess.state.receiverChains).flatMap
               LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.chainCloneEvents)
      (12 * FineScale) := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, hmks⟩
    · rw [hnil]
      simp only [↓reduceIte]
      exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hrc1]
      simp only [List.cons_ne_self, ↓reduceIte, List.length_singleton, Nat.mul_one]
      cases G.chains with
      | nil =>
        simp only [List.zip_nil_left, List.flatMap_nil, List.append_nil]
        exact (PhaseGroupSpec.rustAlloc_any fineCostModel 104 8).mono (by decide)
      | cons gc0 gcs =>
        simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        unfold LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.chainCloneEvents
        dsimp only
        rw [hmks]
        simp only [↓reduceIte, List.append_nil]
        have hck : PhaseGroupSpec fineCostModel
            (· = match rc0.chainKey with
                 | none => []
                 | some _ => LibsignalBinary.Heap.rustAllocEvents 32 1)
            (3 * FineScale) := by
          cases rc0.chainKey
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · exact PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
        exact (CliGroupBounds.phaseGroupSpec_append_eq fineCostModel
          (PhaseGroupSpec.rustAlloc_any fineCostModel 104 8)
          (CliGroupBounds.phaseGroupSpec_append_eq fineCostModel
            (CliGroupBounds.phaseGroupSpec_append_eq fineCostModel
              (CliGroupBounds.vecCloneEvents_groupSpec fineCostModel gc0.srk)
              (CliGroupBounds.vecCloneEvents_groupSpec fineCostModel gc0.priv))
            hck)).mono (by decide)
  have hpend := CliGroupBounds.optTailCloneEvents_groupSpec fineCostModel G.pending
  have hkyb := CliGroupBounds.optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice := CliGroupBounds.vecCloneEvents_groupSpec fineCostModel G.alice
  have hpq : PhaseGroupSpec fineCostModel
      (· = if sess.state.pqRatchetState.length = 0 then []
           else LibsignalBinary.Heap.rustAllocEvents sess.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel sess.state.pqRatchetState.length 1
  have s1 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := CliGroupBounds.phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv
    LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.segCloneEvents
  exact s8.mono (by decide)

/-- Scaled `fineCostModel` group bound (`45 * FineScale` = `2,949,120`) for
`RecordSerializeCancelEnv g r` under `RecordAliceInitiatedAnyCkBounds g r`. -/
theorem recordSerializeCancelEnv_aliceInitiated_fine_groupSpec
    {g : CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hb : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds g r) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.RecordSerializeCancelEnv g r)
      (45 * FineScale) := by
  unfold LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.RecordSerializeCancelEnv
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G sess
    exact CliGroupBounds.serializeSomeCancelEnv_groupSpec fineCostModel
      (segCloneEnv_aliceInitiated_fine_groupSpec (hb G sess hg hr))

/-- Concrete closed-Nat `W3` (`init`) numbers from `W3InitiateTightSpec` +
`DeserializeCancelBudget`:
`(cum, live, peak, maxReq, grpS) = (24764863, 15376971, 16425515, 2097152, 420352780)`. -/
def w3InitRealCum : Nat :=
  7874410 + LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineCum
def w3InitRealLive : Nat := 15376971
def w3InitRealPeak : Nat := 16425515
def w3InitRealMaxReq : Nat := 2097152
def w3InitRealGrpS : Nat :=
  1113 * FineScale +
    LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineGrpS +
    45 * FineScale

/-- Checks that `W3`'s proved bounds from `W3InitiateTightSpec` and `DeserializeCancelBudget` fit inside `CliTopBudgetSpec.cliInitSlot*Cap`. -/
theorem w3InitReal_caps_le :
    w3InitRealCum = 24764863 ∧
    w3InitRealGrpS = 420352780 ∧
    w3InitRealLive ≤ w3InitRealPeak ∧
    w3InitRealCum ≤ cliInitSlotCumCap ∧
    w3InitRealLive ≤ cliInitSlotLiveCap ∧
    w3InitRealPeak ≤ cliInitSlotPeakCap ∧
    w3InitRealMaxReq ≤ cliInitSlotReqCap ∧
    w3InitRealGrpS ≤ cliInitSlotGrpSCap := by
  decide

/-- Concrete `W3` (`init`) `SingleSlotFineSpec` built from
`W3InitiateTightSpec.w3InitiateSlot_at_initCallSite_aliceInitiatedAnyCk_phaseCredit`,
`DeserializeCancelBudget`, and `recordSerializeCancelEnv_aliceInitiated_fine_groupSpec`. -/
def w3InitReal_singleSlotFineSpec
    {img : Arm64.Obj.Image} {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall} {x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    (F : CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds g_rec r_rec) :
    SingleSlotFineSpec
      (LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec.W3InitiateSlotEnv
        (LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.mkW3InitiateSlotParamsDeser
          rd
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
          x ownKeyName ownRegName F x_spqr g_rec r_rec)) where
  cum := w3InitRealCum
  live := w3InitRealLive
  peak := w3InitRealPeak
  maxReq := w3InitRealMaxReq
  grpS := w3InitRealGrpS
  credit := by
    have hcr :=
      LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.w3InitiateSlot_at_initCallSite_aliceInitiatedAnyCk_phaseCredit
        (F := F) hsite hkeyName hregName hspqrKey hfileCap
        (fun _ hbs =>
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
        halice
    obtain ⟨_, _, hlive, hpeak, hreq, _⟩ :=
      LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.w3InitiateSlotTight_real192_eq
    dsimp only [LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineLive,
      LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFinePeak,
      LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineMaxReq] at hcr
    rw [hlive, hpeak, hreq] at hcr
    exact hcr
  live_le_peak := w3InitReal_caps_le.2.2.1
  groups :=
    CliGroupBounds.w3InitiateSlotEnv_groupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.mkW3InitiateSlotParamsDeser
        rd
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
        x ownKeyName ownRegName F x_spqr g_rec r_rec)
      (fun bs _ =>
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.recordDeserializeCancelEnv_fine_groupSpec bs)
      (recordSerializeCancelEnv_aliceInitiated_fine_groupSpec halice)

/-- Checks that `WirePksmTightCredit.pksmCanonSlice* msgCapBytes` fits inside `cliRealPksm*Cap`. -/
theorem pksmReal_caps_le :
    WirePksmTightCredit.pksmCanonSliceCum msgCapBytes = 103232265 ∧
    WirePksmTightCredit.pksmCanonSliceCum msgCapBytes ≤ cliRealPksmCumCap ∧
    WirePksmTightCredit.pksmCanonSliceLive msgCapBytes ≤ cliRealPksmLiveCap ∧
    WirePksmTightCredit.pksmCanonSlicePeak msgCapBytes ≤ cliRealPksmPeakCap ∧
    WirePksmTightCredit.pksmCanonSliceMaxReq msgCapBytes ≤ cliRealPksmReqCap ∧
    WirePksmTightCredit.pksmCanonSliceGrpS msgCapBytes ≤ cliRealPksmGrpSCap := by
  decide

/-- Concrete `CliRunCalleeEnvs` bundle wiring `W3InitiateSlotEnv`, `W1SendRealSlotEnv`,
`W2RecvWhisperRealSlotEnv`, `WirePksmTightCredit.PksmCanonSliceEnv`, and
`W4RecvPrekeyRealSlot.W4RecvPrekeyRealEnv` with `RecordDeserializeCancelEnv`. -/
def mkRealCalleeEnvs [LibsignalPlacement]
    (img : Arm64.Obj.Image)
    (P : PEParams) (g : RunCall)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : W1SendRealParams)
    (w2R : W2RecvWhisperRealParams)
    (w4R : W4RecvPrekeyRealParams) :
    CliRunCalleeEnvs where
  initEnv :=
    LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec.W3InitiateSlotEnv
      (LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.mkW3InitiateSlotParamsDeser
        rd
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
        x ownKeyName ownRegName F x_spqr g_rec r_rec)
  encEnv := W1SendRealSlotEnv img P g.i w1R
  decSigEnv := W2RecvWhisperRealSlotEnv P g.i w2R
  pksmEnv := WirePksmTightCredit.PksmCanonSliceEnv
  decPkEnv := W4RecvPrekeyRealEnv w4R

/-- Mode-dispatched companion of `mkRealCalleeEnvs` whose `CliRunOpenedEnv` agrees
definitionally with `mkRealCalleeEnvs` on all four `CallV` constructors (`keygen`, `init`, `send`,
`recv`), allowing `buildCliRealCalleeFineSpecs` to require each arm's call-site preconditions only
on that arm's command constructor. -/
def mkRealCalleeEnvsModeGuarded [LibsignalPlacement]
    (img : Arm64.Obj.Image)
    (P : PEParams) (g : RunCall)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : W1SendRealParams)
    (w2R : W2RecvWhisperRealParams)
    (w4R : W4RecvPrekeyRealParams) :
    CliRunCalleeEnvs where
  initEnv := match g.c with
    | .init _ _ =>
      LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec.W3InitiateSlotEnv
        (LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.mkW3InitiateSlotParamsDeser
          rd
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
          x ownKeyName ownRegName F x_spqr g_rec r_rec)
    | _ => fun _ => False
  encEnv := match g.c with
    | .send _ => W1SendRealSlotEnv img P g.i w1R
    | _ => fun _ => False
  decSigEnv := match g.c with
    | .recv _ => W2RecvWhisperRealSlotEnv P g.i w2R
    | _ => fun _ => False
  pksmEnv := WirePksmTightCredit.PksmCanonSliceEnv
  decPkEnv := match g.c with
    | .recv _ => W4RecvPrekeyRealEnv w4R
    | _ => fun _ => False

private theorem cliRunOpenedEnv_mkRealCalleeEnvs_eq [LibsignalPlacement]
    (img : Arm64.Obj.Image)
    (P : PEParams)
    (rd : RunCall → ReadRule)
    (x : RunCall → CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : RunCall → List (BitVec 8))
    (F : RunCall → CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : RunCall → CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : RunCall → CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : RunCall → CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : RunCall → W1SendRealParams)
    (w2R : RunCall → W2RecvWhisperRealParams)
    (w4R : RunCall → W4RecvPrekeyRealParams) :
    (fun g' => CliRunOpenedEnv cliIo.rd
      (mkRealCalleeEnvs img P g' (rd g') (x g') (ownKeyName g') (ownRegName g')
        (F g') (x_spqr g') (g_rec g') (r_rec g') (w1R g') (w2R g') (w4R g'))
      sessionCapBytes g') =
    (fun g' => CliRunOpenedEnv cliIo.rd
      (mkRealCalleeEnvsModeGuarded img P g' (rd g') (x g') (ownKeyName g') (ownRegName g')
        (F g') (x_spqr g') (g_rec g') (r_rec g') (w1R g') (w2R g') (w4R g'))
      sessionCapBytes g') := by
  funext g' evs
  rcases g' with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c' <;> rfl

theorem emptyPhaseCreditSpec (c l p r : Nat) :
    PhaseCreditSpec fineCostModel (fun _ => False) c l p r :=
  ((PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)).mono
    (Nat.zero_le c) (Nat.zero_le l) (Nat.zero_le p) (Nat.zero_le r)

theorem emptyPhaseGroupSpec (grp : Nat) :
    PhaseGroupSpec fineCostModel (fun _ => False) grp :=
  ((PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)).mono
    (Nat.zero_le grp)

theorem w3Guarded_credit [LibsignalPlacement]
    {P : PEParams} {img : Arm64.Obj.Image}
    {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    (F : CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds g_rec r_rec)
    (w1R : W1SendRealParams) (w2R : W2RecvWhisperRealParams) (w4R : W4RecvPrekeyRealParams) :
    PhaseCreditSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).initEnv
      w3InitRealCum w3InitRealLive w3InitRealPeak w3InitRealMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · rename_i peerV dir
    exact (w3InitReal_singleSlotFineSpec (hsite peerV dir rfl) F hkeyName hregName hspqrKey hfileCap halice).credit
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _

theorem w3Guarded_groups [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds g_rec r_rec)
    (w1R : W1SendRealParams) (w2R : W2RecvWhisperRealParams) (w4R : W4RecvPrekeyRealParams) :
    PhaseGroupSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).initEnv
      w3InitRealGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact
      CliGroupBounds.w3InitiateSlotEnv_groupSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.mkW3InitiateSlotParamsDeser
          rd
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv
          x ownKeyName ownRegName F x_spqr g_rec r_rec)
        (fun bs _ =>
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.recordDeserializeCancelEnv_fine_groupSpec bs)
        (recordSerializeCancelEnv_aliceInitiated_fine_groupSpec halice)
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _

theorem w1Guarded_credit [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g)
    {w1R : W1SendRealParams}
    (hw1 : W1SendRealDom g.c w1R)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w2R : W2RecvWhisperRealParams)
    (w4R : W4RecvPrekeyRealParams) :
    PhaseCreditSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).encEnv
      W1SendRealSlot.w1SendRealDcanCum
      W1SendRealSlot.w1SendRealDcanLive
      W1SendRealSlot.w1SendRealDcanPeak
      W1SendRealSlot.w1SendRealDcanMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact (w1SendRealSlot_dcan_singleSlotFineSpec (img := img) w1R hd.toCliPqxdhInputs
      hd.parseArgs_eq hw1 hd.toCliPqDomainCaps.files_bounded).credit
  · exact emptyPhaseCreditSpec _ _ _ _

theorem w1Guarded_groups [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g)
    {w1R : W1SendRealParams}
    (hw1 : W1SendRealDom g.c w1R)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w2R : W2RecvWhisperRealParams)
    (w4R : W4RecvPrekeyRealParams) :
    PhaseGroupSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).encEnv
      W1SendRealSlot.w1SendRealDcanGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact (w1SendRealSlot_dcan_singleSlotFineSpec (img := img) w1R hd.toCliPqxdhInputs
      hd.parseArgs_eq hw1 hd.toCliPqDomainCaps.files_bounded).groups
  · exact emptyPhaseGroupSpec _

theorem w2Guarded_credit [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g)
    {w2R : W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c w2R)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : W1SendRealParams)
    (w4R : W4RecvPrekeyRealParams) :
    PhaseCreditSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).decSigEnv
      W2RecvWhisperRealSlot.w2RecvWhisperRealDcanCum
      W2RecvWhisperRealSlot.w2RecvWhisperRealDcanLive
      W2RecvWhisperRealSlot.w2RecvWhisperRealDcanPeak
      W2RecvWhisperRealSlot.w2RecvWhisperRealDcanMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact (w2RecvWhisperRealSlot_dcan_singleSlotFineSpec w2R hd.toCliPqxdhInputs
      hd.parseArgs_eq hw2 hd.toCliPqDomainCaps.files_bounded).credit

theorem w2Guarded_groups [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    (hd : CliPqRealCallDomain P g)
    {w2R : W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c w2R)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : W1SendRealParams)
    (w4R : W4RecvPrekeyRealParams) :
    PhaseGroupSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).decSigEnv
      W2RecvWhisperRealSlot.w2RecvWhisperRealDcanGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact (w2RecvWhisperRealSlot_dcan_singleSlotFineSpec w2R hd.toCliPqxdhInputs
      hd.parseArgs_eq hw2 hd.toCliPqDomainCaps.files_bounded).groups

theorem w4Guarded_credit [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    {w4R : W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom w4R)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : W1SendRealParams)
    (w2R : W2RecvWhisperRealParams) :
    PhaseCreditSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).decPkEnv
      W4RecvPrekeyRealSlot.w4RecvPrekeyRealCum
      W4RecvPrekeyRealSlot.w4RecvPrekeyRealLive
      W4RecvPrekeyRealSlot.w4RecvPrekeyRealPeak
      W4RecvPrekeyRealSlot.w4RecvPrekeyRealMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · rename_i peerV
    exact (w4RecvPrekeyReal_singleSlotFineSpec w4R (hw4 peerV rfl)).credit

theorem w4Guarded_groups [LibsignalPlacement]
    {img : Arm64.Obj.Image} {P : PEParams} {g : RunCall}
    {w4R : W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom w4R)
    (rd : ReadRule)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : W1SendRealParams)
    (w2R : W2RecvWhisperRealParams) :
    PhaseGroupSpec fineCostModel
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R).decPkEnv
      W4RecvPrekeyRealSlot.w4RecvPrekeyRealGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · rename_i peerV
    exact (w4RecvPrekeyReal_singleSlotFineSpec w4R (hw4 peerV rfl)).groups

/-- Builds `CliRealCalleeFineSpecs` across all five concrete slot theorems
(`w3InitReal_singleSlotFineSpec`, `w1SendRealSlot_dcan_singleSlotFineSpec`,
`w2RecvWhisperRealSlot_dcan_singleSlotFineSpec`, `WirePksmTightCredit.pksmCanonSlice_fine_*`, and
`w4RecvPrekeyReal_singleSlotFineSpec`). -/
def buildCliRealCalleeFineSpecs [LibsignalPlacement]
    {P : PEParams} {img : Arm64.Obj.Image}
    {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    (hd : CliPqRealCallDomain P g)
    {x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    (F : CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : (ownKeyName).length ≤ 64)
    (hregName : (ownRegName).length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds g_rec r_rec)
    {w1R : W1SendRealParams}
    (hw1 : W1SendRealDom g.c w1R)
    {w2R : W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c w2R)
    {w4R : W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom w4R) :
    CliRealCalleeFineSpecs
      (mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R) :=
  { initCum := w3InitRealCum
    initLive := w3InitRealLive
    initPeak := w3InitRealPeak
    initMaxReq := w3InitRealMaxReq
    initGrpS := w3InitRealGrpS
    init_spec := w3Guarded_credit hsite F hkeyName hregName hspqrKey hfileCap halice w1R w2R w4R
    init_lp := w3InitReal_caps_le.2.2.1
    init_grp := w3Guarded_groups rd x ownKeyName ownRegName F x_spqr g_rec r_rec halice w1R w2R w4R
    encCum := W1SendRealSlot.w1SendRealDcanCum
    encLive := W1SendRealSlot.w1SendRealDcanLive
    encPeak := W1SendRealSlot.w1SendRealDcanPeak
    encMaxReq := W1SendRealSlot.w1SendRealDcanMaxReq
    encGrpS := W1SendRealSlot.w1SendRealDcanGrpS
    enc_spec := w1Guarded_credit hd hw1 rd x ownKeyName ownRegName F x_spqr g_rec r_rec w2R w4R
    enc_lp := W1SendRealSlot.w1SendRealDcan_live_le_peak
    enc_grp := w1Guarded_groups hd hw1 rd x ownKeyName ownRegName F x_spqr g_rec r_rec w2R w4R
    decSigCum := W2RecvWhisperRealSlot.w2RecvWhisperRealDcanCum
    decSigLive := W2RecvWhisperRealSlot.w2RecvWhisperRealDcanLive
    decSigPeak := W2RecvWhisperRealSlot.w2RecvWhisperRealDcanPeak
    decSigMaxReq := W2RecvWhisperRealSlot.w2RecvWhisperRealDcanMaxReq
    decSigGrpS := W2RecvWhisperRealSlot.w2RecvWhisperRealDcanGrpS
    decSig_spec := w2Guarded_credit hd hw2 rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w4R
    decSig_lp := W2RecvWhisperRealSlot.w2RecvWhisperRealDcan_live_le_peak
    decSig_grp := w2Guarded_groups hd hw2 rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w4R
    pksmCum := WirePksmTightCredit.pksmCanonSliceCum msgCapBytes
    pksmLive := WirePksmTightCredit.pksmCanonSliceLive msgCapBytes
    pksmPeak := WirePksmTightCredit.pksmCanonSlicePeak msgCapBytes
    pksmMaxReq := WirePksmTightCredit.pksmCanonSliceMaxReq msgCapBytes
    pksmGrpS := WirePksmTightCredit.pksmCanonSliceGrpS msgCapBytes
    pksm_spec := fun _ hrest => WirePksmTightCredit.pksmCanonSlice_fine_phaseCredit hrest
    pksm_lp := WirePksmTightCredit.pksmCanonSliceLive_le_peak msgCapBytes
    pksm_grp := fun _ hrest => WirePksmTightCredit.pksmCanonSlice_fine_groupSpec hrest
    decPkCum := W4RecvPrekeyRealSlot.w4RecvPrekeyRealCum
    decPkLive := W4RecvPrekeyRealSlot.w4RecvPrekeyRealLive
    decPkPeak := W4RecvPrekeyRealSlot.w4RecvPrekeyRealPeak
    decPkMaxReq := W4RecvPrekeyRealSlot.w4RecvPrekeyRealMaxReq
    decPkGrpS := W4RecvPrekeyRealSlot.w4RecvPrekeyRealGrpS
    decPk_spec := w4Guarded_credit hw4 rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R
    decPk_lp := w4RecvPrekeyReal_caps_le.1
    decPk_grp := w4Guarded_groups hw4 rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R }

/-- Discharges `CliRealR2CalleeCaps` on `buildCliRealCalleeFineSpecs` across all five concrete slots. -/
theorem cliRealCalleeFineSpecs_caps [LibsignalPlacement]
    {P : PEParams} {img : Arm64.Obj.Image}
    {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    (hd : CliPqRealCallDomain P g)
    {x : CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    (F : CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds g_rec r_rec)
    {w1R : W1SendRealParams}
    (hw1 : W1SendRealDom g.c w1R)
    {w2R : W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c w2R)
    {w4R : W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom w4R) :
    CliRealR2CalleeCaps
      (E := mkRealCalleeEnvsModeGuarded img P g rd x ownKeyName ownRegName F x_spqr g_rec r_rec w1R w2R w4R)
      (buildCliRealCalleeFineSpecs hd hsite F hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4) := by
  obtain ⟨_, _, _, hic, hil, hip, hir, hig⟩ := w3InitReal_caps_le
  obtain ⟨_, _, hec, hel, hep, her, heg⟩ := w1SendReal_dcan_caps_le
  obtain ⟨_, _, _, hsc, hsl, hsp, hsr, hsg⟩ := w2RecvWhisperReal_dcan_caps_le
  obtain ⟨_, hkc, hkl, hkp, hkr, hkg⟩ := pksmReal_caps_le
  obtain ⟨_, hpc, hpl, hpp, hpr, hpg⟩ := w4RecvPrekeyReal_caps_le
  exact ⟨hic, hil, hip, hir, hig,
    hec, hel, hep, her, heg,
    hsc, hsl, hsp, hsr, hsg,
    hkc, hkl, hkp, hkr, hkg,
    hpc, hpl, hpp, hpr, hpg⟩

/-- Concrete whole-`main` `FitsTrace fineCostModel` at `≤ 90%` (`965,445,342` B) across all five
concrete slot envelopes under `CliPqRealCallDomain`. -/
theorem cliMain_realR2_concrete_90pct_fitsTrace_fineCostModel [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {img : Arm64.Obj.Image} {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    {x : RunCall → CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g (x g))
    {rd : RunCall → ReadRule}
    {ownKeyName ownRegName : RunCall → List (BitVec 8)}
    (F : RunCall → CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : RunCall → CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : RunCall → CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : RunCall → CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : (ownKeyName g).length ≤ 64)
    (hregName : (ownRegName g).length ≤ 64)
    (hspqrKey : (x_spqr g).p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, (rd g) (x g).F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds (g_rec g) (r_rec g))
    {w1R : RunCall → W1SendRealParams}
    (hw1 : W1SendRealDom g.c (w1R g))
    {w2R : RunCall → W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c (w2R g))
    {w4R : RunCall → W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom (w4R g))
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse
      (fun g' => CliRunOpenedEnv cliIo.rd
        (mkRealCalleeEnvs img P g' (rd g') (x g') (ownKeyName g') (ownRegName g')
          (F g') (x_spqr g') (g_rec g') (r_rec g')
          (w1R g') (w2R g') (w4R g'))
        sessionCapBytes g')
      g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRealMainStepReserve fullLog := by
  rw [cliRunOpenedEnv_mkRealCalleeEnvs_eq] at hEnv
  exact cliMain_realR2_90pct_fitsTrace_fineCostModel henf hsb hsc hcap90 hd
    (buildCliRealCalleeFineSpecs hd hsite (F g) hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4)
    (cliRealCalleeFineSpecs_caps hd hsite (F g) hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4)
    haddr hdirs hEnv

/-- Concrete whole-`main` `FitsEnv fineCostModel` at `≤ 90%` (`965,445,342` B) across all five
concrete slot envelopes under `CliPqRealCallDomain`. -/
theorem cliMain_realR2_concrete_90pct_fitsEnv_fineCostModel [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {img : Arm64.Obj.Image} {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    {x : RunCall → CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g (x g))
    {rd : RunCall → ReadRule}
    {ownKeyName ownRegName : RunCall → List (BitVec 8)}
    (F : RunCall → CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : RunCall → CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : RunCall → CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : RunCall → CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : (ownKeyName g).length ≤ 64)
    (hregName : (ownRegName g).length ≤ 64)
    (hspqrKey : (x_spqr g).p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, (rd g) (x g).F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds (g_rec g) (r_rec g))
    {w1R : RunCall → W1SendRealParams}
    (hw1 : W1SendRealDom g.c (w1R g))
    {w2R : RunCall → W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c (w2R g))
    {w4R : RunCall → W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom (w4R g))
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse
        (fun g' => CliRunOpenedEnv cliIo.rd
          (mkRealCalleeEnvs img P g' (rd g') (x g') (ownKeyName g') (ownRegName g')
            (F g') (x_spqr g') (g_rec g') (r_rec g')
            (w1R g') (w2R g') (w4R g'))
          sessionCapBytes g')
        g addrOpt needStdin dirs ok) := by
  rw [cliRunOpenedEnv_mkRealCalleeEnvs_eq]
  exact cliMain_realR2_90pct_fitsEnv_fineCostModel henf hsb hsc hcap90 hd
    (buildCliRealCalleeFineSpecs hd hsite (F g) hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4)
    (cliRealCalleeFineSpecs_caps hd hsite (F g) hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4)
    haddr hdirs

/-- `1 GiB` (`cliOneGiB ≤ lim.physCap`) specialization of `cliMain_realR2_concrete_90pct_fitsTrace_fineCostModel`. -/
theorem cliMain_realR2_concrete_fitsTrace_fineCostModel [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {P : PEParams} {uuidParse : UuidParser}
    {img : Arm64.Obj.Image} {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    {x : RunCall → CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g (x g))
    {rd : RunCall → ReadRule}
    {ownKeyName ownRegName : RunCall → List (BitVec 8)}
    (F : RunCall → CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : RunCall → CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : RunCall → CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : RunCall → CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : (ownKeyName g).length ≤ 64)
    (hregName : (ownRegName g).length ≤ 64)
    (hspqrKey : (x_spqr g).p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, (rd g) (x g).F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds (g_rec g) (r_rec g))
    {w1R : RunCall → W1SendRealParams}
    (hw1 : W1SendRealDom g.c (w1R g))
    {w2R : RunCall → W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c (w2R g))
    {w4R : RunCall → W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom (w4R g))
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hd : CliPqRealCallDomain P g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse
      (fun g' => CliRunOpenedEnv cliIo.rd
        (mkRealCalleeEnvs img P g' (rd g') (x g') (ownKeyName g') (ownRegName g')
          (F g') (x_spqr g') (g_rec g') (r_rec g')
          (w1R g') (w2R g') (w4R g'))
        sessionCapBytes g')
      g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRealMainStepReserve fullLog :=
  cliMain_realR2_concrete_90pct_fitsTrace_fineCostModel henf hsb hsc
    (Nat.le_trans (by decide : cliRealNinetyPctOneGiB ≤ cliOneGiB) hcap)
    hsite F hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4 hd haddr hdirs hEnv

/-- `cliBudgetLimits` (`1 GiB` RAM, `2 ^ 48` VA) specialization of `cliMain_realR2_concrete_90pct_fitsEnv_fineCostModel`. -/
theorem cliMain_realR2_concrete_fitsEnv_cliBudgetLimits [LibsignalPlacement]
    {P : PEParams} {uuidParse : UuidParser}
    {img : Arm64.Obj.Image} {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {g : RunCall}
    {x : RunCall → CryptoVerification.SignalSession.Cli.RunCompose.InitGhost}
    (hsite : ∀ peerV dir, g.c = .init peerV dir →
      LibsignalBinary.Proofs.PeakBudget.CallSiteFacts.InitCallSite img S g (x g))
    {rd : RunCall → ReadRule}
    {ownKeyName ownRegName : RunCall → List (BitVec 8)}
    (F : RunCall → CryptoGames.LibsignalSession.ShaCompress)
    {x_spqr : RunCall → CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost}
    {g_rec : RunCall → CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r_rec : RunCall → CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))}
    (hkeyName : (ownKeyName g).length ≤ 64)
    (hregName : (ownRegName g).length ≤ 64)
    (hspqrKey : (x_spqr g).p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, (rd g) (x g).F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.RecordAliceInitiatedAnyCkBounds (g_rec g) (r_rec g))
    {w1R : RunCall → W1SendRealParams}
    (hw1 : W1SendRealDom g.c (w1R g))
    {w2R : RunCall → W2RecvWhisperRealParams}
    (hw2 : W2RecvWhisperRealDom g.c (w2R g))
    {w4R : RunCall → W4RecvPrekeyRealParams}
    (hw4 : ∀ peerV, g.c = .recv peerV → W4RecvPrekeyRealDom (w4R g))
    (hd : CliPqRealCallDomain P g)
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (CliMainEnv uuidParse
        (fun g' => CliRunOpenedEnv cliIo.rd
          (mkRealCalleeEnvs img P g' (rd g') (x g') (ownKeyName g') (ownRegName g')
            (F g') (x_spqr g') (g_rec g') (r_rec g')
            (w1R g') (w2R g') (w4R g'))
          sessionCapBytes g')
        g addrOpt needStdin dirs ok) :=
  cliMain_realR2_concrete_90pct_fitsEnv_fineCostModel rfl (Nat.le_refl _) (Nat.le_refl _)
    (by decide : cliRealNinetyPctOneGiB ≤ cliBudgetLimits.physCap)
    hsite F hkeyName hregName hspqrKey hfileCap halice hw1 hw2 hw4 hd haddr hdirs

/-! ## 6. Concrete `recv-prekey` (`3#8`) Non-Vacuity Witness -/

private def nonVacMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ => none
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 0#8
  validPk := fun _ _ => false

private def nonVacCrypto : CryptoGames.LibsignalSession.Crypto where
  F := fun s _ => s
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ _ => List.Vector.replicate 32 0#8
  pubKey := fun _ => List.Vector.replicate 32 0#8

private def nonVacPqxdhPrims : CryptoVerification.E2E.PqxdhPrims where
  F512 := fun s _ => s
  montToEd := fun _ _ => none
  compress := fun _ => List.Vector.replicate 32 0#8
  edNeg := fun _ => List.Vector.replicate 160 0#8
  isTorsionFree := fun _ => false
  dsmb := fun _ _ _ => List.Vector.replicate 160 0#8
  scalarMod := fun _ => List.Vector.replicate 32 0#8
  scalarWide := fun _ => List.Vector.replicate 32 0#8
  encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps := fun _ _ => List.Vector.replicate 32 0#8
  K := nonVacMlKem

/-- Concrete `PEParams` witness whose `montToEd = none` rejects every handshake (`ReachablePqxdhSession`
is empty, so `SessionRecordCapInDomain` holds with zero model assumptions) while `CliPqRealCallDomain`
admits Bob's fresh-directory `recv` call on `wirePrekey :: pksmNonVacFields.bytes`. -/
private def nonVacPEParams : PEParams where
  C := nonVacCrypto
  Q := nonVacPqxdhPrims

/-- Fresh Bob directory witness (`session = none`, empty pre-key stores). -/
private def nonVacBobParty : PqParty where
  party := .B
  me := ⟨List.Vector.replicate 32 0#8, 0#32⟩
  peerId := none
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

/-- Concrete `recv <Alice>` call delivering `wirePrekey :: pksmNonVacFields.bytes` (`3#8` arm). -/
private def nonVacRecvPrekeyCall : RunCall where
  i := pqRecvInputs nonVacPEParams nonVacBobParty
    (wirePrekey :: WirePksmTightCredit.pksmNonVacFields.bytes) 0#256
  c := .recv ⟨utf8 (CryptoVerification.E2E.partyAddressName .A), 1#8⟩
  a := some none
  res := 0#64
  call := 0#64
  stores := 0#64
  inp := 0#64
  coins := 0#64

private theorem nonVacPEParams_not_reachable
    {me : CryptoVerification.E2E.LocalIdentity}
    {x : CryptoVerification.E2E.RecordExtras}
    {g : CryptoGames.LibsignalSession.GhostState (List (BitVec 8))}
    (hr : CryptoVerification.E2E.ReachablePqxdhSession nonVacPEParams me x g) : False := by
  induction hr with
  | initiate X P me' b t x' g' hinit =>
    have hsig : ∀ pk msg sig,
        (CryptoVerification.E2E.modelPrims X nonVacPEParams).sigVerify pk msg sig = false := by
      intro pk msg sig
      unfold CryptoVerification.E2E.modelPrims SignalPqxdh.xeddsaVerifyRef
        CryptoVerification.E2E.blockLevelPrims nonVacPEParams nonVacPqxdhPrims
      dsimp only
      split <;> rfl
    unfold CryptoVerification.E2E.initiateState SignalPqxdh.Model.initiateKeys at hinit
    simp [hsig] at hinit
  | recvPrekey X P me' k m rc x' g' pt hrecv =>
    have hcan : ∀ pk,
        (CryptoVerification.E2E.modelPrims X nonVacPEParams).isCanonical pk = false := by
      intro pk
      unfold CryptoVerification.E2E.modelPrims SignalPqxdh.isCanonicalRef
        CryptoVerification.E2E.blockLevelPrims nonVacPEParams nonVacPqxdhPrims
      dsimp only
      split <;> rfl
    have hacc : ∀ inp,
        SignalPqxdh.Model.acceptKeys (CryptoVerification.E2E.modelPrims X nonVacPEParams) inp =
          none := by
      intro inp
      unfold SignalPqxdh.Model.acceptKeys
      simp [hcan]
    unfold CryptoVerification.E2E.recvPrekeyState at hrecv
    cases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner with
    | error _ =>
      rw [htry] at hrecv
      nomatch hrecv
    | ok inner =>
      rw [htry] at hrecv
      dsimp only at hrecv
      split at hrecv
      · nomatch hrecv
      · rw [hacc] at hrecv
        nomatch hrecv
  | send _ _ _ _ ih => exact ih
  | recv _ _ _ ih => exact ih

private def nonVacKutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem nonVac_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem nonVac_utf8_eq_kutf8 (s : String) :
    CryptoVerification.SignalSession.Cli.utf8 s = nonVacKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.SignalSession.Cli.utf8, nonVacKutf8, List.utf8Encode,
    nonVac_byteArray_toList_eq_data]

private theorem nonVac_repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = nonVacKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, nonVacKutf8, List.utf8Encode,
    nonVac_byteArray_toList_eq_data]

private theorem nonVacBobParty_inSpecDomain :
    PqxdhPartyInSpecDomain nonVacPEParams nonVacBobParty := by
  refine ⟨?_, ?_, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil⟩
  · intro _ _ hs
    nomatch hs
  · intro f hf
    have hle : f.2.length ≤ CryptoVerification.SignalSession.fileCapBytes := by
      unfold CryptoVerification.SignalSession.encodeDir nonVacBobParty nonVacPEParams nonVacCrypto
        at hf
      simp only [List.map_nil, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hf
      unfold CryptoVerification.SignalSession.fileCapBytes
      rcases hf with rfl | rfl | rfl
      · dsimp only
        unfold CryptoVerification.SignalSession.textBytes CryptoVerification.SignalSession.partyAddress
          CryptoVerification.SignalSession.Address.text
        dsimp only
        rw [nonVac_repr_utf8_eq_kutf8]
        have hk_app (a b : String) : nonVacKutf8 (a ++ b) = nonVacKutf8 a ++ nonVacKutf8 b := by
          simp [nonVacKutf8, String.toList_append, List.flatMap_append]
        rw [hk_app, hk_app, List.length_append, List.length_append]
        have hd : (nonVacKutf8 (toString (1 : Nat))).length ≤ 1 := by
          rw [← nonVac_utf8_eq_kutf8]
          exact CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_length_le 1 1
            (by omega) (by omega)
        have hdot : (nonVacKutf8 ".").length = 1 := rfl
        have hp : (nonVacKutf8 (CryptoVerification.E2E.partyAddressName .B)).length = 36 := rfl
        omega
      · decide
      · decide
    refine ⟨?_, fun _ => hle⟩
    unfold CryptoVerification.SignalSession.fileCapBytes at hle
    omega

private theorem nonVacStdin_length_le_msgCap :
    nonVacRecvPrekeyCall.i.stdin.length ≤ msgCapBytes := by
  let x : CryptoVerification.E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs :=
    WirePksmTightCredit.pksmNonVacArgs
  have hb : WirePksmTightCredit.pksmNonVacFields.bytes = x.bytes := rfl
  have henc33 : (CryptoVerification.LibsignalProtoCodec.encodeVarint 33#64).length = 1 := by decide
  have hf1 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField1 x).length = 2 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField1_some x 2#32 rfl]; decide
  have hf2 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField2 x).length = 35 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField2_eq, List.length_cons,
      List.length_append, henc33,
      CryptoVerification.E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.bkBytes_length]
  have hf3 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField3 x).length = 35 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField3_eq, List.length_cons,
      List.length_append, henc33,
      CryptoVerification.E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.ikBytes_length]
  have hf4 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField4 x).length = 4 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField4_eq x (by decide)]; decide
  have hf5 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField5 x).length = 2 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField5_eq]; decide
  have hf6 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField6 x).length = 2 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField6_eq]; decide
  have hf7 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField7 x).length = 2 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField7_eq]; decide
  have hf8 : (CryptoVerification.E2E.Pqxdh.ResponderWire.psmField8 x).length = 1572 := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderWire.psmField8_eq,
      CryptoVerification.E2E.Pqxdh.ResponderWire.encodeVarint_1569, List.length_cons,
      List.length_append,
      CryptoVerification.E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.kyberBytes_length]
    decide
  change (wirePrekey :: WirePksmTightCredit.pksmNonVacFields.bytes).length ≤ msgCapBytes
  rw [List.length_cons, hb,
    CryptoVerification.E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.bytes,
    List.length_cons, CryptoVerification.E2E.Pqxdh.ResponderWire.protoBytes_eq_psmRem0]
  simp only [CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem0,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem1,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem2,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem3,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem4,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem5,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem6,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem7,
    CryptoVerification.E2E.Pqxdh.ResponderWire.psmRem8,
    List.length_append, List.length_nil, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, msgCapBytes]
  decide

/-- Constructs concrete `(nonVacPEParams, nonVacRecvPrekeyCall, fullLog)` satisfying
`CliPqRealCallDomain` and `CliMainEnv` over `CliRunOpenedEnv` on the `3#8` `recv-prekey` arm with
`AllocEvent.alloc 72 ∈ fullLog` and `AllocEvent.realloc 1 2048 1569 ∈ fullLog`. -/
theorem cliPqRealCallDomain_recvPrekey_nonvacuous
    (E : PEParams → RunCall → CliRunCalleeEnvs)
    (hpksm : ∀ P g, (E P g).pksmEnv = WirePksmTightCredit.PksmCanonSliceEnv) :
    ∃ (P₀ : PEParams) (g₀ : RunCall) (fullLog : List AllocEvent),
      CliPqRealCallDomain P₀ g₀ ∧
      CliMainEnv uuidTryParse
        (fun g' => CliRunOpenedEnv cliIo.rd (E P₀ g') sessionCapBytes g')
        g₀ none false [] false fullLog ∧
      AllocEvent.alloc 72 ∈ fullLog ∧
      AllocEvent.realloc 1 2048 1569 ∈ fullLog := by
  let g₀ := nonVacRecvPrekeyCall
  let evsCoins : List AllocEvent :=
    match CryptoVerification.SignalSession.CliExt.readFileResult
        (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs g₀.i)).files
        (utf8 "coins") with
    | Except.ok bs => LibsignalBinary.Heap.SpecBudget.allocBytes1Events bs
    | Except.error () => []
  let fullLog := evsCoins ++ WirePksmTightCredit.pksmNonVacEvents
  refine ⟨nonVacPEParams, g₀, fullLog, ?_, ?_, ?_, ?_⟩
  · have hsess : SessionRecordCapInDomain nonVacPEParams sessionCapBytes :=
      fun _ _ _ hr => False.elim (nonVacPEParams_not_reachable hr)
    have hbk : PqPartyBaseKeysCap sessionCapBytes nonVacBobParty := by
      intro _ _ _ hmem
      nomatch hmem
    have hparse : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c :=
      CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv .A
    have hinit : ∀ peer dir, g₀.c = .init peer dir → dir.length ≤ 26 ∧
        (∀ name bs, cliIo.rd (runFiles g₀.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637) := by
      intro _ _ hc
      nomatch hc
    exact ⟨nonVacBobParty, nonVacBobParty_inSpecDomain,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨WirePksmTightCredit.pksmNonVacFields, 0#256, by decide, rfl⟩))),
      hsess, hbk, nonVacStdin_length_le_msgCap, hparse, hinit⟩
  · have hM1 : CliMainPeakSpec.M1PhaseEnv g₀.i.argv.length [] := Or.inl rfl
    have hM2 : CliMainPeakSpec.M2CollectEnv g₀.i.argv.length [] := by
      have hlen : g₀.i.argv.length = 2 := rfl
      rw [hlen]
      exact Or.inr ⟨[], [], rfl, Or.inl rfl, Or.inr ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩
    have hRf : LibsignalBinary.Heap.SpecBudget.ReadFileEnv
        (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs g₀.i)).files
        (utf8 "coins") evsCoins := by
      refine LibsignalBinary.Heap.SpecBudget.readFileEnv_of_hook _ _ ?_
      dsimp only [evsCoins]
      cases CryptoVerification.SignalSession.CliExt.readFileResult
          (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs g₀.i)).files
          (utf8 "coins") with
      | ok _ => rfl
      | error u => cases u; rfl
    have hM3 : CliMainPeakSpec.M3PhaseEnv false g₀.i.stdin
        (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs g₀.i)).files
        (utf8 "coins") evsCoins :=
      Or.inr ⟨[], evsCoins, rfl, rfl,
        Or.inr ⟨evsCoins, [], (List.append_nil _).symm, hRf, FreeOnlyEvs.nil⟩⟩
    have hSetup : CliMainPeakSpec.CliMainSetupEnv uuidTryParse g₀.i none false evsCoins :=
      Or.inr ⟨[], evsCoins, rfl, hM1,
        Or.inr ⟨[], evsCoins, rfl, hM2,
          Or.inr ⟨[], evsCoins, rfl, rfl, hM3⟩⟩⟩
    have hArm : RunArmEnv cliIo.rd (runFiles g₀.i) (E nonVacPEParams g₀) sessionCapBytes g₀.i.stdin g₀.c
        WirePksmTightCredit.pksmNonVacEvents := by
      change RecvArmEnv (wirePrekey :: WirePksmTightCredit.pksmNonVacFields.bytes)
        (E nonVacPEParams g₀).decSigEnv (E nonVacPEParams g₀).pksmEnv (E nonVacPEParams g₀).decPkEnv
        WirePksmTightCredit.pksmNonVacEvents
      rw [hpksm nonVacPEParams g₀]
      unfold RecvArmEnv wirePrekey
      have hb2 : (3#8 : BitVec 8) ≠ 2#8 := by decide
      simp only [hb2, ↓reduceIte]
      exact Or.inr (Or.inr ⟨WirePksmTightCredit.pksmNonVacEvents, [], (List.append_nil _).symm,
        WirePksmTightCredit.pksmNonVacEvents_mem_slice, Or.inl FreeOnlyEvs.nil⟩)
    have hRun : CliRunOpenedEnv cliIo.rd (E nonVacPEParams g₀) sessionCapBytes g₀
        WirePksmTightCredit.pksmNonVacEvents := by
      simpa only [List.nil_append] using
        (CliRunArmsPeak.cliRunOfR0Env_of_r0_arm
          (R0StageEnv := CliRunArmsPeak.R0OpenedEnv cliIo.rd (runFiles g₀.i))
          (Or.inl FreeOnlyEvs.nil) hArm)
    have hM5 : CliMainPeakSpec.M5PhaseEnv [] [] :=
      Or.inr ⟨[], [], rfl, rfl, FreeOnlyEvs.nil⟩
    have hM6 : CliMainPeakSpec.M6Env false [] :=
      Or.inr ⟨[], [], rfl, rfl, FreeOnlyEvs.nil⟩
    exact Or.inr ⟨evsCoins, WirePksmTightCredit.pksmNonVacEvents, rfl, hSetup,
      Or.inr (Or.inr ⟨WirePksmTightCredit.pksmNonVacEvents, [], (List.append_nil _).symm, hRun,
        Or.inr ⟨[], [], rfl, hM5, hM6⟩⟩)⟩
  · exact List.mem_append_right _ WirePksmTightCredit.pksmNonVacEvents_allocating.1
  · exact List.mem_append_right _ WirePksmTightCredit.pksmNonVacEvents_allocating.2.1

/-- Specialization of `cliPqRealCallDomain_recvPrekey_nonvacuous` to `mkRealCalleeEnvs`. -/
theorem cliPqRealCallDomain_mkRealCalleeEnvs_recvPrekey_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image)
    (rd : RunCall → ReadRule)
    (x : RunCall → CryptoVerification.SignalSession.Cli.RunCompose.InitGhost)
    (ownKeyName ownRegName : RunCall → List (BitVec 8))
    (F : RunCall → CryptoGames.LibsignalSession.ShaCompress)
    (x_spqr : RunCall → CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost)
    (g_rec : RunCall → CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (r_rec : RunCall → CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (w1R : RunCall → W1SendRealParams)
    (w2R : RunCall → W2RecvWhisperRealParams)
    (w4R : RunCall → W4RecvPrekeyRealParams) :
    ∃ (P₀ : PEParams) (g₀ : RunCall) (fullLog : List AllocEvent),
      CliPqRealCallDomain P₀ g₀ ∧
      CliMainEnv uuidTryParse
        (fun g' => CliRunOpenedEnv cliIo.rd
          (mkRealCalleeEnvs img P₀ g' (rd g') (x g') (ownKeyName g') (ownRegName g')
            (F g') (x_spqr g') (g_rec g') (r_rec g')
            (w1R g') (w2R g') (w4R g'))
          sessionCapBytes g')
        g₀ none false [] false fullLog ∧
      AllocEvent.alloc 72 ∈ fullLog ∧
      AllocEvent.realloc 1 2048 1569 ∈ fullLog :=
  cliPqRealCallDomain_recvPrekey_nonvacuous _ (fun _ _ => rfl)

end LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
