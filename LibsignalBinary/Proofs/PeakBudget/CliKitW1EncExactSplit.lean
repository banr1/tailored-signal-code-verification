/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendAuxR2
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget

/-!
# Decomposition of Guarded-Tight `W1` (`encrypt` `@109`) Exact Slot

**Checked by Lean.**

Decomposes `ckx2_w1EncExact_phaseCredit_Stmt` and `ckx2_w1EncExact_groupSpec_Stmt` into four
sub-obligations—domain guard (`w1x_guard_Stmt`), implication-guard lift (`w1x_lift_Stmt`),
unguarded credit core (`w1x_creditCore_Stmt`), and unguarded group core (`w1x_groupCore_Stmt`)—and
proves their parametric assembly.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq w1EncExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_DecodeStateTightEnv ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv
   ckx2_cliEncryptBinaryKitSlotEnvExact ckx2_w1EncExact_groupSpec_Stmt
   ckx2_w1EncExact_phaseCredit_Stmt ckx2_w1EncExact_singleSlotFineSpec_of_stmts)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments (OtrEncryptStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak (WithStoresEncTightEnv)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot (w1CtLenCap w1PkOutCap w1SmSerCap)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv kyberPayloadLen signalMessageNewSerLen)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

/-! ## `@109` Send Envelope and Guard Definitions -/

/-- Exact `@109` `spqr::send::<Coins>` byte-slice envelope inside `ckx2_cliEncryptBinaryKitSlotEnvExact`
(`rfl`-equal to the `let sendEnv` binding in `ckx2_cliEncryptBinaryKitSlotEnvExact`). -/
def w1x_sendEnv109 (W : CliHooks) : SpqrSendBudgetEnv :=
  ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K
    (fun _ => ckx2_DecodeStateTightEnv)
    (fun _ => StatesFromPbTightEnv)

/-- Guard on `<SignalMessage>::new` ghost lengths under `ptext.length ≤ msgCapBytes` and `pqrMsg.length ≤ 64`. -/
def w1x_SigGuard
    (_r : SessionRecord (List (BitVec 8))) (_sess : Session (List (BitVec 8)))
    (_otr : OutgoingTripleRatchet (List (BitVec 8))) (_taken : SessionState (List (BitVec 8)))
    (g : SignalMessageNewGhost) : Prop :=
  g.ciphertext.length ≤ w1CtLenCap ∧
    g.pqRatchet.length ≤ 4096 ∧
    signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap

/-- Guard on `<PreKeySignalMessage>::new` ghost lengths under `scopeKit` (`kyber ≤ 1569`) and `ptext ≤ msgCapBytes`. -/
def w1x_PkCallGuard
    (_r : SessionRecord (List (BitVec 8))) (_sess : Session (List (BitVec 8)))
    (_otr : OutgoingTripleRatchet (List (BitVec 8))) (_taken : SessionState (List (BitVec 8)))
    (call : PreKeyMsgNewCall) : Prop :=
  kyberPayloadLen call.kp ≤ 1569 ∧
    call.msg.serialized.length ≤ w1SmSerCap ∧
    call.model.serialized.length ≤ w1PkOutCap

/-- Placed `WithStoresEncTightEnv` specialization on `(runFiles g.i, w1R.peer)` with `w1x_sendEnv109 W`. -/
noncomputable def W1X_WithStoresEncTight [LibsignalPlacement]
    (W : CliHooks) (g : RunCall) (w1R : W1BinarySendParams) :
    List AllocEvent → Prop :=
  let F0 := runFiles g.i
  let gx := w1EncGhost w1R.x
  let kit := w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer
  let kitEnv := w1BinarySessKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer
  let ikit := w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer
  let ikitEnv := w1BinaryIdKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer
  WithStoresEncTightEnv scopeKit
    kit kitEnv StoresGhost.opened.sessions
    ikit ikitEnv StoresGhost.opened.identity
    W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx
    (fun r sess otr taken =>
      OtrEncryptStepEnv (w1x_sendEnv109 W otr.pqrState gx.rest) gx.ptext.length
        (fun evs => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs))
    (fun r sess otr taken =>
      OtrEncryptStepEnv (w1x_sendEnv109 W otr.pqrState gx.rest) gx.ptext.length
        (fun evs => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs))
    (fun r sess otr taken evs =>
      ∃ call, w1x_PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs)

/-! ## Sub-Obligation Statements -/

/-- `CliPqxdhInputs`, `.send peerV` CLI parse, and `W1BinarySendDom` imply
`PeerSpqrStateTight640 W.C.F W.Q.K w1R.x.F w1R.x.peer.val`. -/
def w1x_guard_Stmt (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (w1R : W1BinarySendParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
    W1BinarySendDom (.send peerV) g.i w1R →
    PeerSpqrStateTight640 W.C.F W.Q.K w1R.x.F w1R.x.peer.val

def w1x_liftCredit_Stmt : Prop :=
  ∀ {M : AllocCostModel} [HasFineReallocCredit M] {G : Prop} {E : List AllocEvent → Prop}
    {c l p r : Nat},
    G → PhaseCreditSpec M E c l p r → PhaseCreditSpec M (fun evs => G → E evs) c l p r

def w1x_liftGroup_Stmt : Prop :=
  ∀ {M : AllocCostModel} [HasFineGroupCredit M] {G : Prop} {E : List AllocEvent → Prop} {grpS : Nat},
    G → PhaseGroupSpec M E grpS → PhaseGroupSpec M (fun evs => G → E evs) grpS

/-- Implication-guard lift for `PhaseCreditSpec` and `PhaseGroupSpec` over `fun evs => G → E evs`. -/
def w1x_lift_Stmt : Prop :=
  w1x_liftCredit_Stmt ∧ w1x_liftGroup_Stmt

/-- Unguarded `CliEncryptSlotEnv` `@109` `PhaseCreditSpec` obligation under `CliPqxdhInputs`,
`.send peerV` parse, `PeerSpqrStateTight640`, `w1R.repAlloc = A.repAlloc`, and `W1BinarySendDom`. -/
def w1x_creditCore_Stmt [LibsignalPlacement] (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
    PeerSpqrStateTight640 W.C.F W.Q.K w1R.x.F w1R.x.peer.val →
    w1R.repAlloc = A.repAlloc →
    W1BinarySendDom (.send peerV) g.i w1R →
    PhaseCreditSpec fineCostModel
      (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A w1R.B (w1x_sendEnv109 W)
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc w1R.B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc w1R.B)
        w1R.x)
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq

/-- Unguarded `CliEncryptSlotEnv` `@109` `PhaseGroupSpec` obligation under `CliPqxdhInputs`,
`.send peerV` parse, `PeerSpqrStateTight640`, `w1R.repAlloc = A.repAlloc`, and `W1BinarySendDom`. -/
def w1x_groupCore_Stmt [LibsignalPlacement] (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
    PeerSpqrStateTight640 W.C.F W.Q.K w1R.x.F w1R.x.peer.val →
    w1R.repAlloc = A.repAlloc →
    W1BinarySendDom (.send peerV) g.i w1R →
    PhaseGroupSpec fineCostModel
      (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A w1R.B (w1x_sendEnv109 W)
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc w1R.B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc w1R.B)
        w1R.x)
      w1EncExactGrpS

/-! ## Parametric Assembly -/

/-- Assembles `ckx2_w1EncExact_phaseCredit_Stmt` from `w1x_guard_Stmt`, `w1x_lift_Stmt`, and `w1x_creditCore_Stmt`. -/
theorem ckx2_w1EncExact_phaseCredit_of_w1x [LibsignalPlacement] (W : CliHooks)
    (hG : w1x_guard_Stmt W) (hL : w1x_lift_Stmt) (hC : w1x_creditCore_Stmt W) :
    ckx2_w1EncExact_phaseCredit_Stmt W := by
  intro g peerV M A w1R hi hp _hc hrep hdom
  have hGuard := hG g peerV w1R hi hp hdom
  exact hL.1 hGuard (hC g peerV M A w1R hi hp hGuard hrep hdom)

/-- Assembles `ckx2_w1EncExact_groupSpec_Stmt` from `w1x_guard_Stmt`, `w1x_lift_Stmt`, and `w1x_groupCore_Stmt`. -/
theorem ckx2_w1EncExact_groupSpec_of_w1x [LibsignalPlacement] (W : CliHooks)
    (hG : w1x_guard_Stmt W) (hL : w1x_lift_Stmt) (hGr : w1x_groupCore_Stmt W) :
    ckx2_w1EncExact_groupSpec_Stmt W := by
  intro g peerV M A w1R hi hp _hc hrep hdom
  have hGuard := hG g peerV w1R hi hp hdom
  exact hL.2 hGuard (hGr g peerV M A w1R hi hp hGuard hrep hdom)

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
