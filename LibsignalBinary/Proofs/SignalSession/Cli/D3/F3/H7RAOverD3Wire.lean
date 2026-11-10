/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
public import LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
public import LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie
public import LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAgreePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3AssemblyFresh
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# End-to-End `Out1Dom`-Parametric `MainOkOverD3F3` Assembly

**Checked by Lean.**

Assembles `MainOkOverD3F3` end-to-end, parametric in the post-decryption session predicate
`Out1Dom`, the `SessionGhostValid`-carrying `OverD3` slot-520 envelope, and the `Out1Dom` target
phase-credit and phase-group bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire

open Arm64 (GhostName HookOk Memory subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (bytesOfString)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (IdentityKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (
  PreKeySignalMessage Session SessionRecord StoreCall fullTrace messageDecryptSignal_trace_prefix
)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
  libsignalSessionExterns lsProg_51 lsρ withLsCl
)
open CryptoVerification.E2E (
  PEParams UnreachedPqxdhPrimitives aesDecHookMallocng partyAddressName pqxdhSpqrModel
  recvPrekeyState wirePrekey wireWhisper
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost serviceIdParse uuidTryParse
)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhInputs Inputs baseKeysFile cliExternsPlaced identityFile libsignalSessionLib
  lsReadFileSym oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress pqInitInputs pqRecvInputs
  pqSendInputs sessionFile stdinCapBytes
)
open CryptoVerification.SignalSession.Cli (
  DirGhost IdGhost KyberGhost StoresGhost addressText baseKeysName keyName pathOf removePreKey utf8
)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV DirWrOk RunCall StoreCallPeerPlaced StoresWrOk cliIo cliMainStk cliResStack cliRunBudgets
  cliRunNeeds cliRunSemD2c_placed cliWrOk inputOf keyName_length
  messageDecryptSignal_calls_peer_placed mainFrameSize namedWrites namedWrites_ascii okPeerPath
  parseArgs saveUpd_own saveUpd_peers_path
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost DecSigGhost EncGhost Init2Data SlotAns addrValOf finish mkSlot runAns runRel
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (
  SessMatchesPm cliAnswers cliFinal cliDecryptPrekeyNeed cliStep decPkDef decSigDef decSigKey
  initParty pkRecvCoins pkStoreKeys pkToE?
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (
  addrValE runAns_pqInit_eq runAns_pqRecvBad runAns_pqRecvPrekey_eq runAns_pqRecvWhisper_eq
  runAns_pqSend_eq
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (recv_rest_length_le_msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact (
  w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq w1EncExactPeak
  w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak
)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2 (
  ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact
  ckx2_w1EncExact_groupSpec_Stmt ckx2_w1EncExact_phaseCredit_Stmt
)
open LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race (
  ckx2_w2DecSigExact_groupSpec ckx2_w2DecSigExact_phaseCredit
)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W3BinaryInitParams)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0 (
  d3SlotMainFitsOneGiBOf mainEntryBudgetFitsCapOf_pqD3Recv_dom0
)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal (pqRunAns_namedWrites_bounds)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact (hmx_binaryKitRunSlotEnvsSlotOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W3InitBinaryKitSlotEnvFixed realCliInitBinarySlotEnvFixed
)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (
  peerSpqrStateTight640_of_pqOrD3Recv
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record (RecordStructure)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie (
  sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom
)
open LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps (pksmParse_lengths_le)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  decPkOverDef decPkOverDef_namedWrites_sub
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget (
  cliRunSemOverV4
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 (Block617TransferFixedHyp)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (MainOkOverD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  CliPqOrD3RecvInputs pqD3ScopedRun
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3AssemblyFresh (
  h7f_libsignalFullPlacementOfLinkedAt h7f_overD3_assembly_of_fitsCap h7f_pksmSlotOk_pksmTryFromEnv
  h7f_pksmTryFromEnv_congr
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob (
  DecPkD3ValidOverOfEnv' DecPkD3ValidOverTightConcreteEnv'
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAVerNeRawSlot520 (
  H7RADecPkOverEnvTwinFam H7RATightPollProducerAt h7ra_decPkOverConcreteTwinOf
  h7ra_decPkValidOverTwin_slot520_ok h7ra_tightPollProducerAt_decPkD3ValidOver
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (
  MainIoOfPlaced ReadStdinBoundedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (
  cliRunArmEnvs cliRunCalleesEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget (
  r2EncGhost r2PeerGhost0
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (
  r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget (
  CliInitSlotOkPlaced CliRunHooksBundle
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  PksmTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. `Out1Dom` Alias, Honest D3 `RunSlotEnvs`, & Main-Level Domain Dischargers -/

/-- Signature of `FreshBobPrev1Dom` and `PostBobPrev1Dom`. -/
abbrev H7RAOut1DomPred : Type :=
  Nat → Nat → Nat → SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop

/-- Guard asserting that the peer's existing session file deserializes under `StoresGhost.opened.sessions`. -/
def H7RAPrev0DeserializeGuard (x : DecPkGhost) : Prop :=
  ∃ bs orec,
    StoresGhost.opened.sessions.get cliIo.rd x.F (addressText x.peer.val) = .ok bs ∧
    RecordStructure.deserialize bs = .ok orec ∧
    (orec.map (·.previousSessions.length)).getD 0 = 0

/-- `RunSlotEnvs` over `ckx2_cliEncryptBinaryKitSlotEnvExact`,
`ckx2_cliDecryptSignalBinaryKitSlotEnvExact`, `realCliInitBinarySlotEnvFixed W`, and `DecPkOverTwinEnv`. -/
noncomputable def h7ra_honestOverD3FineSlotEnvs
    {mpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (mmpl : MultiPlacement) (brkStart : BitVec 64)
    (DecPkOverTwinEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunSlotEnvs :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  hmx_binaryKitRunSlotEnvsSlotOf
    (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (DecPkOverTwinEnv X W γ tp)

private theorem h7ra_w3InitFixed_congr [LibsignalPlacement] {w₁ w₂ : W3BinaryInitParams}
    (hpeer : w₁.x.peer = w₂.x.peer) (hxF : w₁.x.F = w₂.x.F)
    (hF : w₁.F = w₂.F) (hpk : w₁.peerKey = w₂.peerKey)
    (hspqr : w₁.x_spqr = w₂.x_spqr) (hg : w₁.g_rec = w₂.g_rec) (hr : w₁.r_rec = w₂.r_rec) :
    W3InitBinaryKitSlotEnvFixed w₁ = W3InitBinaryKitSlotEnvFixed w₂ := by
  funext evs
  unfold W3InitBinaryKitSlotEnvFixed
  rw [hpeer, hxF, hF, hpk, hspqr, hg, hr]

theorem h7ra_initEnv_r1c_congr [LibsignalPlacement]
    (W : CliHooks) (g : RunCall) (d2 : Init2Data) (fsp : BitVec 64) :
    realCliInitBinarySlotEnvFixed W (r1cInitGhost g d2 fsp) =
      realCliInitBinarySlotEnvFixed W (r1cInitGhost g d2 0#64) := by
  funext evs
  apply propext
  constructor
  · rintro ⟨w, hx, hF, hspqr, hgv, halice, hslot⟩
    refine ⟨{ w with x := r1cInitGhost g d2 0#64 }, rfl, hF, hspqr, hgv, halice, ?_⟩
    have heq := h7ra_w3InitFixed_congr (w₁ := w) (w₂ := { w with x := r1cInitGhost g d2 0#64 })
      (by rw [hx]; rfl) (by rw [hx]; rfl) rfl rfl rfl rfl rfl
    exact Eq.mp (congrFun heq evs) hslot
  · rintro ⟨w, hx, hF, hspqr, hgv, halice, hslot⟩
    refine ⟨{ w with x := r1cInitGhost g d2 fsp }, rfl, hF, hspqr, hgv, halice, ?_⟩
    have heq := h7ra_w3InitFixed_congr (w₁ := w) (w₂ := { w with x := r1cInitGhost g d2 fsp })
      (by rw [hx]; rfl) (by rw [hx]; rfl) rfl rfl rfl rfl rfl
    exact Eq.mp (congrFun heq evs) hslot

/-- Ciphertext length bound `pm.message.ciphertext.length ≤ msgCapBytes` on `.recv` `3#8 :: rest`. -/
theorem h7ra_pksmParse_ct_le_msgCapBytes
    {g : RunCall} {peerV : AddrV} {rest : List (BitVec 8)} {pm : PreKeySignalMessage}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : pksmParse rest = some pm) :
    pm.message.ciphertext.length ≤ msgCapBytes :=
  Nat.le_trans (pksmParse_lengths_le hpk).2.2.1 (recv_rest_length_le_msgCapBytes hin hc hst)

theorem h7ra_peerSpqrStateTight640_r3b
    {W : CliHooks} {g : RunCall} {meV peerV : AddrV} {pm : PreKeySignalMessage}
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV)) :
    PeerSpqrStateTight640 W.C.F W.Q.K
      (r3bDecPkGhost g meV peerV pm).F (r3bDecPkGhost g meV peerV pm).peer.val :=
  peerSpqrStateTight640_of_pqOrD3Recv hi hparse

/-- Discharges `H7RAPrev0DeserializeGuard` on `r3bDecPkGhost g meV peerV pm` from `CliPqOrD3RecvInputs`. -/
theorem h7ra_prev0Guard_r3b
    {W : CliHooks} {g : RunCall} {meV peerV : AddrV} {pm : PreKeySignalMessage}
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV)) :
    H7RAPrev0DeserializeGuard (r3bDecPkGhost g meV peerV pm) :=
  sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom hi hparse

section NwDomOverV4

private theorem h7ra_identityFile_len_le_64 (P : Party) :
    (identityFile (partyAddressName P)).length ≤ 64 := by
  cases P <;> decide

private theorem h7ra_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private def h7ra_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem h7ra_utf8_eq_kutf8 (s : String) : utf8 s = h7ra_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, h7ra_kutf8, List.utf8Encode, h7ra_byteArray_toList_eq_data]

private theorem h7ra_utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [h7ra_utf8_eq_kutf8, h7ra_utf8_eq_kutf8, h7ra_utf8_eq_kutf8]
  simp [h7ra_kutf8, String.toList_append, List.flatMap_append]

private theorem h7ra_pathOf_id_addrValE (P : Party) :
    pathOf (utf8 "identities") (addrValE P).name = utf8 (identityFile (partyAddressName P)) := by
  have hne : utf8 "identities" ≠ [] := by rw [h7ra_utf8_eq_kutf8]; decide
  simp only [pathOf, hne, ↓reduceIte, addrValE, identityFile]
  rw [← h7ra_utf8_append, ← h7ra_utf8_append]
  rfl

private theorem h7ra_pathOf_sess_addrValE (P : Party) :
    pathOf (utf8 "sessions") (addressText (addrValE P)) =
      utf8 (sessionFile (partyAddress P)) := by
  have hne : utf8 "sessions" ≠ [] := by rw [h7ra_utf8_eq_kutf8]; decide
  have had : addressText (addrValE P) = utf8 (partyAddress P).text := by
    have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
    simp only [addressText, addrValE, CryptoVerification.SignalSession.Cli.decimalText, h1,
      CryptoVerification.SignalSession.Address.text, partyAddress]
    rw [← h7ra_utf8_append, ← h7ra_utf8_append]
  rw [had]
  simp only [pathOf, hne, ↓reduceIte, sessionFile]
  rw [← h7ra_utf8_append, ← h7ra_utf8_append]
  rfl

private theorem h7ra_okPeerPath_id (P : Party) :
    okPeerPath P (pathOf (utf8 "identities") (addrValE P).name) := by
  rw [h7ra_pathOf_id_addrValE]
  refine ⟨?_, .inl ?_⟩
  · rw [h7ra_utf8_eq_kutf8]
    intro b hb
    have hall :
        (h7ra_kutf8 (identityFile (partyAddressName P))).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [h7ra_utf8_eq_kutf8]
    cases P <;> decide

private theorem h7ra_utf8_inj {s₁ s₂ : String} (h : utf8 s₁ = utf8 s₂) : s₁ = s₂ := by
  have hmap := congrArg (List.map UInt8.ofBitVec) h
  have hrt : ∀ b : UInt8, UInt8.ofBitVec (BitVec.ofNat 8 b.toNat) = b := fun b => by
    simp [UInt8.ofBitVec_toBitVec]
  simp only [utf8, List.map_map, Function.comp_def, hrt, List.map_id'] at hmap
  have hba : s₁.toByteArray = s₂.toByteArray := by
    rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
    rcases hs1 : s₁.toUTF8 with ⟨⟨xs₁⟩⟩
    rcases hs2 : s₂.toUTF8 with ⟨⟨xs₂⟩⟩
    rw [hs1, hs2, h7ra_byteArray_toList_eq_data, h7ra_byteArray_toList_eq_data] at hmap
    dsimp only at hmap
    subst hmap
    rfl
  exact String.toByteArray_inj.mp hba

private theorem h7ra_sessionFile_partyAddress_eq (P : Party) :
    sessionFile (partyAddress P) = "sessions/" ++ partyAddressName P ++ "." ++ "1" := by
  have h1 : toString (1 : Nat) = "1" := by
    apply h7ra_utf8_inj
    have hdt : utf8 (toString (1 : Nat)) = [BitVec.ofNat 8 (0x30 + 1)] :=
      CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit 1 (by omega)
    have hu1 : utf8 "1" = [BitVec.ofNat 8 (0x30 + 1)] := by
      rw [h7ra_utf8_eq_kutf8]; decide
    exact hdt.trans hu1.symm
  simp only [sessionFile, partyAddress, CryptoVerification.SignalSession.Address.text, h1,
    String.append_assoc]

private theorem h7ra_okPeerPath_sess (P : Party) :
    okPeerPath P (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  rw [h7ra_pathOf_sess_addrValE]
  refine ⟨?_, .inr ?_⟩
  · rw [h7ra_utf8_eq_kutf8, h7ra_sessionFile_partyAddress_eq]
    intro b hb
    have hall :
        (h7ra_kutf8 ("sessions/" ++ partyAddressName P ++ "." ++ "1")).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [h7ra_utf8_eq_kutf8, h7ra_sessionFile_partyAddress_eq]
    cases P <;> decide

private theorem h7ra_list_length_le_flatMap_utf8EncodeChar :
    ∀ l : List Char, l.length ≤ (l.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | c :: cs => by
    have hc : 1 ≤ (String.utf8EncodeChar c).length := by
      unfold String.utf8EncodeChar
      dsimp only
      by_cases h1 : c.val.toNat ≤ 127
      · simp only [h1, ↓reduceIte, List.length_cons, List.length_nil]; omega
      · by_cases h2 : c.val.toNat ≤ 2047
        · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]; omega
        · by_cases h3 : c.val.toNat ≤ 65535
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
    have ih := h7ra_list_length_le_flatMap_utf8EncodeChar cs
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

private theorem h7ra_string_length_le_utf8_length (s : String) : s.length ≤ (utf8 s).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  rw [String.length_ofList]
  have hutf : (utf8 (String.ofList l)).length = (l.flatMap String.utf8EncodeChar).length := by
    simp [utf8, List.utf8Encode, h7ra_byteArray_toList_eq_data]
  rw [hutf]
  exact h7ra_list_length_le_flatMap_utf8EncodeChar l

private theorem h7ra_u32_toString_len_le_10 (id : BitVec 32) :
    (toString id.toNat).length ≤ 10 :=
  Nat.le_trans (h7ra_string_length_le_utf8_length (toString id.toNat)) (keyName_length id)

private theorem h7ra_sessionFile_len_le_64 (P : Party) :
    (sessionFile (partyAddress P)).length ≤ 64 := by
  rw [h7ra_sessionFile_partyAddress_eq]
  cases P <;> decide

private theorem h7ra_oneTimeKyberPreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimeKyberPreKeyFile id).length ≤ 64 := by
  have h := h7ra_u32_toString_len_le_10 id
  unfold oneTimeKyberPreKeyFile
  rw [String.length_append]
  have hp : ("one-time-kyber-pre-keys/").length = 24 := by decide
  omega

private theorem h7ra_baseKeysFile_len_le_64 (id : BitVec 32) :
    (baseKeysFile id).length ≤ 64 := by
  have h := h7ra_u32_toString_len_le_10 id
  unfold baseKeysFile
  simp only [String.length_append]
  have hp1 : ("last-resort-kyber-pre-keys/").length = 27 := by decide
  have hp2 : (".base-keys").length = 10 := by decide
  omega

private theorem h7ra_oneTimePreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimePreKeyFile id).length ≤ 64 := by
  have h := h7ra_u32_toString_len_le_10 id
  unfold oneTimePreKeyFile
  rw [String.length_append]
  have hp : ("one-time-pre-keys/").length = 18 := by decide
  omega

private theorem h7ra_setOrPush_length_le_succ
    (xs : List (List (BitVec 8) × List (BitVec 8))) (k v : List (BitVec 8)) :
    (DirGhost.setOrPush k v xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [DirGhost.setOrPush]
  | cons _ _ ih =>
    unfold DirGhost.setOrPush
    split <;> [simp; (simp only [List.length_cons]; omega)]

private theorem h7ra_dirPut_writes_length_le_succ (d : DirGhost) (k v : List (BitVec 8)) :
    (d.put k v).writes.length ≤ d.writes.length + 1 := by
  simp only [DirGhost.writes, DirGhost.put, List.length_map]
  exact h7ra_setOrPush_length_le_succ d.changed k v

private theorem h7ra_saveUpd_peers_writes_length_le_succ (F : FsFiles)
    (idG : IdGhost) (rem : AddrVal) (k : IdentityKey) :
    (idG.saveUpd cliIo.rd F rem k).peers.writes.length ≤ idG.peers.writes.length + 1 ∧
      (idG.saveUpd cliIo.rd F rem k).own = idG.own := by
  refine ⟨?_, saveUpd_own cliIo.rd F idG rem k⟩
  unfold IdGhost.saveUpd
  split
  · exact h7ra_dirPut_writes_length_le_succ idG.peers rem.name k.serialize
  · exact Nat.le_succ _

private theorem h7ra_foldl_cliStep_writes_length_le (F : FsFiles) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (calls.foldl (cliStep F) g).writes.length ≤ g.writes.length + calls.length
  | [], g => by simp
  | c :: cs, g => by
    have h1 : (cliStep F g c).writes.length ≤ g.writes.length + 1 := by
      cases c with
      | loadSession _ | isTrustedIdentity _ _ _ => exact Nat.le_succ _
      | saveIdentity rem k =>
        obtain ⟨hp, ho⟩ := h7ra_saveUpd_peers_writes_length_le_succ F g.identity rem k
        dsimp only [cliStep, StoresGhost.writes]; rw [ho]; simp only [List.length_append]; omega
      | storeSession rem r =>
        dsimp only [cliStep, StoresGhost.writes]
        have hs := h7ra_dirPut_writes_length_le_succ g.sessions (addressText rem)
          (CryptoVerification.E2E.Record.encodeRecord r)
        simp only [List.length_append]; omega
    have h2 := h7ra_foldl_cliStep_writes_length_le F cs (cliStep F g c)
    dsimp only [List.foldl, List.length_cons]
    omega

private theorem h7ra_storesWrOk_foldl (F : FsFiles) (P : Party) :
    ∀ (cs : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ cs, StoreCallPeerPlaced (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = utf8 "identities" →
      g.sessions.path = utf8 "sessions" →
      StoresWrOk (okPeerPath P) (cs.foldl (cliStep F) g) := by
  intro cs
  induction cs with
  | nil => intro g _ hg0 _ _; exact hg0
  | cons c cs' ih =>
    intro g hcs hg0 hp hs
    have hc1 := hcs c List.mem_cons_self
    cases c with
    | loadSession _ | isTrustedIdentity _ _ _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | saveIdentity rem _k =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with
          own := by rw [saveUpd_own]; exact hg0.own
          peers := DirWrOk.saveUpd hg0.peers (hp ▸ h7ra_okPeerPath_id P) }
        (by rw [saveUpd_peers_path, hp]) hs
    | storeSession rem _r0 =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with sessions := hg0.sessions.put (hs ▸ h7ra_okPeerPath_sess P) _ } hp hs

private theorem h7ra_decSigDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold decSigDef at h
  split at h
  · next _pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨_k, _r, -, hpref⟩ :=
      messageDecryptSignal_trace_prefix W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := h7ra_foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]; omega
  · cases h
  · cases h

private theorem h7ra_storesWrOk_decSigDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next _pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageDecryptSignal_calls_peer_placed
      W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
      msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hc
    exact h7ra_storesWrOk_foldl F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

private theorem h7ra_kyberMark_writes_length_le_1
    {F : FsFiles} {kpkId spkId : BitVec 32} {bk : CryptoGames.LibsignalSession.PublicKey}
    {kyber' : KyberGhost}
    (hkm : StoresGhost.opened.kyber.mark cliIo.rd F kpkId spkId bk = (.ok (), kyber')) :
    kyber'.oneTime.writes.length + kyber'.lastResort.writes.length ≤ 1 := by
  unfold KyberGhost.mark at hkm
  cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F (keyName kpkId) with
  | error _ => rw [hot] at hkm; cases hkm
  | ok bs =>
    rw [hot] at hkm
    cases bs with
    | cons _ _ =>
      dsimp only at hkm; injection hkm with _ hk; subst hk; dsimp only
      have h1 := h7ra_dirPut_writes_length_le_succ StoresGhost.opened.kyber.oneTime (keyName kpkId) []
      have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
      have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
      omega
    | nil =>
      dsimp only at hkm
      cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName kpkId) with
      | error _ => rw [hlr] at hkm; cases hkm
      | ok seen =>
        rw [hlr] at hkm; dsimp only at hkm
        split at hkm
        · cases hkm
        · split at hkm
          · cases hkm
          · injection hkm with _ hk; subst hk; dsimp only
            have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
            have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
            rw [h0a, Nat.zero_add]
            exact Nat.le_trans (h7ra_dirPut_writes_length_le_succ _ _ _) (by rw [h0b])

private theorem h7ra_decPkDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h; dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h; dsimp only at h
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h; dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C
                  (CryptoVerification.E2E.pqxdhSpqrSession W)
                  ((CryptoVerification.E2E.pqxdhSessionParams W).expectedAddrs
                    (initParty (addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1; injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  obtain ⟨hp, ho⟩ := h7ra_saveUpd_peers_writes_length_le_succ F
                    StoresGhost.opened.identity (addrValE P) pm.identityKey
                  have hs := h7ra_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P))
                    (CryptoVerification.E2E.Record.encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                  have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  dsimp only [StoresGhost.writes]; rw [ho]
                  simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
                  omega
                | error err => cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h; dsimp only at h
          cases hpk : pkToE? pm with
          | none => rw [hpk] at h; cases h
          | some m =>
            rw [hpk] at h; dsimp only at h
            cases hsk : pkStoreKeys F m with
            | none => rw [hsk] at h; cases h
            | some k =>
              rw [hsk] at h
              cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
              | error _ => rw [hkp] at h; cases h
              | ok kp =>
                rw [hkp] at h
                cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                | error _ => rw [hreg] at h; cases h
                | ok reg =>
                  rw [hreg] at h; dsimp only at h
                  cases hrecv : recvPrekeyState X W
                      (initParty (addrValE P)) ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                  | none => rw [hrecv] at h; cases h
                  | some o =>
                    rw [hrecv] at h
                    cases o with
                    | none => cases h
                    | some triple =>
                      rcases triple with ⟨x, gs, _⟩
                      dsimp only at h
                      cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                          pm.signedPreKeyId pm.baseKey with
                      | mk kres kyber' =>
                        rw [hkm] at h
                        cases kres with
                        | error _ => cases h
                        | ok u =>
                          cases u; dsimp only at h
                          injection h with h1; injection h1 with h2
                          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                          have hkyb := h7ra_kyberMark_writes_length_le_1 hkm
                          obtain ⟨hp_le, ho⟩ := h7ra_saveUpd_peers_writes_length_le_succ F
                            StoresGhost.opened.identity (addrValE P) pm.identityKey
                          have hs_le := h7ra_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                            (addressText (addrValE P))
                            (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)
                          have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                          have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                          have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                          have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                          have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                          unfold StoresGhost.writes; dsimp only; rw [ho]
                          simp only [List.length_append, h0_own, h0_signed, h0_pub]
                          cases pm.preKeyId with
                          | none =>
                            dsimp only
                            have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                            omega
                          | some j =>
                            dsimp only; unfold removePreKey
                            cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                            | error _ =>
                              dsimp only
                              have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                              omega
                            | ok bs =>
                              cases bs with
                              | nil =>
                                dsimp only
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega
                              | cons _ _ =>
                                dsimp only
                                have hot_put := h7ra_dirPut_writes_length_le_succ
                                  StoresGhost.opened.oneTime (keyName j) []
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega

private theorem h7ra_decPkOverDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkOverDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkOverDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h; dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h; dsimp only at h
        cases hcur : r.bind (·.currentSession) with
        | none =>
          rw [hcur] at h
          exact h7ra_decPkDef_writes_len_le_4 h
        | some s =>
          rw [hcur] at h; dsimp only at h
          by_cases hm_s : SessMatchesPm s pm
          · rw [ite_eq_left hm_s] at h
            exact h7ra_decPkDef_writes_len_le_4 h
          · rw [ite_eq_right hm_s] at h
            cases hpk : pkToE? pm with
            | none => rw [hpk] at h; cases h
            | some m =>
              rw [hpk] at h; dsimp only at h
              cases hsk : pkStoreKeys F m with
              | none => rw [hsk] at h; cases h
              | some k =>
                rw [hsk] at h
                cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
                | error _ => rw [hkp] at h; cases h
                | ok kp =>
                  rw [hkp] at h
                  cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                  | error _ => rw [hreg] at h; cases h
                  | ok reg =>
                    rw [hreg] at h; dsimp only at h
                    cases hrecv : recvPrekeyState X W (initParty (addrValE P))
                        ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                    | none => rw [hrecv] at h; cases h
                    | some o =>
                      rw [hrecv] at h
                      cases o with
                      | none => cases h
                      | some triple =>
                        rcases triple with ⟨_x, gs, _⟩
                        dsimp only at h
                        cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                            pm.signedPreKeyId pm.baseKey with
                        | mk kres kyber' =>
                          rw [hkm] at h
                          cases kres with
                          | error _ => cases h
                          | ok u =>
                            cases u; dsimp only at h
                            injection h with h1; injection h1 with h2
                            obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                            have hkyb := h7ra_kyberMark_writes_length_le_1 hkm
                            obtain ⟨hp_le, ho⟩ := h7ra_saveUpd_peers_writes_length_le_succ F
                              StoresGhost.opened.identity (addrValE P) pm.identityKey
                            have hs_le := h7ra_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                              (addressText (addrValE P))
                              (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1
                                { state := gs.session, pendingPreKey := none, pendingKyberPreKey := none,
                                  localRegistrationId := reg, remoteRegistrationId := m.regId,
                                  aliceBaseKey := CryptoVerification.E2E.djbKey m.baseKey }
                                (CryptoVerification.E2E.Record.encSession
                                  (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.clearPending s)))
                            have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                            have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                            have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                            have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                            have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                            unfold StoresGhost.writes; dsimp only; rw [ho]
                            simp only [List.length_append, h0_own, h0_signed, h0_pub]
                            cases pm.preKeyId with
                            | none =>
                              dsimp only
                              have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                              omega
                            | some j =>
                              dsimp only; unfold removePreKey
                              cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                              | error _ =>
                                dsimp only
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega
                              | ok bs =>
                                cases bs with
                                | nil =>
                                  dsimp only
                                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                  omega
                                | cons _ _ =>
                                  dsimp only
                                  have hot_put := h7ra_dirPut_writes_length_le_succ
                                    StoresGhost.opened.oneTime (keyName j) []
                                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                  omega

private theorem h7ra_finish_inv {α : Type} {ans : SlotAns α}
    {outFn : α → List (BitVec 8)} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : finish ans outFn = some (some (ws, out))) :
    ∃ g' v, ans = some (some (g', v)) ∧ ws = namedWrites g'.writes ∧ out = outFn v := by
  cases ans with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some gv =>
      rcases gv with ⟨g', v⟩
      dsimp only [finish] at h
      injection h with h1; injection h1 with h2
      obtain ⟨hw, ho⟩ := Prod.mk.inj h2
      exact ⟨g', v, rfl, hw.symm, ho.symm⟩

private theorem h7ra_pqRecvInputs_nwDom
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (st : CryptoVerification.SignalSession.PqParty)
    (ct : List (BitVec 8)) (rc : BitVec 256)
    (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (ha : runAns (cliRunSemOverV4 X W) (pqRecvInputs ⟨W.C, W.Q⟩ st ct rc) =
      some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  cases ct with
  | nil =>
    rw [runAns_pqRecvBad (cliRunSemOverV4 X W) ⟨W.C, W.Q⟩ st [] rc (by decide) (by decide)] at ha
    cases ha
  | cons t rest =>
    by_cases ht2 : t = wireWhisper
    · subst ht2
      have hdecSig : (cliRunSemOverV4 X W).decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn := rfl
      rw [runAns_pqRecvWhisper_eq (cliRunSemOverV4 X W) ⟨W.C, W.Q⟩ st rest rc, hdecSig] at ha
      cases hsm : SignalMessage.tryFrom protoSignalCodec rest with
      | error _ => rw [hsm] at ha; cases ha
      | ok msg =>
        rw [hsm] at ha; dsimp only at ha
        obtain ⟨g', v, hg, rfl, _⟩ := h7ra_finish_inv ha
        have hlen4 : g'.writes.length ≤ 4 := h7ra_decSigDef_writes_bounds hg
        have hwr : StoresWrOk (okPeerPath st.party.other) g' := h7ra_storesWrOk_decSigDef hg
        refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
        have hasc : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
          fun w hw => (hwr.writes w hw).1
        rw [namedWrites_ascii g'.writes hasc] at hq
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
        rcases (hwr.writes w hw).2 with hp | hp <;> rw [hp]
        · exact h7ra_identityFile_len_le_64 st.party.other
        · exact h7ra_sessionFile_len_le_64 st.party.other
    · by_cases ht3 : t = wirePrekey
      · subst ht3
        have hpksm : (cliRunSemOverV4 X W).pksmParse = pksmParse := rfl
        have hdecPk : (cliRunSemOverV4 X W).decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn := rfl
        rw [runAns_pqRecvPrekey_eq (cliRunSemOverV4 X W) ⟨W.C, W.Q⟩ st rest rc, hpksm, hdecPk] at ha
        cases hpm : pksmParse rest with
        | none => rw [hpm] at ha; cases ha
        | some pm =>
          rw [hpm] at ha; dsimp only at ha
          obtain ⟨g', v, hg, rfl, _⟩ := h7ra_finish_inv ha
          obtain ⟨kpkId, opkId, hsub⟩ := decPkOverDef_namedWrites_sub hg
          have hlen4 := h7ra_decPkOverDef_writes_len_le_4 hg
          refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
          rcases hsub q hq with h | h | h | h | h <;> rw [h]
          · exact h7ra_identityFile_len_le_64 st.party.other
          · exact h7ra_sessionFile_len_le_64 st.party.other
          · exact h7ra_oneTimeKyberPreKeyFile_len_le_64 kpkId
          · exact h7ra_baseKeysFile_len_le_64 kpkId
          · exact h7ra_oneTimePreKeyFile_len_le_64 opkId
      · rw [runAns_pqRecvBad (cliRunSemOverV4 X W) ⟨W.C, W.Q⟩ st (t :: rest) rc
          (fun h => ht2 (Option.some.inj h)) (fun h => ht3 (Option.some.inj h))] at ha
        cases ha

/-- Named-writes domain bound (`nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64`) for
`cliRunSemOverV4 X W` on `CliPqOrD3RecvInputs ⟨W.C, W.Q⟩`. -/
theorem h7ra_nwDom_pqD3Recv_overV4
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns (cliRunSemOverV4 X W) i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  rcases hi with hi_pq | ⟨st, ct, rc, _hwf, rfl⟩
  · rcases hi_pq with ⟨st, hwf, h1 | h2 | h3 | h4 | h5⟩
    · rcases h1 with ⟨hcap, b, t, rfl⟩
      have heq : runAns (cliRunSemOverV4 X W) (pqInitInputs ⟨W.C, W.Q⟩ st b t) =
          runAns (cliRunSemD2c_placed X W) (pqInitInputs ⟨W.C, W.Q⟩ st b t) := by
        rw [runAns_pqInit_eq, runAns_pqInit_eq]; rfl
      exact pqRunAns_namedWrites_bounds ⟨st, hwf, Or.inl ⟨hcap, b, t, rfl⟩⟩ (heq ▸ ha)
    · rcases h2 with ⟨m, r, hm, rfl⟩
      have heq : runAns (cliRunSemOverV4 X W) (pqSendInputs ⟨W.C, W.Q⟩ st m r) =
          runAns (cliRunSemD2c_placed X W) (pqSendInputs ⟨W.C, W.Q⟩ st m r) := by
        rw [runAns_pqSend_eq, runAns_pqSend_eq]; rfl
      exact pqRunAns_namedWrites_bounds ⟨st, hwf, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩ (heq ▸ ha)
    · rcases h3 with ⟨ct, rc, _, rfl⟩
      exact h7ra_pqRecvInputs_nwDom X W st (wireWhisper :: ct) rc nw out ha
    · rcases h4 with ⟨m, rc, _, rfl⟩
      exact h7ra_pqRecvInputs_nwDom X W st (wirePrekey :: m.bytes) rc nw out ha
    · rcases h5 with ⟨ct, rc, _, _, _, rfl⟩
      exact h7ra_pqRecvInputs_nwDom X W st ct rc nw out ha
  · exact h7ra_pqRecvInputs_nwDom X W st ct rc nw out ha

end NwDomOverV4

/-! ## 2. `Out1Dom`-Parametric `MainEntryBudgetFitsCapOf` & `MainOkOverD3F3` Assemblers -/

private theorem h7ra_mainArmEnvs_eq_runArmEnvs
    (ReadEnv : CryptoVerification.LibsignalPublicApi.StoreKit.FsFiles →
      List (BitVec 8) → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs)
    (PksmEnv : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost → List AllocEvent → Prop)
    (S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem) :
    LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge.cliMainArmEnvs
        (LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge.cliRunCalleesEnvs ReadEnv)
        sEnvs PksmEnv S =
      cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmEnv S := rfl

private theorem h7ra_pqD3ScopedRun_eq (WP : CryptoVerification.E2E.PEParams)
    (Run₀ : Inputs → CryptoVerification.SignalSession.Cli.RunAnswer → Prop) :
    pqD3ScopedRun WP Run₀ =
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget.pqD3ScopedRun
        WP Run₀ := rfl

private theorem h7ra_overV4_enc (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    (cliRunSemOverV4 X W).encrypt =
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef ⟨W.C, W.Q⟩
        CryptoVerification.SignalSession.Cli.Slots.scopeIn := rfl

private theorem h7ra_overV4_pksm (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    (cliRunSemOverV4 X W).pksmParse = pksmParse := rfl

private theorem h7ra_overV4_pksm_iff {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {rest : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : (cliRunSemOverV4 X W).pksmParse rest = some pm) :
    pksmParse rest = some pm :=
  Eq.mp (congrArg (· = some pm) (congrFun (h7ra_overV4_pksm X W) rest)) h

private theorem h7ra_encSlotSpecPlaced_d2c_eq_overV4 [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : LibsignalBinary.Heap.BudgetLimits)
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    encSlotSpecPlaced A lim EncEnv (cliRunSemD2c_placed X W) =
      encSlotSpecPlaced A lim EncEnv (cliRunSemOverV4 X W) := by
  funext stk
  unfold encSlotSpecPlaced
  rfl

private theorem h7ra_decSigSlotSpecFrozenPlaced_d2c_eq_overV4 [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : LibsignalBinary.Heap.BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD2c_placed X W) =
      decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemOverV4 X W) := by
  funext stk
  unfold decSigSlotSpecFrozenPlaced
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecPlacedOf
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecBasePlaced
  rfl

section IrreducibleWire

attribute [local irreducible] pksmParse MainEntryBudgetFitsCapOf RunEnv

/-- Discharges `MainEntryBudgetFitsCapOf` for `cliRunSemOverV4 X W` at `DecPkOverTwinEnv` from
`DecPkOverTwinEnv ⊆ W4TargetEnvOf Out1Dom` and `PhaseCreditSpec` / `PhaseGroupSpec` on `W4TargetEnvOf Out1Dom`. -/
theorem h7ra_fitsCap_overV4_of_out1Dom [LibsignalPlacement]
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    (Out1Dom : H7RAOut1DomPred)
    (DecPkOverTwinEnv : DecPkGhost → List AllocEvent → Prop)
    (W4TargetEnvOf : H7RAOut1DomPred → DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : ckx2_w1EncExact_phaseCredit_Stmt W)
    (hEncGrp : ckx2_w1EncExact_groupSpec_Stmt W)
    (hEnvSub : ∀ (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      let x := r3bDecPkGhost g meV peerV pm
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      H7RAPrev0DeserializeGuard x →
      ∀ evs, DecPkOverTwinEnv x evs → W4TargetEnvOf Out1Dom x evs)
    (hW4Credit : ∀ (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      let x := r3bDecPkGhost g meV peerV pm
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      H7RAPrev0DeserializeGuard x →
      PhaseCreditSpec fineCostModel (W4TargetEnvOf Out1Dom x) w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : ∀ (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      let x := r3bDecPkGhost g meV peerV pm
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      H7RAPrev0DeserializeGuard x →
      PhaseGroupSpec fineCostModel (W4TargetEnvOf Out1Dom x) w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (hmx_binaryKitRunSlotEnvsSlotOf
          (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
          (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
          A cliRunBudgets (realCliInitBinarySlotEnvFixed W) DecPkOverTwinEnv)
        PksmTryFromEnv (cliRunSemOverV4 X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) := by
  have h := mainEntryBudgetFitsCapOf_pqD3Recv_dom0
    (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    img (cliRunSemOverV4 X W) X W A cliRunBudgets DecPkOverTwinEnv
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    (h7ra_nwDom_pqD3Recv_overV4 X W)
    hEncCredit hEncGrp
    (ckx2_w2DecSigExact_phaseCredit W)
    (ckx2_w2DecSigExact_groupSpec W)
    (fun g meV peerV rest pm hi hp hin hc hst hpk => by
      have hpk' := h7ra_overV4_pksm_iff hpk
      have hct := h7ra_pksmParse_ct_le_msgCapBytes hin hc hst hpk'
      have hspqr := h7ra_peerSpqrStateTight640_r3b (meV := meV) (pm := pm) hi hp
      have hprev0 := h7ra_prev0Guard_r3b (meV := meV) (pm := pm) hi hp
      exact (hW4Credit g meV peerV rest pm hi hp hct hspqr hprev0).of_imp
        (hEnvSub g meV peerV rest pm hi hp hin hc hst hpk' hct hspqr hprev0))
    hW4Lp
    (fun g meV peerV rest pm hi hp hin hc hst hpk => by
      have hpk' := h7ra_overV4_pksm_iff hpk
      have hct := h7ra_pksmParse_ct_le_msgCapBytes hin hc hst hpk'
      have hspqr := h7ra_peerSpqrStateTight640_r3b (meV := meV) (pm := pm) hi hp
      have hprev0 := h7ra_prev0Guard_r3b (meV := meV) (pm := pm) hi hp
      exact (hW4Grp g meV peerV rest pm hi hp hct hspqr hprev0).of_imp
        (hEnvSub g meV peerV rest pm hi hp hin hc hst hpk' hct hspqr hprev0))
    hFits
    (h7ra_overV4_enc X W)
  let sEnvs : RunSlotEnvs :=
    hmx_binaryKitRunSlotEnvsSlotOf
      (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
      (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
      A cliRunBudgets (realCliInitBinarySlotEnvFixed W) DecPkOverTwinEnv
  have heq :=
    congrArg (fun aEnvs =>
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
        (RunEnv aEnvs)
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))
      (h7ra_mainArmEnvs_eq_runArmEnvs (ReadFileRuleEnvFixed cliIo.rd) sEnvs PksmTryFromEnv
        (cliRunSemOverV4 X W))
  exact Eq.mp heq h

/-- Proves `MainOkOverD3F3` by combining `h7ra_decPkValidOverTwin_slot520_ok` with the
`Out1Dom`-parametric envelope inclusion `hEnvSub` and `PhaseCreditSpec` / `PhaseGroupSpec` bounds. -/
theorem h7ra_overD3_wire_of_out1Dom
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) (img : Image)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (Out1Dom : H7RAOut1DomPred)
    (OverOfEnv' : @H7RADecPkOverEnvTwinFam (libsignalPlacementOf mpl hblk hext_nodup))
    (DecPkOverTwinEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (W4TargetEnvOf : H7RAOut1DomPred → UnreachedPqxdhPrimitives → CliHooks → GhostName →
      BitVec 64 → DecPkGhost → List AllocEvent → Prop)
    (RecvBytesEnv : CliHooks → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (SendSpqrEnv : CliHooks →
      CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop)
    (tdEnv : GhostName → BitVec 64 → CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (henc_addr : ∀ W γ tp g (peerV : AddrV) (peerG meG : AddrGhost) fsp,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      peerG.val = addrValOf peerV →
      ckx2_cliEncryptBinaryKitSlotEnvExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliRunBudgets (r2EncGhost g peerG meG fsp) =
        ckx2_cliEncryptBinaryKitSlotEnvExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliRunBudgets (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ W γ tp g fsp w (peerV : AddrV) (meG : AddrGhost) msgG m,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkOverTwinEnv X W γ tp x = DecPkOverTwinEnv X W γ tp y)
    (hW1 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliEncryptBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hW2 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hW3 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hReadFixed : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
            (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (lsρ lsReadFileSym)
          (readFileSpecPlaced cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hDeser : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 46)
          (sessDeserializeSpecPlaced scopeKit
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            SessDeserializeCancelEnv))
    (hRaw : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        EncodeRawPreallocPlacedOkX
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hGrow : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (lsProg_51 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 621)
          (withLsCl mpl
            (growOneVecU8BudgetSpec fineCostModel
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)))
    (hAesDec : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookOk (aesDecHookMallocng mmpl W.C.D)
          (aesDecBudgetSpec W.C.D fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits))
    (hSpqr : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        SpqrV1PlacedSeamsOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          mmpl ghFixed W (InitialStateEnv W.C.F)
          (fun st msg => RecvBytesEnv W st.bytes msg.bytes) (SendSpqrEnv W))
    (hRecv_ne : ∀ (W : CliHooks) stBs msgBs, ∃ evs, RecvBytesEnv W stBs msgBs evs)
    (htd : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv (RecvBytesEnv W) FormatInnerEnv a evs →
      tdEnv γ tp W a evs)
    (hPollTwin : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        H7RATightPollProducerAt
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          mmpl ghFixed W X OverOfEnv' (tdEnv γ tp) (DecPkOverTwinEnv X W γ tp))
    (hsEnv' : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) g evs,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      h7ra_decPkOverConcreteTwinOf OverOfEnv'
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp) g evs →
      DecPkOverTwinEnv X W γ tp g evs)
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        ckx2_w1EncExact_phaseCredit_Stmt W)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        ckx2_w1EncExact_groupSpec_Stmt W)
    (hEnvSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        pksmParse rest = some pm →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        ∀ evs, DecPkOverTwinEnv X W γ tp x evs → W4TargetEnvOf Out1Dom X W γ tp x evs)
    (hW4Credit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        PhaseCreditSpec fineCostModel (W4TargetEnvOf Out1Dom X W γ tp x)
          w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        PhaseGroupSpec fineCostModel (W4TargetEnvOf Out1Dom X W γ tp x) w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h7f_overD3_assembly_of_fitsCap
    hLs hblk hext_nodup ghFixed
    (fun _X W γ tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ckx2_cliEncryptBinaryKitSlotEnvExact W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
    (fun _X W γ tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
    (fun _X W _γ _tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      realCliInitBinarySlotEnvFixed W)
    DecPkOverTwinEnv PksmTryFromEnv
    hlibc hTr hG hioOf hstk hHooks
    (fun _X W _γ _tp gc d2 fsp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h7ra_initEnv_r1c_congr W gc d2 fsp)
    (fun _X W γ tp gc peerV peerG meG fsp hp => henc_addr W γ tp gc peerV peerG meG fsp hp)
    (fun _X W γ tp gc fsp w peerV meG msgG m => hdec_ghost W γ tp gc fsp w peerV meG msgG m)
    h7f_pksmTryFromEnv_congr
    hdp_ghost
    (fun _h547 W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h7f_pksmSlotOk_pksmTryFromEnv mmpl ghFixed W (hG γ tp))
    (fun h547 X W γ tp => by
      letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
      change (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliEncryptBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemOverV4 X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464)
      rw [← h7ra_encSlotSpecPlaced_d2c_eq_overV4]
      exact hW1 h547 X W γ tp)
    (fun h547 X W γ tp => by
      letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
      change (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemOverV4 X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463)
      rw [← h7ra_decSigSlotSpecFrozenPlaced_d2c_eq_overV4]
      exact hW2 h547 X W γ tp)
    (fun h547 X W γ tp => hW3 h547 X W γ tp)
    (fun h547 X W γ tp => by
      letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
      exact h7ra_decPkValidOverTwin_slot520_ok
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits mmpl ghFixed W X
        OverOfEnv'
        (h7ra_honestOverD3FineSlotEnvs hblk hext_nodup mmpl brkStart DecPkOverTwinEnv X W γ tp)
        h547 (hG γ tp) (hHooks W γ tp).runHooks
        (hReadFixed h547 W γ tp) (hDeser h547 W γ tp)
        (hRaw h547 W γ tp) (hGrow h547 W γ tp) (hAesDec h547 W γ tp)
        (hSpqr h547 W γ tp) (hRecv_ne W) (htd W γ tp)
        (hPollTwin h547 X W γ tp) (hsEnv' X W γ tp))
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have hfit := h7ra_fitsCap_overV4_of_out1Dom img X W
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        Out1Dom (DecPkOverTwinEnv X W γ tp)
        (fun D => W4TargetEnvOf D X W γ tp)
        w4Cum w4Live w4Peak w4MaxReq w4GrpS
        (hEncCredit h547 W) (hEncGrp h547 W)
        (hEnvSub h547 X W γ tp) (hW4Credit h547 X W γ tp) hW4Lp (hW4Grp h547 X W γ tp) hFits
      have hsEq :
          hmx_binaryKitRunSlotEnvsSlotOf
            (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
            (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (DecPkOverTwinEnv X W γ tp) =
          { encrypt := ckx2_cliEncryptBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
            decryptSignal := ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
            initiate := realCliInitBinarySlotEnvFixed W
            decryptPrekey := DecPkOverTwinEnv X W γ tp } := rfl
      have heq2 :=
        congr
          (congrArg
            (fun (sEnvs : RunSlotEnvs) RunS =>
              MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
                (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
                (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
                  sEnvs PksmTryFromEnv (cliRunSemOverV4 X W)))
                RunS)
            hsEq)
          (h7ra_pqD3ScopedRun_eq ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
      exact Eq.mp heq2 hfit)

/-- Value-projected Slot-520 `OverD3` envelope wrapper around `h7ra_decPkOverConcreteTwinOf`,
existentially projecting over value components of `DecPkGhost` so pointer-ghost irrelevance holds. -/
def H7RADecPkOverValProjectedEnv [LibsignalPlacement]
    (OverOfEnv' : H7RADecPkOverEnvTwinFam)
    (A : CryptoVerification.RustHeap.RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ x' : DecPkGhost,
    x'.peer.val = x.peer.val ∧ x'.me.val = x.me.val ∧
    x'.stores = x.stores ∧ x'.coinsP = x.coinsP ∧
    x'.F = x.F ∧ x'.coins = x.coins ∧ x'.msg = x.msg ∧
    h7ra_decPkOverConcreteTwinOf OverOfEnv' A W X tdEnv x' evs

theorem h7ra_decPkOverValProjectedEnv_congr [LibsignalPlacement]
    (OverOfEnv' : H7RADecPkOverEnvTwinFam)
    (A : CryptoVerification.RustHeap.RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hst : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hF : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    H7RADecPkOverValProjectedEnv OverOfEnv' A W X tdEnv x =
      H7RADecPkOverValProjectedEnv OverOfEnv' A W X tdEnv y := by
  funext evs
  unfold H7RADecPkOverValProjectedEnv
  rw [hp, hm, hst, hcp, hF, hc, hmsg]

/-- Instantiates `h7ra_overD3_wire_of_out1Dom` at `H7RADecPkOverValProjectedEnv`, discharging
pointer-ghost irrelevance internally. -/
theorem h7ra_overD3_wire_projected_of_out1Dom
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) (img : Image)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (Out1Dom : H7RAOut1DomPred)
    (OverOfEnv' : @H7RADecPkOverEnvTwinFam (libsignalPlacementOf mpl hblk hext_nodup))
    (W4TargetEnvOf : H7RAOut1DomPred → UnreachedPqxdhPrimitives → CliHooks → GhostName →
      BitVec 64 → DecPkGhost → List AllocEvent → Prop)
    (RecvBytesEnv : CliHooks → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (SendSpqrEnv : CliHooks →
      CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop)
    (tdEnv : GhostName → BitVec 64 → CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (henc_addr : ∀ W γ tp g (peerV : AddrV) (peerG meG : AddrGhost) fsp,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      peerG.val = addrValOf peerV →
      ckx2_cliEncryptBinaryKitSlotEnvExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliRunBudgets (r2EncGhost g peerG meG fsp) =
        ckx2_cliEncryptBinaryKitSlotEnvExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliRunBudgets (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ W γ tp g fsp w (peerV : AddrV) (meG : AddrGhost) msgG m,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (r3aDecSigGhost0 g peerV meG m))
    (hW1 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliEncryptBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hW2 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hW3 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hReadFixed : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
            (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (lsρ lsReadFileSym)
          (readFileSpecPlaced cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hDeser : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 46)
          (sessDeserializeSpecPlaced scopeKit
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            SessDeserializeCancelEnv))
    (hRaw : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        EncodeRawPreallocPlacedOkX
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hGrow : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (lsProg_51 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 621)
          (withLsCl mpl
            (growOneVecU8BudgetSpec fineCostModel
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)))
    (hAesDec : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookOk (aesDecHookMallocng mmpl W.C.D)
          (aesDecBudgetSpec W.C.D fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits))
    (hSpqr : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        SpqrV1PlacedSeamsOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          mmpl ghFixed W (InitialStateEnv W.C.F)
          (fun st msg => RecvBytesEnv W st.bytes msg.bytes) (SendSpqrEnv W))
    (hRecv_ne : ∀ (W : CliHooks) stBs msgBs, ∃ evs, RecvBytesEnv W stBs msgBs evs)
    (htd : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv (RecvBytesEnv W) FormatInnerEnv a evs →
      tdEnv γ tp W a evs)
    (hPollTwin : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        H7RATightPollProducerAt
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          mmpl ghFixed W X OverOfEnv' (tdEnv γ tp)
          (@H7RADecPkOverValProjectedEnv (libsignalPlacementOf mpl hblk hext_nodup) OverOfEnv'
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp)))
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        ckx2_w1EncExact_phaseCredit_Stmt W)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        ckx2_w1EncExact_groupSpec_Stmt W)
    (hEnvSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
        (x' : DecPkGhost),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        pksmParse rest = some pm →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        x'.F = x.F →
        x'.peer.val = x.peer.val →
        x'.msg = x.msg →
        ∀ evs,
          h7ra_decPkOverConcreteTwinOf OverOfEnv'
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp) x' evs →
          W4TargetEnvOf Out1Dom X W γ tp x evs)
    (hW4Credit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        PhaseCreditSpec fineCostModel (W4TargetEnvOf Out1Dom X W γ tp x)
          w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        PhaseGroupSpec fineCostModel (W4TargetEnvOf Out1Dom X W γ tp x) w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h7ra_overD3_wire_of_out1Dom
    hLs hblk hext_nodup ghFixed img Out1Dom OverOfEnv'
    (fun X W γ tp =>
      @H7RADecPkOverValProjectedEnv (libsignalPlacementOf mpl hblk hext_nodup) OverOfEnv'
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp))
    W4TargetEnvOf RecvBytesEnv SendSpqrEnv tdEnv
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    hlibc hTr hG hioOf hstk hHooks henc_addr hdec_ghost
    (fun X W γ tp x y hp hm hst hcp hF hc hmsg =>
      @h7ra_decPkOverValProjectedEnv_congr (libsignalPlacementOf mpl hblk hext_nodup) OverOfEnv'
        (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp)
        x y hp hm hst hcp hF hc hmsg)
    hW1 hW2 hW3 hReadFixed hDeser hRaw hGrow hAesDec hSpqr hRecv_ne htd hPollTwin
    (fun _X _W _γ _tp g _evs h => ⟨g, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩)
    hEncCredit hEncGrp
    (fun h547 X W γ tp g meV peerV rest pm hi hp hin hc hst hpk hct hspqr hprev0 evs => by
      rintro ⟨x', hxp, _hxm, _hxst, _hxcp, hxF, _hxc, hxmsg, hx'⟩
      exact hEnvSub h547 X W γ tp g meV peerV rest pm x'
        hi hp hin hc hst hpk hct hspqr hprev0 hxF hxp hxmsg evs hx')
    hW4Credit hW4Lp hW4Grp hFits

/-- Closed `Out1Dom`-parametric `MainOkOverD3F3` assembly discharging `hPollTwin` via
`DecPkD3ValidOverTightConcreteEnv'`. -/
theorem h7ra_overD3_wire_tightRaw_of_out1Dom
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) (img : Image)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (Out1Dom : H7RAOut1DomPred)
    (W4TargetEnvOf : H7RAOut1DomPred → UnreachedPqxdhPrimitives → CliHooks → GhostName →
      BitVec 64 → DecPkGhost → List AllocEvent → Prop)
    (RecvBytesEnv : CliHooks → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (SendSpqrEnv : CliHooks →
      CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop)
    (tdEnv : GhostName → BitVec 64 → CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (henc_addr : ∀ W γ tp g (peerV : AddrV) (peerG meG : AddrGhost) fsp,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      peerG.val = addrValOf peerV →
      ckx2_cliEncryptBinaryKitSlotEnvExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliRunBudgets (r2EncGhost g peerG meG fsp) =
        ckx2_cliEncryptBinaryKitSlotEnvExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliRunBudgets (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ W γ tp g fsp w (peerV : AddrV) (meG : AddrGhost) msgG m,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
          (r3aDecSigGhost0 g peerV meG m))
    (hW1 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliEncryptBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hW2 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hW3 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hReadFixed : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
            (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (lsρ lsReadFileSym)
          (readFileSpecPlaced cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hDeser : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 46)
          (sessDeserializeSpecPlaced scopeKit
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            SessDeserializeCancelEnv))
    (hRaw : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        EncodeRawPreallocPlacedOkX
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hGrow : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (lsProg_51 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 621)
          (withLsCl mpl
            (growOneVecU8BudgetSpec fineCostModel
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)))
    (hAesDec : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookOk (aesDecHookMallocng mmpl W.C.D)
          (aesDecBudgetSpec W.C.D fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits))
    (hSpqr : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        SpqrV1PlacedSeamsOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          mmpl ghFixed W (InitialStateEnv W.C.F)
          (fun st msg => RecvBytesEnv W st.bytes msg.bytes) (SendSpqrEnv W))
    (hRecv_ne : ∀ (W : CliHooks) stBs msgBs, ∃ evs, RecvBytesEnv W stBs msgBs evs)
    (htd : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv (RecvBytesEnv W) FormatInnerEnv a evs →
      tdEnv γ tp W a evs)
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        ckx2_w1EncExact_phaseCredit_Stmt W)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        ckx2_w1EncExact_groupSpec_Stmt W)
    (hEnvSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
        (x' : DecPkGhost),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        pksmParse rest = some pm →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        x'.F = x.F →
        x'.peer.val = x.peer.val →
        x'.msg = x.msg →
        ∀ evs,
          DecPkD3ValidOverTightConcreteEnv'
            (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp) x' evs →
          W4TargetEnvOf Out1Dom X W γ tp x evs)
    (hW4Credit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        PhaseCreditSpec fineCostModel (W4TargetEnvOf Out1Dom X W γ tp x)
          w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (_rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        let x := r3bDecPkGhost g meV peerV pm
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        pm.message.ciphertext.length ≤ msgCapBytes →
        PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
        H7RAPrev0DeserializeGuard x →
        PhaseGroupSpec fineCostModel (W4TargetEnvOf Out1Dom X W γ tp x) w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h7ra_overD3_wire_projected_of_out1Dom
    hLs hblk hext_nodup ghFixed img Out1Dom
    (@DecPkD3ValidOverOfEnv' (libsignalPlacementOf mpl hblk hext_nodup))
    W4TargetEnvOf RecvBytesEnv SendSpqrEnv tdEnv
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    hlibc hTr hG hioOf hstk hHooks henc_addr hdec_ghost
    hW1 hW2 hW3 hReadFixed hDeser hRaw hGrow hAesDec hSpqr hRecv_ne htd
    (fun h547 X W γ tp => by
      letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
      exact h7ra_tightPollProducerAt_decPkD3ValidOver
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        mmpl ghFixed W X (tdEnv γ tp)
        (@H7RADecPkOverValProjectedEnv (libsignalPlacementOf mpl hblk hext_nodup)
          (@DecPkD3ValidOverOfEnv' (libsignalPlacementOf mpl hblk hext_nodup))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X (tdEnv γ tp))
        h547)
    hEncCredit hEncGrp hEnvSub hW4Credit hW4Lp hW4Grp hFits

end IrreducibleWire

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
