/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Pksm
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Budget-Threaded `validMatch` Slot, `mainSpecTightPlacedAt` Lift, and `W4RecvPrekeyRealEnv` Inclusion

Proves the top-level block-`520` `decrypt_prekey` slot contracts, block-`579` `run` lifts,
block-`617` `mainSpecTightPlacedAt` corollaries, `SingleSlotFineSpec`, and `W4RecvPrekeyRealEnv`
inclusion for non-canonical `validMatch` `PreKeySignalMessage`s.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

open CryptoVerification (lsρ)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (cliIo_rd_ok_length_le_sessionCapBytes mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive d3RecvW4ExtMaxReq d3RecvW4ExtPeak mainSt0Dom mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_mem_w4 mkD3RecvCalleeEnvs realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_mem_w4)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (W4RecvPrekeyRealEnv W4RecvPrekeyRealParams mkW4RecvPrekeySlotParams w4RecvPrekeyRealEnv_nonvacuous_alloc w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB (W4ArchivedTrialDomOf W4FailedTdDomOf W4RecvPrekeyRealDomOf W4TryDecryptCallDomOf W4TryDecryptPathACDomOf w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak w4RecvPrekeyReal1MiB_i_eq w4RecvPrekeyReal1MiB_i_singleSlotFineSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget (StageP2PathAQpanCliD3PlacedBudgetStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAContPlacedBudget (StageP2PathAQpanCliD3AtPlacedBudgetStmt stageP2PathAQpanCliD3At_of_stmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget (DecPkD3ValidMatchCliEnv DecPkD3ValidMatchEnv cliDecryptPrekey_slot_d3_match_placedBudget_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3 (encodeInjOn_scopeIn ratchetScopeCoversPq_scopeIn)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (GhostState PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage Session SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalPlacement blkPl_111 lsmpl lsρ)
open CryptoVerification.E2E (PEParams PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.E2E.Pqxdh.ResponderWire (PreKeyTryFromArgs)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks Inputs PqParty PqSessionMatches PqxdhPartyInSpecDomain cliExternsPlaced lsReadFileSym observe pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome)
open CryptoVerification.SignalSession.Cli (CliInputsOk CommitOk MainResult RunAnswer StoresGhost cliInputs cliStaticsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunNeeds cliWrOk domainArgv_pqRecv mProgPlaced parseArgs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunHsOk RunNeeds RunSem addrValOf dpPollNeed mkSlot runAns runFiles runProgPlaced runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed commitOk_pqRecvPrekey_decPkDef decPkDef pkToE? pksmParseAgrees_S0 pksmTyped_S0 pmOfE pqDecryptPrekeyAgrees_decPkDef)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (tryFrom_serialized)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (decodeProto kyberOk pksmParse pksmParse_bytes)
open CryptoVerification.SignalSession.Cli.RunRefine (runAns_pqRecvPrekey_eq runBounds_pqRecv)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ runEncOk_pqRecv scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (TryDecryptCliEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (phaseGroupSpec_exists_guarded)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf (peerSpqrStateTight640_of_pqRecv_wf)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (DecPkOkD3 decPkDef_eq_pmOfE_of_pkToE?_some decPkOkD3_pqRecv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PlacedBudget (StageP2PathAQpanCliD3PlacedBudgetStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAPlacedBudget (StageP2PathAQpanCliD3AtPlacedBudgetStmt stageP2PathAQpanCliD3At_of_stmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (cliRunSemF3 encodeInjOn_scopeIn ratchetScopeCoversPq_scopeIn runFilesOk_pqRecv_cli_f3 runHsOk_pqRecvPrekey_body_f3)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunArmEnvs RunArmsPlaced RunEnv run_ok_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (StageP3GenStepsVRegsPlacedStmt StageP3PrevEmptyVRegsPlacedStmt pollTryDecryptPlacedSpecTPTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (decPkSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv mainSpecTightPlacedAt readFileSpecPlaced runSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget (DecPkD3ValidMatchPollEnv DecPkD3ValidMatchEnv DecPkD3ValidMatchCliEnv decPk_d3_validMatch_poll_placedBudget cliDecryptPrekey_slot_d3_match_placedBudget_at_block)

private theorem tryFrom_inner_of_pksmParse_pkToE_local {body : List (BitVec 8)}
    {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m) :
    SignalMessage.tryFrom protoSignalCodec m.inner = .ok pm.message := by
  have hm_inner : m.inner = pm.message.serialized := by
    unfold pkToE? at hpk
    split at hpk
    · cases hpk
    · split at hpk
      · cases hpk
      · split at hpk
        · cases hpk
        · injection hpk with hm
          exact (congrArg PreKeyMessageFields.inner hm).symm
  cases body with
  | nil => cases hparse
  | cons vb rest =>
    unfold pksmParse at hparse
    dsimp only at hparse
    split at hparse
    · cases hparse
    · rcases hdec : decodeProto rest with _ | mp
      · simp [hdec] at hparse
      rw [hdec] at hparse
      rcases hbk : mp.baseKey with _ | bk
      · simp [hbk] at hparse
      rcases hik : mp.identityKey with _ | ik
      · simp [hbk, hik] at hparse
      rcases hmsg : mp.message with _ | rawMsg
      · simp [hbk, hik, hmsg] at hparse
      rcases hsid : mp.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at hparse
      simp only [hbk, hik, hmsg, hsid] at hparse
      cases hkyb : kyberOk (vb >>> 4) mp
      · simp [hkyb] at hparse
      simp only [hkyb, ↓reduceIte] at hparse
      rcases h1 : PublicKey.deserialize bk with _ | baseKey
      · simp [h1] at hparse
      rcases h2 : PublicKey.deserialize ik with _ | idKey
      · simp [h1, h2] at hparse
      rcases h3 : SignalMessage.tryFrom protoSignalCodec rawMsg with _ | inner
      · simp [h1, h2, h3] at hparse
      simp only [h1, h2, h3, Option.some.injEq] at hparse
      subst hparse
      have hser : inner.serialized = rawMsg := tryFrom_serialized h3
      dsimp only at hm_inner ⊢
      rw [hm_inner, hser]
      exact h3

private theorem pksmParse_bytes_of_parse_pkToE_local {body : List (BitVec 8)}
    {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    pksmParse m.bytes = some (pmOfE m pm.message) := by
  have hi := tryFrom_inner_of_pksmParse_pkToE_local hparse hpk
  let x : PreKeyTryFromArgs :=
    { ptr := 0, sret := 0, regId := m.regId, opkId := m.opkId, spkId := m.spkId,
      kpkId := m.kpkId, kyberCt := m.kyberCt, baseKey := m.baseKey, idPub := m.idPub,
      inner := m.inner }
  have h := pksmParse_bytes x hm
  change pksmParse m.bytes =
    (match SignalMessage.tryFrom protoSignalCodec m.inner with
     | .ok i => some (pmOfE m i)
     | .error _ => none) at h
  rw [h, hi]

private theorem runAns_pqRecvPrekey_eq_canonical_local (S : RunSem) (X : UnreachedPqxdhPrimitives)
    (WP : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS_pksm : S.pksmParse = pksmParse) (hS_decPk : S.decryptPrekey = decPkDef X WP Scope)
    (st : PqParty) (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256) (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    runAns S (pqRecvInputs WP st (wirePrekey :: body) rc) =
      runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) := by
  have hcanon := pksmParse_bytes_of_parse_pkToE_local hparse hpk hm
  have hfiles_eq :
      (initFsState (cliInputs (pqRecvInputs WP st (wirePrekey :: body) rc))).files =
      (initFsState (cliInputs (pqRecvInputs WP st (wirePrekey :: m.bytes) rc))).files := rfl
  rw [runAns_pqRecvPrekey_eq, runAns_pqRecvPrekey_eq, hS_pksm, hparse, hcanon, hS_decPk]
  dsimp only [runFiles]
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk, hfiles_eq]

noncomputable def cliRunSemD3ValidMatch (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSemF3 X W (decPkDef X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn) pksmParse

def pqD3ScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop)
    (i : Inputs) (a : RunAnswer) : Prop :=
  CliPqOrD3RecvDom WP i ∧ Run₀ i a

theorem runRel_pqRecv_validMatch (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (st : PqParty) (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hbody : body.length < 2 ^ 32)
    (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    let a := runAns (cliRunSemD3ValidMatch X W) inp
    pqD3ScopedRun WP (runRel (cliRunSemD3ValidMatch X W)) inp a ∧
      observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
      CommitOk inp (CryptoVerification.SignalSession.Cli.MainResult.ofAnswer a) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let S : RunSem := cliRunSemD3ValidMatch X W
  have hlen : (wirePrekey :: body).length ≤ 2 ^ 32 := Nat.succ_le_of_lt hbody
  have hhs : RunHsOk S (pqRecvInputs WP st (wirePrekey :: body) rc) :=
    runHsOk_pqRecvPrekey_body_f3 (S := S) WP st body rc fun pm' hpm' => by
      change pksmParse body = some pm' at hpm'
      cases Option.some.inj (hpm'.symm.trans hparse)
      exact decPkOkD3_pqRecv WP scopeIn encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn WP)
        st body pm m rc hwf hparse hpk hm hmatch
  have hcanon_ans :
      runAns S (pqRecvInputs WP st (wirePrekey :: body) rc) =
        runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
    runAns_pqRecvPrekey_eq_canonical_local S X WP scopeIn rfl rfl
      st body pm m rc hparse hpk hm
  have href :=
    CryptoVerification.SignalSession.Cli.RunRefine.runAns_pqRecvPrekey S X WP
      (pksmParseAgrees_S0 (S := S) rfl)
      (pqDecryptPrekeyAgrees_decPkDef S X WP scopeIn rfl
        (pksmTyped_S0 (S := S) rfl) encodeInjOn_scopeIn
        (ratchetScopeCoversPq_scopeIn WP))
      st m rc hwf hm hmatch
  have hobs :
      observe (pqRecvInputs WP st (wirePrekey :: body) rc).files
        (runAns S (pqRecvInputs WP st (wirePrekey :: body) rc)) =
      pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: body) rc)
        (pqRecvPrekeyModel X WP st m rc) := by
    rw [hcanon_ans]
    exact href
  exact ⟨⟨Or.inr ⟨st, wirePrekey :: body, rc, hwf, rfl⟩,
      domainArgv_pqRecv WP st (wirePrekey :: body) rc,
      runBounds_pqRecv WP st (wirePrekey :: body) rc hlen,
      runFilesOk_pqRecv_cli_f3 (S := S) rfl WP st (wirePrekey :: body) rc hwf,
      runEncOk_pqRecv S WP st (wirePrekey :: body) rc,
      hhs, rfl⟩,
    hobs,
    commitOk_pqRecvPrekey_decPkDef (S := S) (X := X) (W := WP) (Scope := scopeIn)
      rfl st body rc⟩

theorem cliDecryptPrekey_slotOk_d3_match_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3AtPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hP3A : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3GenStepsVRegsPlacedStmt)
    (hP3B : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_d3_match_placedBudget_at_block A lim B mmpl gh W hi X S Scope
      hDropNz hh hRead hDeser hP2A hP3A hP3B hTryDec hinjK hsub hS hok hevs_sub
      stk (hneed ▸ h1) h2

theorem decPkValidMatchSlotOk_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop} (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3AtPlacedBudgetStmt A lim ReadEnv DeserEnv X mmpl gh W cliRunBudgets
      P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt) (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_d3_match_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim cliRunBudgets mmpl gh W (by decide) X S scopeIn needs
    h547 hh hRead hDeser hP2A hP3A hP3B hTryDec
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv hneed

theorem cliDecryptPrekey_d3_match_slotOk_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hP2A : StageP2PathAQpanCliD3PlacedBudgetStmt A lim P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt) (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchCliEnv A.repAlloc W X cliRunBudgets P2PathAErrEnv P2PathAOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkValidMatchSlotOk_placedBudget mmpl gh W X h547 hh hRead hDeser
    (stageP2PathAQpanCliD3At_of_stmt hP2A X mmpl gh W cliRunBudgets)
    hP3A hP3B hTryDec S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

abbrev decPkValidMatchSlotOk_cli_placedBudget := @cliDecryptPrekey_d3_match_slotOk_placedBudget

theorem subroutine_ok_runSpecTightPlaced_mono_run [LibsignalPlacement]
    {P : Program} {e : BitVec 64} {M : AllocCostModel} {CodeOk : Memory → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run₁ Run₂ : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (himp : ∀ i a, Run₁ i a → Run₂ i a)
    (h : subroutine_ok P e
      (runSpecTightPlaced CodeOk A lim Env uuidParse Run₂ wrOk resStack)) :
    subroutine_ok P e
      (runSpecTightPlaced CodeOk A lim Env uuidParse Run₁ wrOk resStack) := by
  refine subroutine_ok_mono h
    (fun ⟨g, st⟩ R s0 hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => he)
    (fun _ _ _ _ ho => ho)
  simp only [runSpecTightPlaced, runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, himp g.i g.a hp.1.2.1, hp.1.2.2⟩, hp.2⟩

theorem hrun_cli_validMatch_tight_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hP2A : StageP2PathAQpanCliD3PlacedBudgetStmt A lim P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt) (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))))
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchCliEnv A.repAlloc W X cliRunBudgets P2PathAErrEnv P2PathAOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemD3ValidMatch X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfPlaced A lim sEnvs (cliRunSemD3ValidMatch X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfPlaced A lim sEnvs (cliRunSemD3ValidMatch X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemD3ValidMatch X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs) uuidTryParse
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W))) cliWrOk cliResStack) := by
  have hslot := cliDecryptPrekey_d3_match_slotOk_placedBudget mmpl gh W X h547 hh hRead hDeser
    hP2A hP3A hP3B hTryDec (cliRunSemD3ValidMatch X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl
  have hrun := run_ok_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    harms hh (hcFromSlot hslot) hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs (by decide)) (by decide) (by decide)
  exact subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun

theorem d3_valid_match_main_ok_cli_tight_placed_at [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds} (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hP2A : StageP2PathAQpanCliD3PlacedBudgetStmt A lim P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt) (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))))
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchCliEnv A.repAlloc W X cliRunBudgets P2PathAErrEnv P2PathAOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hMainLift :
      (slotsOfPlaced A lim sEnvs (cliRunSemD3ValidMatch X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W))))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W)))) :=
  hMainLift
    (cliDecryptPrekey_d3_match_slotOk_placedBudget mmpl gh W X h547 hh hRead hDeser
      hP2A hP3A hP3B hTryDec (cliRunSemD3ValidMatch X W) sEnvs needs
      hsEnv rfl rfl (fun _ _ _ _ h => h) hneed)

abbrev main_ok_cli_validMatch_tight_placed_at := @d3_valid_match_main_ok_cli_tight_placed_at

theorem phaseCredit_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

def ValidMatchRealSlotEnv (evs : List AllocEvent) : Prop :=
  ∃ w4R : W4RecvPrekeyRealParams,
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs

def decPkD3ValidMatchCum : Nat := w4RecvPrekeyReal1MiB_i_Cum

def decPkD3ValidMatchLive : Nat := w4RecvPrekeyReal1MiB_i_Live

def decPkD3ValidMatchPeak : Nat := w4RecvPrekeyReal1MiB_i_Peak

def decPkD3ValidMatchMaxReq : Nat := w4RecvPrekeyReal1MiB_i_MaxReq

def decPkD3ValidMatchGrpS : Nat := w4RecvPrekeyRealGrpS

def decPkD3ValidMatchReal_singleSlotFineSpec :
    SingleSlotFineSpec ValidMatchRealSlotEnv where
  cum := decPkD3ValidMatchCum
  live := decPkD3ValidMatchLive
  peak := decPkD3ValidMatchPeak
  maxReq := decPkD3ValidMatchMaxReq
  grpS := decPkD3ValidMatchGrpS
  credit := phaseCredit_exists_guarded_u fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).credit
  live_le_peak := w4RecvPrekeyReal1MiB_i_eq.2.2.2.2
  groups := phaseGroupSpec_exists_guarded fineCostModel fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).groups

theorem decPkD3ValidMatch_caps_le :
    decPkD3ValidMatchLive ≤ decPkD3ValidMatchPeak ∧
    decPkD3ValidMatchCum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
    decPkD3ValidMatchLive ≤ w4RecvPrekeyReal1MiB_i_Live ∧
    decPkD3ValidMatchPeak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
    decPkD3ValidMatchMaxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
    decPkD3ValidMatchGrpS ≤ w4RecvPrekeyRealGrpS :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem decPkD3ValidMatch_ext_caps_le :
    decPkD3ValidMatchCum ≤ d3RecvW4ExtCum ∧
    decPkD3ValidMatchLive ≤ d3RecvW4ExtLive ∧
    decPkD3ValidMatchPeak ≤ d3RecvW4ExtPeak ∧
    decPkD3ValidMatchMaxReq ≤ d3RecvW4ExtMaxReq ∧
    decPkD3ValidMatchGrpS ≤ d3RecvW4ExtGrpS :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
   Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem peerSpqrStateTight640_of_cliPqOrD3Recv {P : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvDom P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 P.C.F P.Q.K (runFiles i) (addrValOf peer) := by
  rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
  · exact peerSpqrStateTight640_of_cliPqInputs_recv hPq hparse
  · exact peerSpqrStateTight640_of_pqRecv_wf hwf hparse

theorem w4RecvPrekeyRealDomOf_validMatch {i : Inputs} {peerAddr : AddrV}
    (R : W4RecvPrekeyRealParams)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hrd : R.rd = cliIo.rd) (hfiles : R.files = runFiles i)
    (hkpk : R.kpkDir = CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber.lastResort)
    (hpeer : R.peer.val = addrValOf peerAddr) (hownKey : R.ownKeyName.length ≤ 64)
    (hownReg : R.ownRegName.length ≤ 64) (hkpkMark : R.kpkMarkName.length ≤ 64)
    (hresOld : R.x_res.cap.toNat ≤ 4096)
    (hresNew : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096)
    (hspqrKey : R.x_spqr.p.authKey.length ≤ 32)
    (hcurDom : R.hasCurSession = true →
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
          SessionCloneDom 286196 ses_cur)
    (hcurFail : R.hasCurSession = true → W4FailedTdDomOf R.F R.K msgCapBytes R.fc_cur)
    (htrialsLen : R.archivedTrials.length ≤ 4)
    (htrialsDom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K msgCapBytes x)
    (harchValid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (harchEnc : (encodeRecord R.r_arch).length ≤ 2097152)
    (hout0Valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hout0Enc : (encodeRecord R.r_out0).length ≤ 2097152)
    (hout1 : FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1)
    (htdB : R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B)
    (htdAC : R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K msgCapBytes R.td_AC) :
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R where
  kpk_dir := hkpk
  outer_dom :=
    { peer_len := by
        have hp40 : peerAddr.name.length ≤ 40 := parseArgs_peer_name_length_le hparse
        change (mkW4RecvPrekeySlotParams R).peer.val.name.length ≤ 40
        simp only [mkW4RecvPrekeySlotParams, hpeer]
        exact hp40
      ownKey_len := hownKey
      ownReg_len := hownReg
      kpkMark_len := hkpkMark
      res_old := hresOld
      res_new := hresNew
      ikm_small := by decide
      spqr_key := hspqrKey
      sess_cap := fun bs hbs => by
        rw [mkW4RecvPrekeySlotParams, hrd, hfiles] at hbs
        exact cliIo_rd_ok_length_le_sessionCapBytes (runFiles i) _ bs hbs
      small_cap := fun d _ n bs hbs => by
        rw [mkW4RecvPrekeySlotParams, hrd, hfiles] at hbs
        exact cliIo_rd_ok_length_le_sessionCapBytes (runFiles i) _ bs hbs
      cur_dom := by
        cases hcs : R.hasCurSession with
        | false =>
          exact Or.inl (fun evs hevs => by
            change (if R.hasCurSession then _ else fun _ => False) evs at hevs
            rw [hcs] at hevs
            exact hevs)
        | true =>
          exact Or.inr (hcurDom hcs)
      arch_valid := harchValid
      arch_enc := harchEnc
      out0_valid := hout0Valid
      out0_enc := hout0Enc
      out1_freshBob := hout1
      trials_len4 := htrialsLen }
  cur_fail_dom := hcurFail
  trials_dom := htrialsDom
  tdB_dom := htdB
  tdAC_dom := htdAC

theorem validMatchRealSlotEnv_nonvacuous_alloc
    {R : W4RecvPrekeyRealParams} (hDom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ ValidMatchRealSlotEnv evs := by
  obtain ⟨evs, hne, hevs⟩ := w4RecvPrekeyRealEnv_nonvacuous_alloc R
  exact ⟨evs, hne, R, hDom, hevs⟩

def ValidMatchStageP3WitnessFacts (i : Inputs) (peerAddr : AddrV)
    (R : W4RecvPrekeyRealParams) (evs : List AllocEvent) : Prop :=
  R.rd = cliIo.rd ∧
  R.files = runFiles i ∧
  (R.kpkDir = CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber.oneTime ∨
    R.kpkDir = CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber.lastResort) ∧
  R.peer.val = addrValOf peerAddr ∧
  R.ownKeyName.length ≤ 64 ∧
  R.ownRegName.length ≤ 64 ∧
  R.kpkMarkName.length ≤ 64 ∧
  R.x_res.cap.toNat ≤ 4096 ∧
  reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096 ∧
  R.x_spqr.p.authKey.length ≤ 32 ∧
  (R.hasCurSession = true →
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
        SessionCloneDom 286196 ses_cur) ∧
  (R.hasCurSession = true → W4FailedTdDomOf R.F R.K msgCapBytes R.fc_cur) ∧
  R.archivedTrials.length ≤ 4 ∧
  (∀ x ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K msgCapBytes x) ∧
  (∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
  (encodeRecord R.r_arch).length ≤ 2097152 ∧
  (∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
  (encodeRecord R.r_out0).length ≤ 2097152 ∧
  FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1 ∧
  (R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B) ∧
  (R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K msgCapBytes R.td_AC) ∧
  W4RecvPrekeyRealEnv R evs

theorem decPkD3ValidMatchEnv_mem_validMatchRealSlotEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost} (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (_hfiles : x.F = runFiles g.i) (_hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3ValidMatchCliEnv A W X B P2PathAErrEnv P2PathAOkEnv x evs →
        ∃ R : W4RecvPrekeyRealParams, ValidMatchStageP3WitnessFacts g.i peerAddr R evs) :
    ∀ evs, DecPkD3ValidMatchCliEnv A W X B P2PathAErrEnv P2PathAOkEnv x evs →
      ValidMatchRealSlotEnv evs := by
  intro evs hevs
  have hTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) :=
    peerSpqrStateTight640_of_cliPqOrD3Recv hi hparse
  obtain ⟨R, hrd, hRfiles, hkpk, hRpeer, hownK, hownR, hkpkM, hresO, hresN, hspqrK,
    hcurDom, hcurFail, htrialsLen, htrialsDom, harchV, harchE, hout0V, hout0E,
    hout1, htdB, htdAC, hRenv⟩ := hStageP3Bridge hTight hstdin evs hevs
  exact ⟨R, w4RecvPrekeyRealDomOf_validMatch R hparse hrd hRfiles hkpk hRpeer
    hownK hownR hkpkM hresO hresN hspqrK hcurDom hcurFail htrialsLen htrialsDom
    harchV harchE hout0V hout0E hout1 htdB htdAC, hRenv⟩

theorem decPkD3ValidMatchEnv_mem_w4RecvPrekeyRealEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost} (hc : g.c = .recv peerAddr)
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (hfiles : x.F = runFiles g.i) (hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3ValidMatchCliEnv A W X B P2PathAErrEnv P2PathAOkEnv x evs →
        ∃ R : W4RecvPrekeyRealParams, ValidMatchStageP3WitnessFacts g.i peerAddr R evs) :
    ∀ evs, DecPkD3ValidMatchCliEnv A W X B P2PathAErrEnv P2PathAOkEnv x evs →
      (match g.c with | .recv _ => ValidMatchRealSlotEnv | _ => fun _ => False) evs := by
  intro evs hevs
  have hmem := decPkD3ValidMatchEnv_mem_validMatchRealSlotEnv A W X B hi hstdin hparse
    hfiles hpeer hStageP3Bridge evs hevs
  rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
  dsimp only at hc
  subst hc
  exact hmem

theorem decPkD3ValidMatchEnv_mem_existentialRealCalleeEnvs [LibsignalPlacement]
    (img : Image) (S : RunSem)
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost} (hc : g.c = .recv peerAddr)
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (hfiles : x.F = runFiles g.i) (hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3ValidMatchCliEnv A W X B P2PathAErrEnv P2PathAOkEnv x evs →
        ∃ R : W4RecvPrekeyRealParams, ValidMatchStageP3WitnessFacts g.i peerAddr R evs) :
    ∀ evs, DecPkD3ValidMatchCliEnv A W X B P2PathAErrEnv P2PathAOkEnv x evs →
      (mkExistentialRealCalleeEnvs img S ⟨W.C, W.Q⟩ g).decPkEnv evs :=
  decPkD3ValidMatchEnv_mem_w4RecvPrekeyRealEnv A W X B hc hi hstdin hparse hfiles hpeer
    hStageP3Bridge

theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_validMatch_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hMem : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      ∀ evs, DecPkEnv g evs → (mkExistentialRealCalleeEnvs img S P g).decPkEnv evs) :
    ∀ i : Inputs, CliPqOrD3RecvDom P i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_mem_w4 img S P hMem

theorem mainSt0Dom_init_cliBudgetLimits_validMatch_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hMem : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      ∀ evs, DecPkEnv g evs → (mkExistentialRealCalleeEnvs img S P g).decPkEnv evs)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_mem_w4 img S P hMem i hok

theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_validMatch_d3_1GiB [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall) (hi_g : CliPqOrD3RecvDom P g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS) :
    ∀ i : Inputs, CliPqOrD3RecvDom P i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P S_pk hCaps

theorem mainSt0Dom_init_cliBudgetLimits_validMatch_d3_1GiB [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams) {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall) (hi_g : CliPqOrD3RecvDom P g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P S_pk hCaps i hok

/-- `SpqrV1PlacedSeamsOfEnv` frozen block-`520` slot contract for `validMatch` routed via
`StageP2PathAQpanCliD3FrozenAtPlacedBudgetStmt`. -/
theorem decPkValidMatchSlotOk_at_full_of_readEnv_ofEnv_placedBudget
    [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {InitEnv : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks
      M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hP2A :
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget.StageP2PathAQpanCliD3FrozenAtPlacedBudgetStmt
        A lim X mmpl gh W P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hAesDec : HookOk
      (CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D)
      (LibsignalBinary.Heap.SpecBudget.aesDecBudgetSpec W.C.D M A lim))
    (hSpqr :
      LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.SpqrV1PlacedSeamsOfEnv
        M A lim mmpl gh W InitEnv (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget.TryDecryptCliEnvOf
        W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
        LibsignalBinary.Heap.SpecBudget.FmtWriteEnv RecvBytesEnv
        LibsignalBinary.Heap.SpecBudget.FormatInnerEnv a evs →
      tdEnv W a evs)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X cliRunBudgets ReadEnv SessDeserializeCancelEnv
        P2PathAErrEnv P2PathAOkEnv (tdEnv W) g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue.decPkValidMatchSlotOk_at_full_placedBudget
    mmpl gh W X h547 hh hRead hDeser hP2A hP3A hP3B
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue.cli_tryDecrypt_of_tdEnv_at_518
      mmpl gh W 0#64 hG hAesDec hSpqr hRecv_ne htd)
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- `SpqrV1PlacedSeamsOfEnv` frozen block-`579` `runSpecTightPlaced` lift for `validMatch`
routed via `StageP2PathAQpanCliD3FrozenAtPlacedBudgetStmt`. -/
theorem hrun_cli_validMatch_tight_at_full_of_readEnv_ofEnv_placed
    [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {InitEnv : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks
      M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hP2A :
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget.StageP2PathAQpanCliD3FrozenAtPlacedBudgetStmt
        A lim X mmpl gh W P2PathAErrEnv P2PathAOkEnv)
    (hP3A : StageP3GenStepsVRegsPlacedStmt)
    (hP3B : StageP3PrevEmptyVRegsPlacedStmt)
    (hAesDec : HookOk
      (CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D)
      (LibsignalBinary.Heap.SpecBudget.aesDecBudgetSpec W.C.D M A lim))
    (hSpqr :
      LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.SpqrV1PlacedSeamsOfEnv
        M A lim mmpl gh W InitEnv (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget.TryDecryptCliEnvOf
        W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
        LibsignalBinary.Heap.SpecBudget.FmtWriteEnv RecvBytesEnv
        LibsignalBinary.Heap.SpecBudget.FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv : ∀ g evs,
      DecPkD3ValidMatchEnv A.repAlloc W X cliRunBudgets ReadEnv SessDeserializeCancelEnv
        P2PathAErrEnv P2PathAOkEnv (tdEnv W) g evs →
      sEnvs.decryptPrekey g evs)
    (harms :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
        A lim cEnvs sEnvs aEnvs
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemD3ValidMatch X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs (cliRunSemD3ValidMatch X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
          A lim sEnvs (cliRunSemD3ValidMatch X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemD3ValidMatch X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (CryptoVerification.LibsignalFrozen lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W)))
        cliWrOk cliResStack) := by
  have hslot := decPkValidMatchSlotOk_at_full_of_readEnv_ofEnv_placedBudget mmpl gh W X h547 hG hh
    hRead hDeser hP2A hP3A hP3B hAesDec hSpqr hRecv_ne htd (cliRunSemD3ValidMatch X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl
  have hrun :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
      harms hh (hcFromSlot hslot) hpksm
      (runNeed_cli_le_resStack_placed A lim sEnvs (by decide)) (by decide) (by decide)
  exact subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPlacedBudget
