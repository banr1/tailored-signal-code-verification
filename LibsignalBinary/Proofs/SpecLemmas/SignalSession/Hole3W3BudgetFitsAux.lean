/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.ReprBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionInitiatePostCommon
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSessionPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegIdPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget

/-!
# Block-521 `initiate` (`W3`) Budget Fitness and Stage-5 Store Poll Bridge

**Checked by Lean.**

Strengthens Stage 5's block-570 `sessStorePoll` contract with `RecordGhostValid`,
proves `RecordAliceInitiatedAnyCkBounds` for the promoted session record at Stage 5,
and discharges `W3CliInitiateBudgetFits` across Stages 1–5 at
`realCliInitBinarySlotEnvFixed W`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3BudgetFitsAux

noncomputable section

open Arm64 (CalleeSavedPreserved HookSat Memory Spec State subroutine_ok subroutine_ok_outcome_intro)
open Arm64.Obj (MultiPlacement)
open ProofLib
open SepProp
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession
  (ChainKey IdentityKey KeyPair PublicKey RootKey SessionState SpqrDirection currentVersion
   initializeInitiatorSession maxReceiverChains rootCreateChain)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoGames.Ratchet (clampScalar)
open CryptoVerification (LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.E2E
  (PreKeyBundleFields UnreachedPqxdhPrimitives initiateInput initiatorRecordExtras keyPairOf
   modelPrims ofU8 pqxdhSpqrSession u8Vec vecU8)
open CryptoVerification.E2E.InMem.SessionStoreImpl (record_sessionRecordAt_eq toRecordGhost)
open CryptoVerification.E2E.Pqxdh.TopLevel (aliceInitiatedSession aliceInitiatedState
   encodeSession_aliceInitiated_length_le)
open CryptoVerification.E2E.Record (encSession encodeRecord lenField)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (encodeVarint_length_le_10)
open CryptoVerification.E2E.RecordX (sessionOfX)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded subroutine_ok_rocl_of_plain withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalSpqrV1 (Params libsignalSpqrParams)
open CryptoVerification.LibsignalTripleRatchet (calculateAgreement extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost TailVecGhost protocolAddressAt)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdPollGhost ReadRule SessStorePollGhost StoresGhost addressText dirAt
   sessStoreBoxAt)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569 lsProg_570)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (InitOk₀ bundleEOf? cliInitiateFrame cliInitiateNeed initDef initParty padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced AtStage2Placed AtStage3Placed AtStage4Placed AtStage5Placed
   IdOwnPollGhostPlaced InitTraceFsSound cliAddrTextStk cliCoinsFillStack cliCoinsFillStackPlaced
   cliDirPutStk initEntryPlaced initOom initProgPlaced stk_sub_ge_base
   transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas (mkBundleE)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas (stage4EphVec)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn scopeKit)
open CryptoVerification.SignalSession.Coins.Placed (blkPC_618 blkPl_618)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W3BinaryInitParams)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (sessStorePoll_seqFree_placed_ok_of_depsX)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv FreeOnlyAlign16Evs)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (optTailCloneLen)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid encSessionMem_eq_of_sessionGhostValid ghostCloneValid_of_sessionGhostValid
   recordGhostValid_of_sessionRecordAt)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
  (freeOnlyEvs_rustDealloc8 w3BoxedStoreStepEnv_of_exactDealloc)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec (W3BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3BoundedEvs W3InitiateFullEnvWide W3Stage1EnvWide W3Stage2Env W3Stage4Env W3Stage5Env)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (AliceInitiatedAnyCkBounds RecordAliceInitiatedAnyCkBounds)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (serializeStackX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget (AddrTextEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (CliInitSlotOkPlacedAt ExternNoAllocFailed Stage3OkEventsFit Stage3OkEventsOut W3GhostHooks
   initRunHooks_of_w3GhostHooks lsProg_not_allocFailedIn_cliGhost stage3PlacedOk_okEvents
   w3Exist_placed_ok_of_ghost w3Local_placed_ok_of_seams)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
  (cliExistingStoreCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (Stage1BudgetFits Stage1StepWitness Stage2BudgetFits Stage2StepWitness Stage3PlacedOk
   Stage4BudgetFits stage2OkEvents subroutine_ok_of_sepWPp_init_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (signal_session_coins_fill_placed_ok_at_init)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget
  (signal_session_coins_fill_vm_placed_ok_at_init signal_session_coins_fill_vm_placed_ok_of_mc_ms)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced initSlotSpecPlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced spqrInitialStateInnerSpec verifySignatureInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
  (subroutine_ok_semInitSlot_of_noAllocFail)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
  (trustPollGhostOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlacedBudget
  (sessLoadPollGhostOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudget
  (kpkSigEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudgetAux
  (spkSigEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget
  (initEntryMemPlaced initiate_stage1_placed_ok stage1BadSpkEvents stage1OkEvents stage1SigsOkEvents
   stage1TrustEvents stage1UntrustedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget
  (Stage2PlacedOk coinsFill_placed_ok_at_init_vmPreserved stage2Placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget
  (stage3AfterDh4Events stage3AfterKemBoxEvents stage3Dh1UnwindEvents
   stage3Dh2UnwindEvents stage3Dh3UnwindEvents stage3Dh4Opt stage3Dh4UnwindEvents stage3OkEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget
  (dh4OptEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExitPlacedBudget
  (stage4ErrExitEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux
  (stage4PreChainEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSessionPlacedBudget
  (stage4StepSessionEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget
  (initiate_stage4_placed_ok stage4ErrTotalEvents stage4OkTotalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudget
  (initAcceptSession initAcceptSessionGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget
  (initIdRegIdPollGhostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget
  (initIdSavePollGhost initSessStorePollGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget
  (Stage5BudgetFits initiate_stage5_placed_ok_gen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (CliIdKeyPairPollEnv CliIdRegIdPollEnv ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced
   InitStoreCalleesPlaced initStoreCallees_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
  (SetUnackPreKeyMsgEpochEnv setUnackPreKeyMsgEpochEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (InitialStateParamsEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget
  (serializeCanonSeqFree_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)

/-! ## Stage-5 `sessStorePoll` Envelope and Block-521 Assembly -/

/-- Stage-5 `sessStorePoll` allocator envelope pairing `RecordSerializeSeqFreeEnv` with `RecordGhostValid`. -/
def W3SessStorePollEnv (eEnvs : ExistingStoreCalleesEnvs)
    (x : SessStorePollGhost) (evs : List AllocEvent) : Prop :=
  RecordGhostValid (toRecordGhost x.call.call.g) x.call.call.record ∧
    CliStorePollEnv eEnvs.addressText RecordSerializeSeqFreeEnv eEnvs.dirPut x evs

/-- Strengthens block 570 (`sessStorePollSpecPlaced`) on `initProgPlaced` to `W3SessStorePollEnv`. -/
theorem w3m_sessStorePoll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) B)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (W3SessStorePollEnv eEnvs) (stk - cliInitiateFrame)) := by
  let H := cliGhostExterns gh' (cliExternsPlaced mmpl W)
  have h1 := stk_sub_ge_base hstk
  have hext : 0xd0 + max (max cliAddrTextStk serializeStackX)
      (max cliDirPutStk extHookStack) ≤ 516880 := by decide
  have h570_raw : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim
        (CliStorePollEnv eEnvs.addressText RecordSerializeSeqFreeEnv eEnvs.dirPut)
        (stk - cliInitiateFrame)) :=
    sessStorePoll_seqFree_placed_ok_of_depsX hh.alloc hExist.addressText
      (serializeCanonSeqFree_placed_ok_of_serContractsX hh.ser) hExist.dirPut (by omega)
  have h570 : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (W3SessStorePollEnv eEnvs) (stk - cliInitiateFrame)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [sessStorePollSpecPlaced] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.readReg64 .x0 = x.call.fut ∧ s0.readReg64 .x8 = x.call.out ∧
          x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
          (encodeRecord x.call.call.record).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (W3SessStorePollEnv eEnvs x)⌝ ∗
        (sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
          dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          CryptoVerification.E2E.Record.sessionRecordAt
            A.repAlloc x.call.call.recA x.call.call.g x.call.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) := by
      simpa only [sepConj_assoc] using hpre0
    rw [satisfies_pure_sepConj] at hpre'
    obtain ⟨⟨hx0, hx8, hnameLt, hrecLt, hchgLt, hfit⟩, hspatial⟩ := hpre'
    have hrec_sat : s0.mem ⊨
        CryptoVerification.E2E.Record.sessionRecordAt
            A.repAlloc x.call.call.recA x.call.call.g x.call.call.record ∗
          (sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
            dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
            protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hspatial
    have hrec_repr : s0.mem ⊨
        sessionRecordAt A.repAlloc x.call.call.recA (toRecordGhost x.call.call.g)
            x.call.call.record ∗
          (sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
            dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
            protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) := by
      rwa [← record_sessionRecordAt_eq] at hrec_sat
    have hgvalid : RecordGhostValid (toRecordGhost x.call.call.g) x.call.call.record :=
      recordGhostValid_of_sessionRecordAt hrec_repr
    have hfit_hop : FitsEnv M lim st
        (CliStorePollEnv eEnvs.addressText RecordSerializeSeqFreeEnv eEnvs.dirPut x) :=
      fun evs he => hfit evs ⟨hgvalid, he⟩
    have hm_hop : s0.mem ⊨
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv eEnvs.addressText RecordSerializeSeqFreeEnv eEnvs.dirPut)
          (stk - cliInitiateFrame)).pre (x, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only
      have h1' : s0.mem ⊨
          ⌜s0.readReg64 .x0 = x.call.fut ∧ s0.readReg64 .x8 = x.call.out ∧
            x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (encodeRecord x.call.call.record).length < 2 ^ 32 ∧
            x.dir.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollEnv eEnvs.addressText RecordSerializeSeqFreeEnv eEnvs.dirPut x)⌝ ∗
          (sessStoreBoxAt x.call.fut x.self x.call.call.addrA x.call.call.recA 0#8 ∗
            dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
            protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
            CryptoVerification.E2E.Record.sessionRecordAt
              A.repAlloc x.call.call.recA x.call.call.g x.call.call.record ∗
            A.pool lim st s0 ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hnameLt, hrecLt, hchgLt, hfit_hop⟩, hspatial⟩
      simpa only [sepConj_assoc] using h1'
    refine h570_raw.mono_outcome (x, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | h1' | h2' | h3'
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      exact ⟨evs, ⟨htr, ⟨hgvalid, hevs⟩⟩, hm⟩
    · exact Or.inr (Or.inl h1')
    · exact Or.inr (Or.inr (Or.inl h2'))
    · exact Or.inr (Or.inr (Or.inr h3'))
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh' W)
    (hi := (by decide : 521 < 619)) h570

/-- Whole-function `initiate` budget-fitness bundle routing Stage 5 through `W3SessStorePollEnv`. -/
structure W3CliInitiateBudgetFits [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop)
    (Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (s0 : State) (st0 : M.σ) : Prop where
  stage1 : Stage1BudgetFits M lim eEnvs InitEnv W X x s0 st0 st0
  stage2 : ∀ {s2 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2BudgetFits M lim eEnvs InitEnv x s0 st0
      (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0)
  stage3 : ∀ {s2 s3 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
      {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
      {pqspkPtr : BitVec 64} {opkId : BitVec 32}
      {evs1 evs2 : List AllocEvent} {box : BitVec 64},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box →
    Stage3Fit x be kp ekASk ekAPk pqspkPtr opkId s0 st0
      (M.stepEvents (stage2OkEvents evs1 evs2)
        (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0))
  stage4 : ∀ {s2 s3 s4 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
      {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
      {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
      {evs1 evs2 : List AllocEvent} {box : BitVec 64}
      {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
      {kemCtBytes hkSlotBytes : List (BitVec 8)} {evsS3 : List AllocEvent},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box →
    Stage3Out x be kp dk hdr evsS3 →
    AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
      s0 s4 →
    Stage4BudgetFits M lim InitStateEnv InitEnv W x dk st0
      (M.stepEvents evsS3
        (M.stepEvents (stage2OkEvents evs1 evs2)
          (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0)))
  stage5 : ∀ {s2 s3 s4 s5 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
      {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
      {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
      {evs1 evs2 : List AllocEvent} {box : BitVec 64}
      {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
      {kemCtBytes hkSlotBytes : List (BitVec 8)} {evsS3 : List AllocEvent}
      {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {evsSpqr : List AllocEvent},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box →
    Stage3Out x be kp dk hdr evsS3 →
    AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
      s0 s4 →
    InitStateEnv
      (libsignalSpqrParams false .a2b (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
    AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
    Stage5BudgetFits M lim InitEnv
      (CliIdRegIdPollEnv eEnvs.dirGet cliIo.rd)
      eEnvs.idSavePoll
      (W3SessStorePollEnv eEnvs)
      x be kp hdr opkId sg ss s0 st0
      (M.stepEvents (stage4OkTotalEvents W x evsSpqr)
        (M.stepEvents evsS3
          (M.stepEvents (stage2OkEvents evs1 evs2)
            (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0))))

private theorem hookSat_withStack_keepsFs {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec.keepsFs) (stk : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookSat H sym (withStack spec stk).keepsFs := by
  rcases hsat with ⟨f, hf, hok⟩
  have hws := CryptoVerification.SignalSession.Cli.MainHops.hookOk_withStack hok stk hpan hex hoom
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hws x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan' | hex' | hoom'
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, Arm64.Spec.keepsFs] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan')
  · exact Or.inr (Or.inr (Or.inl hex'))
  · exact Or.inr (Or.inr (Or.inr hoom'))

/-- Block-521 `initProgPlaced` subroutine contract over `W3CliInitiateBudgetFits`. -/
theorem w3m_cliInitiate_placed_ok_of_local [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) B)
    (hLocal : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
      InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh' W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      W3CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0) :
    subroutine_ok (initProgPlaced mmpl gh' W) initEntryPlaced
      (initSlotSpecPlaced A lim InitEnv S stk) := by
  have : InitTraceFsSound mmpl gh' W := ⟨hh.fs⟩
  have hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh' W B stk :=
    initStoreCallees_placed_ok mmpl gh' W B hh hExist stk hstk hstk64
  have hStorePollW3 := w3m_sessStorePoll_placed_ok mmpl gh' W B hh hExist hstk
  have hLoc : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk :=
    hLocal hstk hstk64
  have hStage2 : Stage2PlacedOk A lim eEnvs InitStateEnv InitEnv mmpl gh' W X B S :=
    stage2Placed_ok A lim eEnvs InitStateEnv InitEnv mmpl gh' W X B S
  have hCoinsRoCl : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 618)
        (withLsRoCl lsmpl
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget.coinsFillSpecPlacedW3 cStk)) :=
    fun hc1 hc2 => signal_session_coins_fill_placed_ok_at_init mmpl gh' W hh.allocFs hc1 hc2
  have hCoinsVmPlaced : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) :=
    fun hc1 hc2 => coinsFill_placed_ok_at_init_vmPreserved mmpl gh' W hh.allocFs hc1 hc2
  have hCoinsVm : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) := by
    intro cStk hc1 hc2
    have hge : 80 ≤ cStk := by unfold cliCoinsFillStack extHookStack at hc1; omega
    exact signal_session_coins_fill_vm_placed_ok_of_mc_ms hge hc2
      (subroutine_ok_rocl_of_plain
        (ls_hook_ok_ultra_of_mem
          (prog := (blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
          (hookSat_withStack_keepsFs hh.memcpyRegionKeepsFs (cStk - 80))))
      (subroutine_ok_rocl_of_plain
        (ls_hook_ok_ultra_of_mem
          (prog := (blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
          (hookSat_withStack_keepsFs hh.memsetRegionKeepsFs (cStk - 80))))
  apply subroutine_ok_of_sepWPp_init_placed
  rintro ⟨x, st0⟩ R s0 hpc hrun0 hpre hal
  unfold initSlotSpecPlaced at hpre
  obtain ⟨hinv, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only at hpre1
  simp only [slotFramePlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfs0, hfilesOk, hsInitOk, hspk, hFitsInit⟩,
    hcoinsLt, hm⟩ := hpre1
  have hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val :=
    hok x.F x.peer.val x.me.val hfilesOk hsInitOk
  have hs0 : AtInitEntryPlaced x s0 :=
    { pc := hpc
      run := hrun0
      inv := hinv
      spAligned := hal
      x0 := hx0
      x1 := hx1
      x2 := hx2
      x3 := hx3
      x4 := hx4
      x5 := hx5
      x6 := hx6
      x7 := hx7
      x8 := hx8
      files := hfs0 }
  have hFitAll := hFits x st0 s0 hs0 hfilesOk hsInitOk hinitOk hcoinsLt hspk hFitsInit
  refine ⟨initEntryMemPlaced A lim st0 x stk s0, ?_, ?_⟩
  · simpa only [initEntryMemPlaced, sepConj_assoc] using hm
  · have hpostK : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf →
        (((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).post (x, st0) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
      intro sf Pf ⟨hsp, hcs, hent⟩
      exact ⟨fun hmPf => Satisfies.mono (sepConj_mono_left hent) hmPf, hsp, hcs⟩
    have hpanicK : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf →
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).onPanic (x, st0) s0 sf ∗ R)) := by
      intro sf Pf hent hmPf
      exact Satisfies.mono (sepConj_mono_left hent) hmPf
    have hF1 := hFitAll.stage1
    refine initiate_stage1_placed_ok hh hStore hLoc
      hF1.fitTrustShim hF1.fitTrustPoll hF1.fitTrustClone hF1.envUntrusted
      hF1.fitSpkSer hF1.envBadSpk hF1.fitKpkSer hF1.envBadKpk
      hF1.fitLoadShim hF1.fitLoadPoll
      hS hinitOk hcoinsLt hstk hstk64 hspk hs0 hpostK hpanicK
      fun s2 be evsT1 evsT2 evsL1 evsL2 futT futL
          hevsT1 hfutTNZ hfutTAl hevsT2 hevsL1 hfutLNZ hfutLAl hevsL2 hs2 => ?_
    have hw1 : Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL :=
      ⟨hevsT1, hfutTNZ, hfutTAl, hevsT2, hevsL1, hfutLNZ, hfutLAl, hevsL2, hs2⟩
    have hF2 := hFitAll.stage2 hw1
    refine hStage2 hh @hCoinsVmPlaced hStore hLoc
      hF2.fitShim hF2.fitPoll hF2.envErr
      hS hinitOk hcoinsLt hstk hstk64 hspk hs2 hpostK hpanicK
      (fun evs1 evs2 box kp _ _ _ hkp hbox hevs1 hevs2 _ _ =>
        Entails.pure_left fun ⟨hnfit, _⟩ =>
          False.elim (hnfit (hF2.fitPqspkAlloc evs1 evs2 box kp hkp hbox hevs1 hevs2)))
      fun s3 kp ekASk ekAPk pqspkPtr opkId evs1 evs2 box hbox hevs1 hevs2 hs3 => ?_
    have hw2 : Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box :=
      ⟨hbox, hevs1, hevs2, hs3⟩
    have hF3 := hFitAll.stage3 hw1 hw2
    refine hStage3 hh @hCoinsVm @hCoinsRoCl hLoc hF3
      hS hinitOk hcoinsLt hstk hstk64 hspk hs3 hpostK hpanicK
      fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr evsS3 hevsS3 hs4 => ?_
    have hF4 := hFitAll.stage4 hw1 hw2 hevsS3 hs4
    refine initiate_stage4_placed_ok hh @hCoinsRoCl hLoc
      hF4.fitPreChain hF4.fitSpqr hF4.fitSess hF4.envErr
      hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpostK hpanicK
      fun s5 sg ss evsSpqr hevsSpqr hs5 => ?_
    have hF5 := hFitAll.stage5 hw1 hw2 hevsS3 hs4 hevsSpqr hs5
    exact initiate_stage5_placed_ok_gen hh
      hStore.rodata_idVt_regIdSlot hStore.idRegIdShim hStore.idRegIdPoll
      hStore.rodata_idVt_saveSlot hStore.idSaveShim hStore.idSavePoll
      hLoc.promoteState
      hStore.rodata_sessVt_storeSlot hStore.sessStoreShim hStorePollW3
      hStore.futDrop hLoc.dropSessionStructure
      hF5 hS hinitOk hcoinsLt hstk hstk64 hspk hs5 hpostK

/-- `CliInitSlotOkPlacedAt` producer from `W3CliInitiateBudgetFits`. -/
theorem w3m_cliInitSlotOkPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hHooks : W3GhostHooks mmpl gh' W A lim ReadEnv)
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          W3CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X) W X x s0 st0) :
    CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      A lim InitEnv X W := by
  let hh := initRunHooks_of_w3GhostHooks hHooks
  have hExist := w3Exist_placed_ok_of_ghost mmpl gh' W A lim ReadEnv hHooks
  have hLocal : ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
      InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk :=
    fun hstk hstk64 =>
      w3Local_placed_ok_of_seams mmpl gh' W A lim InitStateEnv cliRunBudgets
        hh hSpqrInit hVerifySig hstk hstk64
  intro S sEnvs needs henv hfiles hS hinitOk hneed stk h1 h2
  dsimp only [slotsOfPlaced, mkSlot] at h1 ⊢
  have hstk : cliInitiateNeed cliRunBudgets ≤ stk := hneed ▸ h1
  rw [henv]
  have h521 := w3m_cliInitiate_placed_ok_of_local mmpl gh' W X cliRunBudgets S
    hh hExist hLocal
    (stage3PlacedOk_okEvents A lim InitStateEnv InitEnv mmpl gh' W X cliRunBudgets S)
    hS (fun _ _ _ _ hio => hinitOk ▸ hio)
    stk hstk h2 (hFits S hfiles hS hinitOk hstk h2)
  have h579 := transfer_withLsCodeRoLoaded
    (callerProg := lsProg_579 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hi := (by decide : 579 < 619)) h521
  exact subroutine_ok_semInitSlot_of_noAllocFail h579
    (lsProg_not_allocFailedIn_cliGhost mmpl gh' W hghNoAlloc)

/-! ## Stage-5 `RecordAliceInitiatedAnyCkBounds` -/

private theorem lenField1_length_le (bs : List (BitVec 8)) :
    (lenField 1 bs).length ≤ bs.length + 20 := by
  unfold lenField
  have hk : (encodeKey 1 .lengthDelimited).length = 1 := by decide
  have hv := encodeVarint_length_le_10 (BitVec.ofNat 64 bs.length)
  simp only [List.length_append, hk]
  omega

/-- At Stage 5 (`AtStage5Placed`), the promoted session record satisfies `RecordAliceInitiatedAnyCkBounds` under `RecordGhostValid`. -/
theorem w3m_recordAliceInitiatedAnyCk_stage5 [LibsignalPlacement]
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {x : InitGhost}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {pqspkPtr dataPtr : BitVec 64} {opkId reg padVal w1_kyb : BitVec 32}
    {kg : TailVecGhost} {s0 s5 : State}
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hgvalid : RecordGhostValid
      ⟨0#64, 8#64, some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
      ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩) :
    RecordAliceInitiatedAnyCkBounds
      ⟨0#64, 8#64, some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
      ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩ := by
  intro G sess hG hsess
  cases hG
  cases hsess
  let sg₂ := initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg
  let sAcc := initAcceptSession be kp hdr reg x.peer.val ss
  change AliceInitiatedAnyCkBounds sg₂ sAcc
  have hsgv : LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid
      sg₂ sAcc := hgvalid
  have gcv := ghostCloneValid_of_sessionGhostValid hsgv
  have hinitSess := hs5.initSessOk
  dsimp only [initializeInitiatorSession, Bind.bind, Except.bind] at hinitSess
  cases hrc : rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) ⟨be.spkPub⟩
      (KeyPair.generate W.C (bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32))).privateKey with
  | error err => simp [hrc] at hinitSess
  | ok pair =>
    simp only [hrc, Pure.pure, Except.pure, Except.ok.injEq] at hinitSess
    subst hinitSess
    have hsessEq : sAcc = aliceInitiatedSession
        ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
        ⟨u8Vec 32 hdr.ekAPk⟩
        pair.1 (bytesToKey32 (ofU8 dk.chainKey))
        (KeyPair.generate W.C (bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)))
        pair.2 (be.opk.map Prod.fst) be.spkId be.kpkId be.regId reg
        (0x08#8 :: (u8Vec 1568 hdr.kemCt).toList)
        ((pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b (bytesToKey32 (ofU8 dk.pqrKey))) := by
      dsimp only [sAcc, initAcceptSession]
      simp [sessionOfX, initiatorRecordExtras, CryptoVerification.E2E.kyberKey,
        aliceInitiatedSession, aliceInitiatedState,
        SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
        SessionState.setUnacknowledgedPreKeyMessage, currentVersion, maxReceiverChains]
    have hkemLen : (0x08#8 :: (u8Vec 1568 hdr.kemCt).toList).length = 1569 := by
      simp [List.Vector.toList_length]
    have hpqLen :
        ((pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b (bytesToKey32 (ofU8 dk.pqrKey))).length ≤ 1208 := by
      simpa [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain] using
        hs5.pqLen
    refine
      { localIk_le := by have := gcv.localIk_len; omega
        remoteIk_le := by have := gcv.remoteIk_len; omega
        sender_le := fun gs hgs => by
          rcases gcv.sender_ok with ⟨hnone, _⟩ | ⟨gs', _, hsome, _, hsrk, hpriv⟩
          · simp [hnone] at hgs
          · rw [hsome] at hgs; cases hgs; omega
        recv_shape := by
          rw [hsessEq]
          exact Or.inr ⟨_, rfl, rfl⟩
        recv_ghost_le := fun gc hmem => by
          obtain ⟨hsrk, hpriv, _⟩ := gcv.chains_ok gc hmem
          omega
        pending_le := by have := gcv.pending_len; omega
        kyber_eq := by
          have hk := gcv.kyber_len
          rw [hsessEq] at hk
          dsimp only [aliceInitiatedSession, Option.map, Option.getD] at hk
          rw [hkemLen] at hk
          exact Or.inr (Or.inr hk)
        alice_le := by
          have hal : sg₂.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize :=
            hs5.canonPre.2.2.1
          have hlen33 : (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize.length = 33 := by
            simp [PublicKey.serialize]
          rw [hal, hlen33]
          decide
        pq_le := by
          have hpq : sAcc.state.pqRatchetState.length ≤ 1208 := by
            simpa [sAcc, initAcceptSession, sessionOfX,
              SessionState.setUnacknowledgedPreKeyMessage] using hs5.pqLen
          omega
        enc_le := by
          rw [encSessionMem_eq_of_sessionGhostValid hsgv, hsessEq]
          have hs3800 := encodeSession_aliceInitiated_length_le
            ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
            ⟨u8Vec 32 hdr.ekAPk⟩
            pair.1 (bytesToKey32 (ofU8 dk.chainKey))
            (KeyPair.generate W.C (bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)))
            pair.2 (be.opk.map Prod.fst) be.spkId be.kpkId be.regId reg
            (0x08#8 :: (u8Vec 1568 hdr.kemCt).toList)
            ((pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b (bytesToKey32 (ofU8 dk.pqrKey)))
            hkemLen hpqLen
          change (encSession _).length ≤ 3800 at hs3800
          exact Nat.le_trans (lenField1_length_le _) (Nat.add_le_add_right hs3800 20) }

/-! ## Event-List and Poll-Envelope Inclusions -/

private theorem freeOnlyEvs_append {e₁ e₂ : List AllocEvent}
    (h₁ : FreeOnlyEvs e₁) (h₂ : FreeOnlyEvs e₂) : FreeOnlyEvs (e₁ ++ e₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm₁ | hm₂
  · exact h₁ ev hm₁
  · exact h₂ ev hm₂

private theorem freeOnlyEvs_rustDealloc1 (sz : Nat) : FreeOnlyEvs (rustDeallocEvents sz 1) :=
  (FreeOnlyAlign16Evs.rustDealloc (by decide) sz).toFreeOnlyEvs

private theorem w3BoundedEvs_stage3Dh1Unwind : W3BoundedEvs 8 1569 stage3Dh1UnwindEvents := by
  unfold W3BoundedEvs; decide

private theorem w3BoundedEvs_stage3Dh2Unwind : W3BoundedEvs 8 1569 stage3Dh2UnwindEvents := by
  unfold W3BoundedEvs; decide

private theorem w3BoundedEvs_stage3Dh3Unwind : W3BoundedEvs 8 1569 stage3Dh3UnwindEvents := by
  unfold W3BoundedEvs; decide

private theorem w3BoundedEvs_stage3Dh4Unwind : W3BoundedEvs 8 1569 stage3Dh4UnwindEvents := by
  unfold W3BoundedEvs; decide

private theorem w3BoundedEvs_stage3Ok (dh4? : Option SignalPqxdh.Bytes) :
    W3BoundedEvs 8 1569 (stage3OkEvents dh4?) := by
  cases dh4? <;>
    dsimp only [W3BoundedEvs, stage3OkEvents, stage3AfterKemBoxEvents, stage3AfterDh4Events,
      dh4OptEvents] <;>
    decide

private theorem w3BoundedEvs_stage4PreChain (C : CryptoGames.LibsignalSession.Crypto)
    (spk : PublicKey) (ephClamped : List.Vector (BitVec 8) 32) :
    W3BoundedEvs 1 33 (stage4PreChainEvents C spk ephClamped) := by
  unfold stage4PreChainEvents W3BoundedEvs
  rcases calculateAgreement C.X spk ⟨ephClamped⟩ with _ | _ <;> dsimp only <;> decide

private theorem w3BoundedEvs_stage4ErrTotal (W : CliHooks) (x : InitGhost) :
    W3BoundedEvs 1 33 (stage4ErrTotalEvents W x) := by
  unfold stage4ErrTotalEvents stage4PreChainEvents W3BoundedEvs
  rcases calculateAgreement W.C.X x.bundle.spk ⟨clampScalar (stage4EphVec x.coins)⟩ with _ | _ <;>
    dsimp only <;> decide

private theorem w3BoundedEvs_stage4StepSession : W3BoundedEvs 13 416 stage4StepSessionEvents := by
  unfold W3BoundedEvs; decide

private theorem w3BoundedEvs_setUnackEpoch : W3BoundedEvs 4 68 setUnackPreKeyMsgEpochEvents := by
  unfold W3BoundedEvs; decide

private theorem sessLoadPoll_imp_kit [LibsignalPlacement]
    {x : InitGhost} {s0 : State} {futL : BitVec 64} {evs : List AllocEvent}
    (h : (cliExistingStoreCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)).sessLoadPoll
      x.F (sessLoadPollGhostOf x s0 futL) evs) :
    cliSessionKitLoadPollEnv cliIo.rd scopeKit
      (AddrTextValEnv DecimalEnv)
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
      (ofBytesEnv RecordDeserializeCancelEnv)
      x.F StoresGhost.opened.sessions x.peer.val evs := by
  rcases h with ha | ⟨e₁, e₂, rfl, ha, h2⟩
  · exact Or.inl ha
  · refine Or.inr ⟨e₁, e₂, rfl, ha, ?_⟩
    rcases h2 with hg | ⟨e₃, e₄, rfl, hg, h3⟩
    · exact Or.inl hg
    · refine Or.inr ⟨e₃, e₄, rfl, hg, ?_⟩
      have hopt : ∀ e,
          OptLoadDeserEnv (fun _ => False) (fun _ _ => False)
            (StoresGhost.opened.sessions.get cliIo.rd x.F (addressText x.peer.val)) e →
          OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
            (StoresGhost.opened.sessions.get cliIo.rd x.F (addressText x.peer.val)) e := by
        intro e ho
        generalize StoresGhost.opened.sessions.get cliIo.rd x.F (addressText x.peer.val) = res at ho ⊢
        rcases res with _ | (_ | ⟨b, tl⟩)
        · exact ho
        · exact ho
        · rcases ho with ⟨_, _, hf, _⟩
          exact False.elim hf
      rcases h3 with hd | ⟨e₅, e₆, rfl, hd, hf⟩
      · exact Or.inl (hopt _ hd)
      · exact Or.inr ⟨e₅, e₆, rfl, hopt _ hd, hf⟩

private def mkW3Params (W : CliHooks) (x : InitGhost) (pSpqr : Params)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8))) : W3BinaryInitParams :=
  { x := x
    F := W.C.F
    peerKey := x.bundle.idKey
    x_spqr := { pA := 0#64, ret := 0#64, akPtr := 0#64, p := pSpqr }
    g_rec := g_rec
    r_rec := r_rec }

private def dummySpqrParams : Params :=
  libsignalSpqrParams false .a2b 0#256

private theorem libsignalSpqrParams_authKey_le (selfSession : Bool)
    (dir : SpqrDirection) (k : BitVec 256) :
    (libsignalSpqrParams selfSession dir k).authKey.length ≤ 32 := by
  simp [libsignalSpqrParams, keyToBytes32]

private theorem recordGhostValid_none :
    RecordGhostValid ⟨0#64, 8#64, none⟩ ⟨none⟩ :=
  trivial

private theorem recordAliceInitiatedAnyCk_none :
    RecordAliceInitiatedAnyCkBounds ⟨0#64, 8#64, none⟩ ⟨none⟩ := by
  intro _ _ hG _
  cases hG

private theorem realSlot_of_slotEnv (W : CliHooks) (x : InitGhost) (pSpqr : Params)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (hp : pSpqr.authKey.length ≤ 32)
    (hgv : RecordGhostValid g_rec r_rec)
    (hal : RecordAliceInitiatedAnyCkBounds g_rec r_rec)
    {evs : List AllocEvent}
    (hevs : W3InitBinaryKitSlotEnvFixed (mkW3Params W x pSpqr g_rec r_rec) evs) :
    realCliInitBinarySlotEnvFixed W x evs :=
  ⟨mkW3Params W x pSpqr g_rec r_rec, rfl, rfl, hp, hgv, hal, hevs⟩

private theorem realSlot_of_stage1 (W : CliHooks) (x : InitGhost) {evs : List AllocEvent}
    (h1 : W3Stage1EnvWide
      (W3BoxedStoreStepEnv 32
        (cliIdentityKitTrustPollEnv
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          x.F StoresGhost.opened.identity x.peer.val x.bundle.idKey .sending))
      (W3BoxedStoreStepEnv 24
        (cliSessionKitLoadPollEnv cliIo.rd scopeKit
          (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv)
          x.F StoresGhost.opened.sessions x.peer.val))
      x.peer.name.bytes.length evs) :
    realCliInitBinarySlotEnvFixed W x evs :=
  realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
    (libsignalSpqrParams_authKey_le false .a2b 0#256)
    recordGhostValid_none recordAliceInitiatedAnyCk_none
    (Or.inl (Or.inl (Or.inl (Or.inl h1))))

private abbrev evsOf {P : List AllocEvent → Prop} {e : List AllocEvent} (_ : P e) :
    List AllocEvent := e

private theorem seqEnv_append {E₁ E₂ : List AllocEvent → Prop} {e₁ e₂ : List AllocEvent}
    (h₁ : E₁ e₁) (h₂ : E₂ e₂) : SeqEnv E₁ E₂ (e₁ ++ e₂) :=
  Or.inr ⟨e₁, e₂, rfl, h₁, h₂⟩

private theorem w3Stage1Trust_mem [LibsignalPlacement] (x : InitGhost) (s0 : State)
    {evsT1 evsT2 : List AllocEvent} {futT : BitVec 64}
    (hbT : BoxAllocEnv 32 evsT1)
    (htP : (cliExistingStoreCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)).idTrustPoll
      x.F (trustPollGhostOf x s0 futT) evsT2) :
    W3BoxedStoreStepEnv 32
      (cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        x.F StoresGhost.opened.identity x.peer.val x.bundle.idKey .sending)
      (stage1TrustEvents evsT1 evsT2) := by
  have heqT : stage1TrustEvents evsT1 evsT2 = evsT1 ++ (evsT2 ++ rustDeallocEvents 32 8) := by
    simp only [stage1TrustEvents, List.append_assoc]
  rw [heqT]
  exact w3BoxedStoreStepEnv_of_exactDealloc
    (Or.inr ⟨evsT1, evsT2 ++ rustDeallocEvents 32 8, rfl, hbT,
      Or.inr ⟨evsT2, rustDeallocEvents 32 8, rfl, htP, rfl⟩⟩)

private theorem w3Stage1Ok_mem [LibsignalPlacement] (x : InitGhost) (s0 : State)
    {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
    (hbT : BoxAllocEnv 32 evsT1)
    (htP : (cliExistingStoreCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)).idTrustPoll
      x.F (trustPollGhostOf x s0 futT) evsT2)
    (hbL : BoxAllocEnv 24 evsL1)
    (hlP : (cliExistingStoreCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)).sessLoadPoll
      x.F (sessLoadPollGhostOf x s0 futL) evsL2) :
    W3Stage1EnvWide
      (W3BoxedStoreStepEnv 32
        (cliIdentityKitTrustPollEnv
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          x.F StoresGhost.opened.identity x.peer.val x.bundle.idKey .sending))
      (W3BoxedStoreStepEnv 24
        (cliSessionKitLoadPollEnv cliIo.rd scopeKit
          (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv)
          x.F StoresGhost.opened.sessions x.peer.val))
      x.peer.name.bytes.length
      (stage1OkEvents evsT1 evsT2 evsL1 evsL2) := by
  have hTrust := w3Stage1Trust_mem x s0 hbT htP
  have hLoad : W3BoxedStoreStepEnv 24
      (cliSessionKitLoadPollEnv cliIo.rd scopeKit
        (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv)
        x.F StoresGhost.opened.sessions x.peer.val)
      (evsL1 ++ (evsL2 ++ rustDeallocEvents 24 8)) :=
    w3BoxedStoreStepEnv_of_exactDealloc
      (Or.inr ⟨evsL1, evsL2 ++ rustDeallocEvents 24 8, rfl, hbL,
        Or.inr ⟨evsL2, rustDeallocEvents 24 8, rfl, sessLoadPoll_imp_kit hlP, rfl⟩⟩)
  have heq : stage1OkEvents evsT1 evsT2 evsL1 evsL2 =
      stage1TrustEvents evsT1 evsT2 ++
        (rustAllocEvents 33 1 ++
          (rustDeallocEvents 33 1 ++
            (rustAllocEvents 1569 1 ++
              (rustDeallocEvents 1569 1 ++
                (evsL1 ++ (evsL2 ++ rustDeallocEvents 24 8)))))) := by
    simp only [stage1OkEvents, stage1SigsOkEvents, stage1BadSpkEvents, spkSigEvents, kpkSigEvents,
      List.append_assoc]
  rw [heq]
  exact Or.inr ⟨_, _, rfl, hTrust,
    Or.inr (Or.inr ⟨_, _, rfl, rfl,
      Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 33,
        Or.inr ⟨_, _, rfl, rfl,
          Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 1569, hLoad⟩⟩⟩⟩)⟩

private theorem w3Stage2Ok_mem [LibsignalPlacement] (x : InitGhost) (s0 : State)
    {evs1 evs2 : List AllocEvent} {box : BitVec 64}
    (hb : BoxAllocEnv 16 evs1)
    (hp : CliIdKeyPairPollEnv
      (cliExistingStoreCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)).dirGet cliIo.rd x.F
      { fut := box
        out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
        self := x.stores
        own := StoresGhost.opened.identity.own } evs2) :
    W3Stage2Env
      (W3BoxedStoreStepEnv 16
        (SeqEnv
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd
            x.F StoresGhost.opened.identity.own (CryptoVerification.SignalSession.Cli.utf8 "identity-key-pair"))
          (SeqEnv
            (OptIkpTryFromEnv
              (StoresGhost.opened.identity.own.get cliIo.rd x.F
                (CryptoVerification.SignalSession.Cli.utf8 "identity-key-pair")))
            FreeOnlyEvs)))
      (stage2OkEvents evs1 evs2) := by
  have hKp : W3BoxedStoreStepEnv 16 _ (evs1 ++ (evs2 ++ rustDeallocEvents 16 8)) :=
    w3BoxedStoreStepEnv_of_exactDealloc
      (Or.inr ⟨evs1, evs2 ++ rustDeallocEvents 16 8, rfl, hb,
        Or.inr ⟨evs2, rustDeallocEvents 16 8, rfl, hp, rfl⟩⟩)
  have heq : stage2OkEvents evs1 evs2 =
      (evs1 ++ (evs2 ++ rustDeallocEvents 16 8)) ++ rustAllocEvents 1568 1 := by
    simp only [stage2OkEvents, List.append_assoc]
  rw [heq]
  exact Or.inr ⟨_, _, rfl, hKp, Or.inr (Or.inr rfl)⟩

private theorem fitsEvents_of_realSlot_append (W : CliHooks) (x : InitGhost) (st0 : fineCostModel.σ)
    (hFits0 : FitsEnv fineCostModel cliBudgetLimits st0 (realCliInitBinarySlotEnvFixed W x))
    {pre stepEvs : List AllocEvent}
    (hmem : realCliInitBinarySlotEnvFixed W x (pre ++ stepEvs)) :
    FitsEvents fineCostModel cliBudgetLimits (fineCostModel.stepEvents pre st0) stepEvs :=
  ((fitsEvents_append fineCostModel cliBudgetLimits pre stepEvs st0).mp (hFits0 _ hmem)).2

/-! ## Whole-Function `W3CliInitiateBudgetFits` Discharge -/

/-- Discharges `W3CliInitiateBudgetFits` across Stages 1–5 at `realCliInitBinarySlotEnvFixed W`. -/
theorem w3m_initiate_budgetFits [LibsignalPlacement]
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (S : RunSem)
    (_hFilesOk : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (_hInit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hInitOk : S.initOk = InitOk₀ ⟨W.C, W.Q⟩)
    {stk : Nat} (_hstk_lo : cliInitiateNeed cliRunBudgets ≤ stk) (_hstk_hi : stk ≤ 2 ^ 63)
    (x : InitGhost) (st0 : fineCostModel.σ) (s0 : State)
    (_hEntry : AtInitEntryPlaced x s0)
    (_hFOk : S.filesOk x.F x.peer.val x.me.val)
    (_hIOk : S.initOk x.F x.peer.val x.me.val)
    (_hIOk0 : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (_hCoins : x.coins.length < 2 ^ 63)
    (_hSp : stk ≤ s0.sp.toNat)
    (hFits0 : FitsEnv fineCostModel cliBudgetLimits st0 (realCliInitBinarySlotEnvFixed W x)) :
    W3CliInitiateBudgetFits fineCostModel cliBudgetLimits
      (cliExistingStoreCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (InitialStateParamsEnv W.C.F)
      (realCliInitBinarySlotEnvFixed W)
      (Stage3OkEventsFit cliBudgetLimits (realCliInitBinarySlotEnvFixed W) W X)
      (Stage3OkEventsOut W X)
      W X x s0 st0 where
  stage1 :=
    { fitTrustShim := fun evsT1 hbT =>
        hFits0 evsT1 (realSlot_of_stage1 W x (Or.inl (Or.inl hbT)))
      fitTrustPoll := fun evsT1 futT hbT _ _ evsT2 htP =>
        fitsEvents_of_realSlot_append W x st0 hFits0
          (realSlot_of_stage1 W x (Or.inl (Or.inr ⟨evsT1, evsT2, rfl, hbT, Or.inl htP⟩)))
      fitTrustClone := fun evsT1 evsT2 futT hbT _ _ htP _ => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        unfold stringCloneEvents
        split_ifs with hz
        · trivial
        · exact fitsEvents_of_realSlot_append W x st0 hFits0
            (realSlot_of_stage1 W x
              (Or.inr ⟨_, _, rfl, hTrust, Or.inl (Or.inl (Or.inr rfl))⟩))
      envUntrusted := fun evsT1 evsT2 futT hbT _ _ htP _ => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        refine ⟨stage1UntrustedEvents evsT1 evsT2 x.peer.name, ?_, rfl⟩
        dsimp only [stage1UntrustedEvents]
        unfold stringCloneEvents
        split_ifs with hz
        · rw [List.append_nil]
          exact realSlot_of_stage1 W x (Or.inl hTrust)
        · exact realSlot_of_stage1 W x
            (Or.inr ⟨_, _, rfl, hTrust, Or.inl (Or.inl (Or.inr rfl))⟩)
      fitSpkSer := fun evsT1 evsT2 futT hbT _ _ htP _ => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        exact fitsEvents_of_realSlot_append W x st0 hFits0
          (realSlot_of_stage1 W x
            (Or.inr ⟨_, _, rfl, hTrust, Or.inr (Or.inl rfl)⟩))
      envBadSpk := fun evsT1 evsT2 futT _ _ _ hbT _ _ htP _ _ => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        refine ⟨stage1BadSpkEvents evsT1 evsT2, ?_, rfl⟩
        exact realSlot_of_stage1 W x
          (Or.inr ⟨stage1TrustEvents evsT1 evsT2, spkSigEvents, rfl, hTrust,
            Or.inr (Or.inr ⟨_, _, rfl, rfl, Or.inl (freeOnlyEvs_rustDealloc1 33)⟩)⟩)
      fitKpkSer := fun evsT1 evsT2 futT _ _ _ hbT _ _ htP _ _ => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        refine fitsEvents_of_realSlot_append W x st0 hFits0 (realSlot_of_stage1 W x ?_)
        have heq : stage1BadSpkEvents evsT1 evsT2 ++ rustAllocEvents 1569 1 =
            stage1TrustEvents evsT1 evsT2 ++
              (rustAllocEvents 33 1 ++ (rustDeallocEvents 33 1 ++ rustAllocEvents 1569 1)) := by
          simp only [stage1BadSpkEvents, spkSigEvents, List.append_assoc]
        rw [heq]
        exact Or.inr ⟨_, _, rfl, hTrust,
          Or.inr (Or.inr ⟨_, _, rfl, rfl,
            Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 33, Or.inl rfl⟩⟩)⟩
      envBadKpk := fun evsT1 evsT2 futT _ _ _ hbT _ _ htP _ _ _ => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        refine ⟨stage1SigsOkEvents evsT1 evsT2, ?_, rfl⟩
        have heq : stage1SigsOkEvents evsT1 evsT2 =
            stage1TrustEvents evsT1 evsT2 ++
              (rustAllocEvents 33 1 ++
                (rustDeallocEvents 33 1 ++
                  (rustAllocEvents 1569 1 ++ rustDeallocEvents 1569 1))) := by
          simp only [stage1SigsOkEvents, stage1BadSpkEvents, spkSigEvents, kpkSigEvents,
            List.append_assoc]
        rw [heq]
        exact realSlot_of_stage1 W x
          (Or.inr ⟨_, _, rfl, hTrust,
            Or.inr (Or.inr ⟨_, _, rfl, rfl,
              Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 33,
                Or.inr ⟨_, _, rfl, rfl, Or.inl (freeOnlyEvs_rustDealloc1 1569)⟩⟩⟩)⟩)
      fitLoadShim := fun evsT1 evsT2 futT _ _ hbT _ _ htP _ _ evsL1 hbL => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        refine fitsEvents_of_realSlot_append W x st0 hFits0 (realSlot_of_stage1 W x ?_)
        have heq : stage1SigsOkEvents evsT1 evsT2 ++ evsL1 =
            stage1TrustEvents evsT1 evsT2 ++
              (rustAllocEvents 33 1 ++
                (rustDeallocEvents 33 1 ++
                  (rustAllocEvents 1569 1 ++ (rustDeallocEvents 1569 1 ++ evsL1)))) := by
          simp only [stage1SigsOkEvents, stage1BadSpkEvents, spkSigEvents, kpkSigEvents,
            List.append_assoc]
        rw [heq]
        exact Or.inr ⟨_, _, rfl, hTrust,
          Or.inr (Or.inr ⟨_, _, rfl, rfl,
            Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 33,
              Or.inr ⟨_, _, rfl, rfl,
                Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 1569, Or.inl hbL⟩⟩⟩⟩)⟩
      fitLoadPoll := fun evsT1 evsT2 evsL1 futT futL _ _ hbT _ _ htP _ _ hbL _ _ evsL2 hlP => by
        have hTrust := w3Stage1Trust_mem x s0 hbT htP
        refine fitsEvents_of_realSlot_append W x st0 hFits0 (realSlot_of_stage1 W x ?_)
        have heq : (stage1SigsOkEvents evsT1 evsT2 ++ evsL1) ++ evsL2 =
            stage1TrustEvents evsT1 evsT2 ++
              (rustAllocEvents 33 1 ++
                (rustDeallocEvents 33 1 ++
                  (rustAllocEvents 1569 1 ++
                    (rustDeallocEvents 1569 1 ++ (evsL1 ++ evsL2))))) := by
          simp only [stage1SigsOkEvents, stage1BadSpkEvents, spkSigEvents, kpkSigEvents,
            List.append_assoc]
        rw [heq]
        exact Or.inr ⟨_, _, rfl, hTrust,
          Or.inr (Or.inr ⟨_, _, rfl, rfl,
            Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 33,
              Or.inr ⟨_, _, rfl, rfl,
                Or.inr ⟨_, _, rfl, freeOnlyEvs_rustDealloc1 1569,
                  Or.inr ⟨evsL1, evsL2, rfl, hbL, Or.inl (sessLoadPoll_imp_kit hlP)⟩⟩⟩⟩⟩)⟩ }
  stage2 := fun hw1 =>
    let hs1 := w3Stage1Ok_mem x s0 hw1.boxTrust hw1.trustPoll hw1.boxLoad hw1.loadPoll
    let eS1 := evsOf hs1
    { fitShim := fun evs1 hb1 =>
        fitsEvents_of_realSlot_append W x st0 hFits0
          (realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inl (Or.inr ⟨eS1, evs1, rfl, hs1, Or.inl (Or.inl hb1)⟩)))))
      fitPoll := fun evs1 box hb1 _ evs2 hp2 => by
        rw [← fineCostModel.stepEvents_append]
        have hmem : realCliInitBinarySlotEnvFixed W x ((eS1 ++ evs1) ++ evs2) := by
          rw [List.append_assoc]
          exact realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inl (Or.inr ⟨eS1, evs1 ++ evs2, rfl, hs1,
              Or.inl (Or.inr ⟨evs1, evs2, rfl, hb1, Or.inl hp2⟩)⟩))))
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      envErr := fun evs1 evs2 box _ _ hb1 hp2 => by
        refine ⟨eS1 ++ (evs1 ++ evs2 ++ rustDeallocEvents 16 8), ?_,
          (fineCostModel.stepEvents_append _ _ _).symm⟩
        refine realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
          (libsignalSpqrParams_authKey_le false .a2b 0#256)
          recordGhostValid_none recordAliceInitiatedAnyCk_none
          (Or.inl (Or.inl (Or.inl (Or.inr ⟨eS1, _, rfl, hs1, Or.inl ?_⟩))))
        rw [List.append_assoc]
        exact w3BoxedStoreStepEnv_of_exactDealloc
          (Or.inr ⟨evs1, evs2 ++ rustDeallocEvents 16 8, rfl, hb1,
            Or.inr ⟨evs2, rustDeallocEvents 16 8, rfl, hp2, rfl⟩⟩)
      fitPqspkAlloc := fun evs1 evs2 box _ _ _ hb1 hp2 => by
        rw [← fineCostModel.stepEvents_append]
        have hs2 := w3Stage2Ok_mem x s0 hb1 hp2
        have hmem : realCliInitBinarySlotEnvFixed W x
            ((eS1 ++ (evs1 ++ evs2 ++ rustDeallocEvents 16 8)) ++
              rustAllocEvents 1568 1) := by
          rw [List.append_assoc]
          exact realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inl (Or.inr ⟨eS1, stage2OkEvents evs1 evs2, rfl, hs1, hs2⟩))))
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem }
  stage3 := fun hw1 hw2 =>
    let hs1 := w3Stage1Ok_mem x s0 hw1.boxTrust hw1.trustPoll hw1.boxLoad hw1.loadPoll
    let hs2 := w3Stage2Ok_mem x s0 hw2.boxAlloc hw2.keyPairPoll
    let eS1 := evsOf hs1
    let eS2 := evsOf hs2
    let hs12 := seqEnv_append hs1 hs2
    { fitOk := by
        rw [← fineCostModel.stepEvents_append]
        exact fitsEvents_of_realSlot_append W x st0 hFits0
          (realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inr ⟨eS1 ++ eS2, _, rfl, hs12, w3BoundedEvs_stage3Ok _⟩))))
      envDh1 := fun _ => by
        refine ⟨(eS1 ++ eS2) ++ stage3Dh1UnwindEvents, ?_, ?_⟩
        · exact realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inr ⟨eS1 ++ eS2, _, rfl, hs12, w3BoundedEvs_stage3Dh1Unwind⟩)))
        · simp only [eS1, eS2, ← AllocCostModel.stepEvents_append]
      envDh2 := fun _ => by
        refine ⟨(eS1 ++ eS2) ++ stage3Dh2UnwindEvents, ?_, ?_⟩
        · exact realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inr ⟨eS1 ++ eS2, _, rfl, hs12, w3BoundedEvs_stage3Dh2Unwind⟩)))
        · simp only [eS1, eS2, ← AllocCostModel.stepEvents_append]
      envDh3 := fun _ => by
        refine ⟨(eS1 ++ eS2) ++ stage3Dh3UnwindEvents, ?_, ?_⟩
        · exact realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inr ⟨eS1 ++ eS2, _, rfl, hs12, w3BoundedEvs_stage3Dh3Unwind⟩)))
        · simp only [eS1, eS2, ← AllocCostModel.stepEvents_append]
      envDh4 := fun _ => by
        refine ⟨(eS1 ++ eS2) ++ stage3Dh4UnwindEvents, ?_, ?_⟩
        · exact realSlot_of_slotEnv W x dummySpqrParams ⟨0#64, 8#64, none⟩ ⟨none⟩
            (libsignalSpqrParams_authKey_le false .a2b 0#256)
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inl (Or.inr ⟨eS1 ++ eS2, _, rfl, hs12, w3BoundedEvs_stage3Dh4Unwind⟩)))
        · simp only [eS1, eS2, ← AllocCostModel.stepEvents_append] }
  stage4 := fun {_ _ _ be _ _ _ _ _ _ kp _ _ _ _ _ _ _ _ dk _ _ _ evsS3} hw1 hw2 hevsS3 _ =>
    let hs1 := w3Stage1Ok_mem x s0 hw1.boxTrust hw1.trustPoll hw1.boxLoad hw1.loadPoll
    let hs2 := w3Stage2Ok_mem x s0 hw2.boxAlloc hw2.keyPairPoll
    let eS1 := evsOf hs1
    let eS2 := evsOf hs2
    let pre3 := (eS1 ++ eS2) ++ evsS3
    let hs123 := seqEnv_append (seqEnv_append hs1 hs2)
      (hevsS3 ▸ w3BoundedEvs_stage3Ok (stage3Dh4Opt X W kp be x.coins))
    let pSpqr := libsignalSpqrParams false .a2b (bytesToKey32 (ofU8 dk.pqrKey))
    let hpSpqr := libsignalSpqrParams_authKey_le false .a2b (bytesToKey32 (ofU8 dk.pqrKey))
    { fitPreChain := by
        simp only [← AllocCostModel.stepEvents_append]
        exact fitsEvents_of_realSlot_append W x st0 hFits0
          (realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inr ⟨pre3, _, rfl, hs123, Or.inl (w3BoundedEvs_stage4PreChain _ _ _)⟩)))
      fitSpqr := fun _ _ _ evsSpqr hSpqr => by
        simp only [← AllocCostModel.stepEvents_append]
        have hmem : realCliInitBinarySlotEnvFixed W x
            ((pre3 ++ stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins))) ++
              evsSpqr) := by
          rw [List.append_assoc pre3]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inr ⟨pre3, _, rfl, hs123,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_stage4PreChain _ _ _, Or.inl hSpqr⟩⟩))
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      fitSess := fun _ _ evsSpqr _ hSpqr => by
        simp only [← AllocCostModel.stepEvents_append]
        have hmem : realCliInitBinarySlotEnvFixed W x
            (((pre3 ++
              stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins))) ++
              evsSpqr) ++ stage4StepSessionEvents) := by
          have heq :
              (((pre3 ++
                stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins))) ++
                evsSpqr) ++ stage4StepSessionEvents) =
              pre3 ++
                (stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins)) ++
                  (evsSpqr ++ stage4StepSessionEvents)) := by
            simp only [List.append_assoc]
          rw [heq]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inr ⟨pre3, _, rfl, hs123,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_stage4PreChain _ _ _,
                Or.inr ⟨evsSpqr, stage4StepSessionEvents, rfl, hSpqr,
                  w3BoundedEvs_stage4StepSession⟩⟩⟩))
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      envErr := fun _ => by
        refine ⟨pre3 ++ stage4ErrTotalEvents W x, ?_, ?_⟩
        · exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inl (Or.inr ⟨pre3, _, rfl, hs123, Or.inl (w3BoundedEvs_stage4ErrTotal W x)⟩))
        · simp only [pre3, eS1, eS2, ← AllocCostModel.stepEvents_append] }
  stage5 := fun {_ _ _ _ be _ _ _ _ _ _ kp _ _ _ _ opkId _ _ _ dk hdr _ _ evsS3 sg ss evsSpqr}
      hw1 hw2 hevsS3 _ hSpqr hs5 =>
    let hs1 := w3Stage1Ok_mem x s0 hw1.boxTrust hw1.trustPoll hw1.boxLoad hw1.loadPoll
    let hs2 := w3Stage2Ok_mem x s0 hw2.boxAlloc hw2.keyPairPoll
    let eS1 := evsOf hs1
    let eS2 := evsOf hs2
    let hs123 := seqEnv_append (seqEnv_append hs1 hs2)
      (hevsS3 ▸ w3BoundedEvs_stage3Ok (stage3Dh4Opt X W kp be x.coins))
    let pSpqr := libsignalSpqrParams false .a2b (bytesToKey32 (ofU8 dk.pqrKey))
    let hpSpqr := libsignalSpqrParams_authKey_le false .a2b (bytesToKey32 (ofU8 dk.pqrKey))
    let hs4 : W3Stage4Env (InitialStateEnv W.C.F
        { pA := 0#64, ret := 0#64, akPtr := 0#64, p := pSpqr })
        (stage4OkTotalEvents W x evsSpqr) := by
      have heq : stage4OkTotalEvents W x evsSpqr =
          stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins)) ++
            (evsSpqr ++ stage4StepSessionEvents) := by
        simp only [stage4OkTotalEvents, List.append_assoc]
      rw [heq]
      exact Or.inr ⟨_, _, rfl, w3BoundedEvs_stage4PreChain _ _ _,
        Or.inr ⟨evsSpqr, stage4StepSessionEvents, rfl, hSpqr, w3BoundedEvs_stage4StepSession⟩⟩
    let pre4 := ((eS1 ++ eS2) ++ evsS3) ++ stage4OkTotalEvents W x evsSpqr
    let hs1234 := seqEnv_append hs123 hs4
    { fitUnackMsg := by
        intro evsU hevsU
        subst hevsU
        simp only [← AllocCostModel.stepEvents_append]
        exact fitsEvents_of_realSlot_append W x st0 hFits0
          (realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, setUnackPreKeyMsgEpochEvents, rfl, hs1234,
              Or.inl w3BoundedEvs_setUnackEpoch⟩))
      fitRegShim := fun evsRS hbRS => by
        simp only [← AllocCostModel.stepEvents_append]
        have hmem : realCliInitBinarySlotEnvFixed W x
            ((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) := by
          rw [List.append_assoc pre4]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch, Or.inl (Or.inl hbRS)⟩⟩)
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      fitRegPoll := fun futReg evsRS hbRS evsRP hRP => by
        simp only [← AllocCostModel.stepEvents_append]
        have hmem : realCliInitBinarySlotEnvFixed W x
            (((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP) := by
          have heq : (((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP) =
              pre4 ++ (setUnackPreKeyMsgEpochEvents ++ (evsRS ++ evsRP)) := by
            simp only [List.append_assoc]
          rw [heq]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inl (Or.inr ⟨evsRS, evsRP, rfl, hbRS, Or.inl hRP⟩)⟩⟩)
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      envErr := fun _ futReg evsRS evsRP evsDrop hbRS hRP hDrop => by
        have hTailFree : FreeOnlyEvs
            (rustDeallocEvents 16 8 ++ (evsDrop ++ rustDeallocEvents 1568 1)) :=
          freeOnlyEvs_append (freeOnlyEvs_rustDealloc8 16)
            (freeOnlyEvs_append hDrop (freeOnlyEvs_rustDealloc1 1568))
        refine ⟨pre4 ++ (setUnackPreKeyMsgEpochEvents ++
          (evsRS ++ (evsRP ++ (rustDeallocEvents 16 8 ++ (evsDrop ++ rustDeallocEvents 1568 1))))),
          ?_, ?_⟩
        · exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inl (Or.inr ⟨evsRS, _, rfl, hbRS,
                  Or.inr ⟨evsRP, _, rfl, hRP, hTailFree⟩⟩)⟩⟩)
        · simp only [pre4, eS1, eS2, stage1OkEvents, stage1SigsOkEvents,
            stage1BadSpkEvents, spkSigEvents, kpkSigEvents, stage1TrustEvents, stage2OkEvents,
            ← AllocCostModel.stepEvents_append, List.append_assoc]
      fitSaveShim := fun _ _ futReg evsRS evsRP hbRS hRP evsSS hbSS => by
        simp only [← AllocCostModel.stepEvents_append]
        have hReg : W3BoxedStoreStepEnv 16 _ (evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsRS, _, rfl, hbRS, Or.inr ⟨evsRP, _, rfl, hRP, rfl⟩⟩)
        have hmem : realCliInitBinarySlotEnvFixed W x
            ((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
              rustDeallocEvents 16 8) ++ evsSS) := by
          have heq :
              ((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
                rustDeallocEvents 16 8) ++ evsSS) =
              pre4 ++ (setUnackPreKeyMsgEpochEvents ++
                ((evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) ++ evsSS)) := by
            simp only [List.append_assoc]
          rw [heq]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inr ⟨_, _, rfl, hReg, Or.inl (Or.inl hbSS)⟩⟩⟩)
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      fitSavePoll := fun _ _ futReg futSave evsRS evsRP evsSS hbRS hRP hbSS evsSP hSP => by
        simp only [← AllocCostModel.stepEvents_append]
        have hReg : W3BoxedStoreStepEnv 16 _ (evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsRS, _, rfl, hbRS, Or.inr ⟨evsRP, _, rfl, hRP, rfl⟩⟩)
        have hmem : realCliInitBinarySlotEnvFixed W x
            (((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
              rustDeallocEvents 16 8) ++ evsSS) ++ evsSP) := by
          have heq :
              (((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
                rustDeallocEvents 16 8) ++ evsSS) ++ evsSP) =
              pre4 ++ (setUnackPreKeyMsgEpochEvents ++
                ((evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) ++ (evsSS ++ evsSP))) := by
            simp only [List.append_assoc]
          rw [heq]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inr ⟨_, _, rfl, hReg,
                  Or.inl (Or.inr ⟨evsSS, evsSP, rfl, hbSS, Or.inl hSP⟩)⟩⟩⟩)
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      fitStoreShim := fun _ _ futReg futSave evsRS evsRP evsSS evsSP hbRS hRP hbSS hSP
          evsStS hbStS => by
        simp only [← AllocCostModel.stepEvents_append]
        have hReg : W3BoxedStoreStepEnv 16 _ (evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsRS, _, rfl, hbRS, Or.inr ⟨evsRP, _, rfl, hRP, rfl⟩⟩)
        have hSave : W3BoxedStoreStepEnv 32 _ (evsSS ++ (evsSP ++ rustDeallocEvents 32 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsSS, _, rfl, hbSS, Or.inr ⟨evsSP, _, rfl, hSP, rfl⟩⟩)
        have hmem : realCliInitBinarySlotEnvFixed W x
            ((((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
              rustDeallocEvents 16 8) ++ evsSS) ++ evsSP ++ rustDeallocEvents 32 8) ++ evsStS) := by
          have heq :
              ((((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
                rustDeallocEvents 16 8) ++ evsSS) ++ evsSP ++ rustDeallocEvents 32 8) ++ evsStS) =
              pre4 ++ (setUnackPreKeyMsgEpochEvents ++
                ((evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) ++
                  ((evsSS ++ (evsSP ++ rustDeallocEvents 32 8)) ++ evsStS))) := by
            simp only [List.append_assoc]
          rw [heq]
          exact realSlot_of_slotEnv W x pSpqr ⟨0#64, 8#64, none⟩ ⟨none⟩ hpSpqr
            recordGhostValid_none recordAliceInitiatedAnyCk_none
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inr ⟨_, _, rfl, hReg,
                  Or.inr ⟨_, _, rfl, hSave, Or.inl (Or.inl hbStS)⟩⟩⟩⟩)
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      fitStorePoll := fun reg _ futReg futSave futStore evsRS evsRP evsSS evsSP evsStS
          hbRS hRP hbSS hSP hbStS dataPtr padVal w1_kyb kg evsStP ⟨hgvalid, hStP⟩ => by
        simp only [← AllocCostModel.stepEvents_append]
        let gRec : RecordGhost :=
          ⟨0#64, 8#64, some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
        let rRec : SessionRecord (List (BitVec 8)) :=
          ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩
        have hgv : RecordGhostValid gRec rRec := hgvalid
        have hal : RecordAliceInitiatedAnyCkBounds gRec rRec :=
          w3m_recordAliceInitiatedAnyCk_stage5 hs5 hgv
        have hReg : W3BoxedStoreStepEnv 16 _ (evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsRS, _, rfl, hbRS, Or.inr ⟨evsRP, _, rfl, hRP, rfl⟩⟩)
        have hSave : W3BoxedStoreStepEnv 32 _ (evsSS ++ (evsSP ++ rustDeallocEvents 32 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsSS, _, rfl, hbSS, Or.inr ⟨evsSP, _, rfl, hSP, rfl⟩⟩)
        have hmem : realCliInitBinarySlotEnvFixed W x
            (((((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
              rustDeallocEvents 16 8) ++ evsSS) ++ evsSP ++ rustDeallocEvents 32 8) ++
              evsStS) ++ evsStP) := by
          have heq :
              (((((((pre4 ++ setUnackPreKeyMsgEpochEvents) ++ evsRS) ++ evsRP ++
                rustDeallocEvents 16 8) ++ evsSS) ++ evsSP ++ rustDeallocEvents 32 8) ++
                evsStS) ++ evsStP) =
              pre4 ++ (setUnackPreKeyMsgEpochEvents ++
                ((evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) ++
                  ((evsSS ++ (evsSP ++ rustDeallocEvents 32 8)) ++ (evsStS ++ evsStP)))) := by
            simp only [List.append_assoc]
          rw [heq]
          exact realSlot_of_slotEnv W x pSpqr gRec rRec hpSpqr hgv hal
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inr ⟨_, _, rfl, hReg,
                  Or.inr ⟨_, _, rfl, hSave,
                    Or.inl (Or.inr ⟨evsStS, evsStP, rfl, hbStS, Or.inl hStP⟩)⟩⟩⟩⟩)
        exact fitsEvents_of_realSlot_append W x st0 hFits0 hmem
      envOk := fun reg _ futReg futSave futStore evsRS evsRP evsSS evsSP evsStS evsStP evsDrop
          hbRS hRP hbSS hSP hbStS dataPtr padVal w1_kyb kg ⟨hgvalid, hStP⟩ hDrop => by
        let gRec : RecordGhost :=
          ⟨0#64, 8#64, some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
        let rRec : SessionRecord (List (BitVec 8)) :=
          ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩
        have hgv : RecordGhostValid gRec rRec := hgvalid
        have hal : RecordAliceInitiatedAnyCkBounds gRec rRec :=
          w3m_recordAliceInitiatedAnyCk_stage5 hs5 hgv
        have hReg : W3BoxedStoreStepEnv 16 _ (evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsRS, _, rfl, hbRS, Or.inr ⟨evsRP, _, rfl, hRP, rfl⟩⟩)
        have hSave : W3BoxedStoreStepEnv 32 _ (evsSS ++ (evsSP ++ rustDeallocEvents 32 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsSS, _, rfl, hbSS, Or.inr ⟨evsSP, _, rfl, hSP, rfl⟩⟩)
        have hStore : W3BoxedStoreStepEnv 32 _ (evsStS ++ (evsStP ++ rustDeallocEvents 32 8)) :=
          w3BoxedStoreStepEnv_of_exactDealloc
            (Or.inr ⟨evsStS, _, rfl, hbStS, Or.inr ⟨evsStP, _, rfl, hStP, rfl⟩⟩)
        have hTail : FreeOnlyEvs (rustDeallocEvents 1568 1 ++ evsDrop) :=
          freeOnlyEvs_append (freeOnlyEvs_rustDealloc1 1568) hDrop
        refine ⟨pre4 ++ (setUnackPreKeyMsgEpochEvents ++
          ((evsRS ++ (evsRP ++ rustDeallocEvents 16 8)) ++
            ((evsSS ++ (evsSP ++ rustDeallocEvents 32 8)) ++
              ((evsStS ++ (evsStP ++ rustDeallocEvents 32 8)) ++
                (rustDeallocEvents 1568 1 ++ evsDrop))))), ?_, ?_⟩
        · exact realSlot_of_slotEnv W x pSpqr gRec rRec hpSpqr hgv hal
            (Or.inr ⟨pre4, _, rfl, hs1234,
              Or.inr ⟨_, _, rfl, w3BoundedEvs_setUnackEpoch,
                Or.inr ⟨_, _, rfl, hReg,
                  Or.inr ⟨_, _, rfl, hSave,
                    Or.inr ⟨_, _, rfl, hStore, hTail⟩⟩⟩⟩⟩)
        · simp only [pre4, eS1, eS2, stage1OkEvents, stage1SigsOkEvents,
            stage1BadSpkEvents, spkSigEvents, kpkSigEvents, stage1TrustEvents, stage2OkEvents,
            ← AllocCostModel.stepEvents_append, List.append_assoc] }

end

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3BudgetFitsAux
