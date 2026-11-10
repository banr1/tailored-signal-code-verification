/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
public import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `OverD3` Stage-P2 and Stage-P4 Allocation Envelope Inclusions

Proves the `out1`-domain-independent allocation envelope inclusions for `OverD3`:
`StageP4Prev1ExitEnv` into `W4BinaryStageP4PathCWideEnvAllFixed`, and `StageP2OverEnv`
(`P2OverPathCErrEnvOf ∨ P2OverPathCOkEnvOf`) into `W4BinaryStageP2PathCWideEnvAllFixed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0EnvSub

open CryptoGames.LibsignalSession (IdentityKey PublicKey SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.Cli.E2E.V1 (bobSpqrParams)
open CryptoVerification.E2E (
  PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput modelPrims
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives bytesToBv8 ofSignalPqxdhAcceptKeysInput
  structuralPrims_initiatorModelPrims
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  acceptKeys_some_lengths ofSignalPqxdhPrimitives
)
open CryptoVerification.E2E.Record (encSession encodeRecord lenField msgField)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost utf8)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs (pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
  cliPollSessPrev1KitPlaced hdrOpkIdBv?_mkPathAHdr
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To3OkEnv P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEnv_iff_eq boxAllocEvents p2Sub1Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget (
  p2Sub4NoneEnv_iff_boxAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1OkEnvOfBob
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  MarkStepEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (
  RemoveStepEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1ExitEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget (
  StorePrev1StepEnv
)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget (bobSpqrGhost)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (
  AcceptOptFieldsEnv acceptOptFieldsEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (
  InitBobSessionBuildEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv
)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (
  W4BinaryAcceptWideEnv W4BinaryInitBobWideEnv W4BinaryPromoteArchiveEnv
  W4BinarySessStorePrev1StepEnv W4OptBoxedStoreStepEnv
)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W4BinaryIdSaveStepEnvAllFixed W4BinaryKpkGetStepEnvAllFixed W4BinaryKpkMarkStepEnvFixed
  W4BinaryPkGetStepEnvAllFixed W4BinaryPkRemoveStepEnvAllFixed W4BinarySelfKpStepEnvAllFixed
  W4BinarySelfRegIdStepEnvAllFixed W4BinarySpkGetStepEnvAllFixed
  W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathCWideEnvAllFixed
  W4BinaryStageP4PathCWideEnvAllFixed
)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (
  OptStageEnv W4BobSessionBuildEnv9 W4ErrTailWideEnv optStageEnv_nil w4ErrTailWideEnv_of_freeOnly
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (
  W4BoxedStoreStepEnv boxedDeallocPred_to_w4BoxedStoreStep rustDealloc8_freeOnly
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (SaveStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (IkpPostCleanupEnv IkpSubEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollSessPrev1SeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  P2PathAErrEnvOf
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget (
  OptIkpTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget (
  OptRegIdMalformedEnv
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)

private theorem e2ar_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) : SeqEnv E₁' E₂' evs :=
  h.elim (fun hE1 => Or.inl (h1 evs hE1))
    fun ⟨e₁, e₂, heq, hE1, hE2⟩ => Or.inr ⟨e₁, e₂, heq, h1 e₁ hE1, h2 e₂ hE2⟩

private theorem e2ar_seqEnv_optStage_nil_left {E F : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : F evs) : SeqEnv (OptStageEnv E) F evs :=
  Or.inr ⟨[], evs, rfl, optStageEnv_nil E, h⟩

private theorem e2ar_seqEnv_optStage_step {E E' F F' : List AllocEvent → Prop}
    (hE : ∀ evs, E evs → E' evs) (hF : ∀ evs, F evs → F' evs)
    {evs : List AllocEvent} (h : SeqEnv E F evs) : SeqEnv (OptStageEnv E') F' evs :=
  e2ar_seqEnv_mono (fun e he => Or.inr (hE e he)) hF h

private theorem e2ar_freeOnlyEvs_append {e1 e2 : List AllocEvent}
    (h1 : FreeOnlyEvs e1) (h2 : FreeOnlyEvs e2) : FreeOnlyEvs (e1 ++ e2) := by
  intro ev hev
  rw [List.mem_append] at hev
  rcases hev with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

/-! ## 1. Stage-P4 `Prev1` (`StageP4Prev1ExitEnv`) Inclusion into `W4BinaryStageP4PathCWideEnvAllFixed` -/

theorem h7w_saveStep_sub_w4IdSaveAllFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {evs : List AllocEvent}
    (h : SaveStepEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity peer.val remoteIk evs) :
    W4BinaryIdSaveStepEnvAllFixed cliIo.rd F0 peer remoteIk evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

theorem h7w_markStep_sub_w4KpkMarkFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles}
    {kpkId₀ spkId₀ kyberPreKeyId signedPreKeyId : BitVec 32}
    {kbk₀ baseKey : PublicKey} {evs : List AllocEvent}
    (h : MarkStepEnv
      (cliPollKpkKitPlaced A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B))
      (cliPollKpkBudgetEnv A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.kyber kyberPreKeyId signedPreKeyId baseKey evs) :
    W4BinaryKpkMarkStepEnvFixed cliIo.rd F0 kyberPreKeyId signedPreKeyId baseKey evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

theorem h7w_removeStep_sub_w4PkRemoveAllFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles} {pid₀ opkId : BitVec 32}
    {evs : List AllocEvent}
    (h : RemoveStepEnv
      (cliPollPkKitPlaced A F0 pid₀ (cliKitStk B))
      (cliPollPkBudgetEnv A F0 pid₀ (cliKitStk B) (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.oneTime opkId evs) :
    W4BinaryPkRemoveStepEnvAllFixed cliIo.rd F0 opkId evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

theorem h7w_storePrev1StepSeqFree_sub_w4SessStorePrev1 [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles} {peer : AddrGhost}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : StorePrev1StepEnv
      (cliPollSessPrev1KitPlaced A F0 peer (cliKitStk B))
      (cliPollSessPrev1SeqFreeBudgetEnv A F0 peer (cliKitStk B))
      StoresGhost.opened.sessions peer.val G ss enc evs) :
    W4BinarySessStorePrev1StepEnv peer G ss enc evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

/-- Full Stage-P4 Path-C (`Prev1`) exit envelope (`StageP4Prev1ExitEnv` at
`cliPollSessPrev1SeqFreeBudgetEnv`) inclusion into `W4BinaryStageP4PathCWideEnvAllFixed`. -/
theorem h7w_stageP4Prev1Exit_sub_w4StageP4PathCAllFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {pid₀ kpkId₀ spkId₀ kyberPreKeyId signedPreKeyId : BitVec 32}
    {kbk₀ baseKey : PublicKey} {opkId? : Option (BitVec 32)}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h :
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      StageP4Prev1ExitEnv
        (cliPollSessPrev1KitPlaced A F0 peer (cliKitStk B))
        (cliPollSessPrev1SeqFreeBudgetEnv A F0 peer (cliKitStk B))
        (cliPollIdKitPlaced A F0 peer (cliKitStk B))
        (cliPollIdBudgetEnv A F0 peer (cliKitStk B) ReadEnv)
        (cliPollPkKitPlaced A F0 pid₀ (cliKitStk B))
        (cliPollPkBudgetEnv A F0 pid₀ (cliKitStk B) ReadEnv)
        (cliPollKpkKitPlaced A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B))
        (cliPollKpkBudgetEnv A F0 kpkId₀ spkId₀ kbk₀ (cliKitStk B) ReadEnv)
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc evs) :
    W4BinaryStageP4PathCWideEnvAllFixed opkId?.isSome cliIo.rd F0 peer remoteIk
      kyberPreKeyId signedPreKeyId (opkId?.getD 0#32) baseKey G ss enc evs := by
  dsimp only [] at h
  cases opkId? with
  | none =>
    rcases h with hstore | hmarkErr | hsaveErr
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hm => e2ar_seqEnv_optStage_step
          (fun _ hmk => h7w_markStep_sub_w4KpkMarkFixed A B hmk)
          (fun _ hst => e2ar_seqEnv_optStage_nil_left
            (e2ar_seqEnv_optStage_step
              (fun _ hsp => h7w_storePrev1StepSeqFree_sub_w4SessStorePrev1 A B hsp)
              (fun _ hf => hf) hst)) hm)
        hstore
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hm => e2ar_seqEnv_optStage_step
          (fun _ hmk => h7w_markStep_sub_w4KpkMarkFixed A B hmk)
          (fun _ hf => e2ar_seqEnv_optStage_nil_left (e2ar_seqEnv_optStage_nil_left hf)) hm)
        hmarkErr
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hf => e2ar_seqEnv_optStage_nil_left
          (e2ar_seqEnv_optStage_nil_left (e2ar_seqEnv_optStage_nil_left hf)))
        hsaveErr
  | some opkId =>
    dsimp only [Option.isSome_some, Option.getD_some]
    rcases h with hstore | hremErr | hmarkErr | hsaveErr
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hm => e2ar_seqEnv_optStage_step
          (fun _ hmk => h7w_markStep_sub_w4KpkMarkFixed A B hmk)
          (fun _ hr => e2ar_seqEnv_optStage_step
            (fun _ hrm => by
              simpa only [↓reduceIte] using h7w_removeStep_sub_w4PkRemoveAllFixed A B hrm)
            (fun _ hst => e2ar_seqEnv_optStage_step
              (fun _ hsp => h7w_storePrev1StepSeqFree_sub_w4SessStorePrev1 A B hsp)
              (fun _ hf => hf) hst) hr) hm)
        hstore
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hm => e2ar_seqEnv_optStage_step
          (fun _ hmk => h7w_markStep_sub_w4KpkMarkFixed A B hmk)
          (fun _ hr => e2ar_seqEnv_optStage_step
            (fun _ hrm => by
              simpa only [↓reduceIte] using h7w_removeStep_sub_w4PkRemoveAllFixed A B hrm)
            (fun _ hf => e2ar_seqEnv_optStage_nil_left hf) hr) hm)
        hremErr
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hm => e2ar_seqEnv_optStage_step
          (fun _ hmk => h7w_markStep_sub_w4KpkMarkFixed A B hmk)
          (fun _ hf => e2ar_seqEnv_optStage_nil_left (e2ar_seqEnv_optStage_nil_left hf)) hm)
        hmarkErr
    · exact e2ar_seqEnv_optStage_step
        (fun _ hs => h7w_saveStep_sub_w4IdSaveAllFixed A B hs)
        (fun _ hf => e2ar_seqEnv_optStage_nil_left
          (e2ar_seqEnv_optStage_nil_left (e2ar_seqEnv_optStage_nil_left hf)))
        hsaveErr

/-! ## 2. Stage-P2 `Over` (`P2OverPathCErrEnvOf` & `P2OverPathCOkEnvOf`) Inclusions into `W4BinaryStageP2PathCWideEnvAllFixed` -/

private theorem e2ar_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 {evs : List AllocEvent}
    (h : InitBobSessionBuildEnv evs) :
    W4BobSessionBuildEnv9 evs := by
  rw [h]
  refine Or.inl ?_
  unfold W4BoundedEvs
  decide

private theorem e2ar_optIkpTryFromEnv_nil
    (gr : Except Unit (List (BitVec 8))) : OptIkpTryFromEnv gr [] := by
  cases gr with
  | ok bs => exact IkpSubEnv.of_cleanup IkpPostCleanupEnv.nil
  | error u => cases u; rfl

private theorem e2ar_seq_opt_freeOnly_absorb {D Opt : List AllocEvent → Prop}
    (hOptNil : Opt []) {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv D (SeqEnv Opt FreeOnlyEvs)) FreeOnlyEvs evs) :
    SeqEnv D (SeqEnv Opt FreeOnlyEvs) evs := by
  rcases h with h1 | ⟨e1, ef2, rfl, h1, hf2⟩
  · exact h1
  · rcases h1 with hd | ⟨ed, eof, rfl, hd, hof⟩
    · exact Or.inr ⟨e1, ef2, rfl, hd, Or.inr ⟨[], ef2, (List.nil_append ef2).symm, hOptNil, hf2⟩⟩
    · rcases hof with hopt | ⟨eo, ef1, rfl, hopt, hf1⟩
      · exact Or.inr ⟨ed, eof ++ ef2, by simp only [List.append_assoc], hd,
          Or.inr ⟨eof, ef2, rfl, hopt, hf2⟩⟩
      · exact Or.inr ⟨ed, eo ++ (ef1 ++ ef2), by simp only [List.append_assoc], hd,
          Or.inr ⟨eo, ef1 ++ ef2, rfl, hopt, e2ar_freeOnlyEvs_append hf1 hf2⟩⟩

private theorem e2ar_cliSelfKpOptBoxed_sub_allFixed {rd : ReadRule} {files : FsFiles}
    {evs : List AllocEvent}
    (h : W4OptBoxedStoreStepEnv 16
      (SeqEnv
        (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd files
            StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
          (SeqEnv
            (OptIkpTryFromEnv
              (StoresGhost.opened.identity.own.get rd files (utf8 "identity-key-pair")))
            FreeOnlyEvs))
        FreeOnlyEvs) evs) :
    W4BinarySelfKpStepEnvAllFixed rd files evs :=
  e2ar_seqEnv_mono (fun _ hb => hb)
    (fun _ hi => e2ar_seq_opt_freeOnly_absorb (e2ar_optIkpTryFromEnv_nil _) hi) h

private theorem e2ar_acceptOptFieldsEnv_sub_w4BoundedEvs {P : Primitives} {inp : AcceptKeysInput}
    {evs : List AllocEvent} (h : AcceptOptFieldsEnv P inp evs) :
    W4BoundedEvs 6 192 evs := by
  rw [h]
  unfold acceptOptFieldsEvents W4BoundedEvs
  dsimp only
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · split
          · decide
          · split <;> decide

private theorem e2ar_acceptOptFieldsEnv_sub_w4AcceptWide {P : Primitives} {inp : AcceptKeysInput}
    (x_res : DoReserveCall) (hasOpk : Bool) {evs : List AllocEvent}
    (h : AcceptOptFieldsEnv P inp evs) :
    W4BinaryAcceptWideEnv x_res hasOpk evs :=
  Or.inr (Or.inl (e2ar_acceptOptFieldsEnv_sub_w4BoundedEvs h))

private theorem e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide
    {P : Primitives} {F : ShaCompress} {inp : AcceptKeysInput} {drKey : DRKey}
    (x_res : DoReserveCall) (hasOpk : Bool) {evs : List AllocEvent}
    (h : InitializeBobV1OptFieldsEnv P F inp drKey evs) :
    W4BinaryInitBobWideEnv F x_res hasOpk (bobSpqrGhost 0#64 drKey.pqrKey) evs :=
  e2ar_seqEnv_mono
    (fun _ ha => e2ar_acceptOptFieldsEnv_sub_w4AcceptWide x_res hasOpk ha)
    (fun _ hs => Or.inr (e2ar_seqEnv_mono
      (fun _ hi => hi)
      (fun _ hb => Or.inr (e2ar_initBobSessionBuildEnv_sub_w4BobSessionBuildEnv9 hb)) hs))
    h

theorem h7w_promoteOverArchiveCanonSess_sub_w4PromoteArchive
    (g_arch : RecordGhost) {sess : Session (List (BitVec 8))}
    {r_arch : SessionRecord (List (BitVec 8))}
    (hcur : r_arch.currentSession = some (clearPending sess))
    {evs : List AllocEvent} (h : PromoteOverArchiveCanonSessEnv sess evs) :
    W4BinaryPromoteArchiveEnv g_arch r_arch evs := by
  have hlen : (encSession (clearPending sess)).length ≤ (encodeRecord r_arch).length := by
    simp only [encodeRecord, hcur, Option.map_some, msgField, lenField, List.length_append]
    omega
  refine Or.inr ?_
  rcases h with h96 | hnil
  · exact e2ar_seqEnv_mono (fun _ hf => hf)
      (fun _ hn => e2ar_seqEnv_mono
        (fun _ heq => ⟨(encSession (clearPending sess)).length, hlen, heq⟩)
        (fun _ h9 => e2ar_seqEnv_mono
          (fun _ he9 => by rw [he9]; unfold W4BoundedEvs; decide)
          (fun _ hf => hf) h9) hn) h96
  · exact e2ar_seqEnv_mono (fun _ hf => hf)
      (fun _ hn => e2ar_seqEnv_mono
        (fun _ heq => ⟨(encSession (clearPending sess)).length, hlen, heq⟩)
        (fun _ h0 => e2ar_seqEnv_mono
          (fun _ he0 => by rw [he0]; unfold W4BoundedEvs; decide)
          (fun _ hf => hf) h0) hn) hnil

private theorem e2ar_seqEnv_opt_tail {A B : List AllocEvent → Prop}
    {ea eb : List AllocEvent} (ha : A ea) (hb : eb = [] ∨ B eb) :
    SeqEnv A B (ea ++ eb) := by
  rcases hb with rfl | hb
  · rw [List.append_nil]; exact Or.inl ha
  · exact Or.inr ⟨ea, eb, rfl, ha, hb⟩

private theorem e2ar_pubKey33_dealloc_mem :
    OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs)
      (publicKeySerializeEvents ++ rustDeallocEvents 33 1) := by
  refine Or.inr (Or.inr ⟨publicKeySerializeEvents, rustDeallocEvents 33 1, rfl,
    by unfold W4BoundedEvs; decide, ?_⟩)
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  subst hev
  exact ⟨1, 33, rfl⟩

private theorem e2ar_box16_mem : BoxAllocEnv 16 (boxAllocEvents 16) :=
  (boxAllocEnv_iff_eq 16 _).mpr rfl

private theorem e2ar_p2Sub3TailAlloc_mem (e : List AllocEvent) (h : P2Sub3TailAllocEnv e) :
    W4BoundedEvs 1 21 e := by
  rw [h]
  unfold W4BoundedEvs
  decide

private theorem e2ar_chain5_of_parts
    {S1 S2 S3 S4 S5 Tail : List AllocEvent → Prop}
    {e1 e2 e3 e4 e5 et : List AllocEvent}
    (h1 : OptStageEnv S1 e1) (h2 : OptStageEnv S2 e2) (h3 : OptStageEnv S3 e3)
    (h4 : OptStageEnv S4 e4) (h5 : OptStageEnv S5 e5) (ht : et = [] ∨ Tail et) :
    SeqEnv (OptStageEnv S1)
      (SeqEnv (OptStageEnv S2)
        (SeqEnv (OptStageEnv S3)
          (SeqEnv (OptStageEnv S4)
            (SeqEnv (OptStageEnv S5) Tail))))
      ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ et) := by
  simp only [List.append_assoc]
  exact e2ar_seqEnv_opt_tail h1
    (Or.inr (e2ar_seqEnv_opt_tail h2
      (Or.inr (e2ar_seqEnv_opt_tail h3
        (Or.inr (e2ar_seqEnv_opt_tail h4
          (Or.inr (e2ar_seqEnv_opt_tail h5 ht))))))))

private theorem e2ar_p2Sub1To3Arm1_decomp {spkPoll : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : P2Sub1To3Arm1Env 16 spkPoll evs) :
    ∃ e1 e2,
      evs = e1 ++ e2 ++ ([] : List AllocEvent) ++ [] ++ [] ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 := by
  rcases h with rfl | ⟨es1, espk, rfl, rfl, hspk⟩
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16, ?_,
      e2ar_pubKey33_dealloc_mem, Or.inr (Or.inl e2ar_box16_mem)⟩
    simp only [p2Sub1Events, List.append_nil]
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16 ++ espk, ?_,
      e2ar_pubKey33_dealloc_mem,
      Or.inr (Or.inr ⟨boxAllocEvents 16, espk, rfl, e2ar_box16_mem, hspk⟩)⟩
    simp only [p2Sub1Events, List.append_assoc, List.append_nil]

private theorem e2ar_p2Sub1To3Arm2_decomp {spkPoll kpkPoll : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : P2Sub1To3Arm2Env 16 spkPoll 16 kpkPoll evs) :
    ∃ e1 e2 e3,
      evs = e1 ++ e2 ++ e3 ++ ([] : List AllocEvent) ++ [] ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 kpkPoll) e3 := by
  rcases h with rfl | ⟨es1, erest, rfl, rfl, hspk_rest⟩
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16, [], ?_,
      e2ar_pubKey33_dealloc_mem, Or.inr (Or.inl e2ar_box16_mem), optStageEnv_nil _⟩
    simp only [p2Sub1Events, List.append_nil]
  · rcases hspk_rest with hspk | ⟨espk, efr_rest, rfl, hspk, hfr_rest⟩
    · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16 ++ erest, [], ?_,
        e2ar_pubKey33_dealloc_mem,
        Or.inr (Or.inr ⟨boxAllocEvents 16, erest, rfl, e2ar_box16_mem, Or.inl hspk⟩),
        optStageEnv_nil _⟩
      simp only [p2Sub1Events, List.append_assoc, List.append_nil]
    · rcases hfr_rest with hfr | ⟨efr, ekpk_all, rfl, hfr, hkpk_all⟩
      · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
          boxAllocEvents 16 ++ (espk ++ efr_rest), [], ?_,
          e2ar_pubKey33_dealloc_mem,
          Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr_rest, rfl, e2ar_box16_mem,
            Or.inr ⟨espk, efr_rest, rfl, hspk, hfr⟩⟩),
          optStageEnv_nil _⟩
        simp only [p2Sub1Events, List.append_assoc, List.append_nil]
      · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
          boxAllocEvents 16 ++ (espk ++ efr), ekpk_all, ?_,
          e2ar_pubKey33_dealloc_mem,
          Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr, rfl, e2ar_box16_mem,
            Or.inr ⟨espk, efr, rfl, hspk, hfr⟩⟩),
          Or.inr hkpk_all⟩
        simp only [p2Sub1Events, List.append_assoc, List.append_nil]

private theorem e2ar_p2Sub1To3Ok_decomp {spkPoll kpkPoll : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : P2Sub1To3OkEnv 16 spkPoll 16 kpkPoll evs) :
    ∃ e1 e2 e3 e4 e5,
      evs = e1 ++ e2 ++ e3 ++ e4 ++ e5 ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 kpkPoll) e3 ∧
      OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs) e4 ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs) e5 := by
  rcases h with rfl | ⟨es1, erest, rfl, rfl, hspk_rest⟩
  · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1, boxAllocEvents 16, [], [], [], ?_,
      e2ar_pubKey33_dealloc_mem, Or.inr (Or.inl e2ar_box16_mem), optStageEnv_nil _,
      optStageEnv_nil _, optStageEnv_nil _⟩
    simp only [p2Sub1Events, List.append_nil]
  · rcases hspk_rest with hspk | ⟨espk, efr1_rest, rfl, hspk, hfr1_rest⟩
    · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
        boxAllocEvents 16 ++ erest, [], [], [], ?_,
        e2ar_pubKey33_dealloc_mem,
        Or.inr (Or.inr ⟨boxAllocEvents 16, erest, rfl, e2ar_box16_mem, Or.inl hspk⟩),
        optStageEnv_nil _, optStageEnv_nil _, optStageEnv_nil _⟩
      simp only [p2Sub1Events, List.append_assoc, List.append_nil]
    · rcases hfr1_rest with hfr1 | ⟨efr1, ekbox_rest, rfl, hfr1, hkbox_rest⟩
      · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
          boxAllocEvents 16 ++ (espk ++ efr1_rest), [], [], [], ?_,
          e2ar_pubKey33_dealloc_mem,
          Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1_rest, rfl, e2ar_box16_mem,
            Or.inr ⟨espk, efr1_rest, rfl, hspk, hfr1⟩⟩),
          optStageEnv_nil _, optStageEnv_nil _, optStageEnv_nil _⟩
        simp only [p2Sub1Events, List.append_assoc, List.append_nil]
      · rcases hkbox_rest with hkbox | ⟨ekbox, ekpk_rest, rfl, hkbox, hkpk_rest⟩
        · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
            boxAllocEvents 16 ++ (espk ++ efr1), ekbox_rest, [], [], ?_,
            e2ar_pubKey33_dealloc_mem,
            Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, e2ar_box16_mem,
              Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
            Or.inr (Or.inl hkbox), optStageEnv_nil _, optStageEnv_nil _⟩
          simp only [p2Sub1Events, List.append_assoc, List.append_nil]
        · rcases hkpk_rest with hkpk | ⟨ekpk, efr2_rest, rfl, hkpk, hfr2_rest⟩
          · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
              boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ ekpk_rest, [], [], ?_,
              e2ar_pubKey33_dealloc_mem,
              Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, e2ar_box16_mem,
                Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
              Or.inr (Or.inr ⟨ekbox, ekpk_rest, rfl, hkbox, Or.inl hkpk⟩),
              optStageEnv_nil _, optStageEnv_nil _⟩
            simp only [p2Sub1Events, List.append_assoc, List.append_nil]
          · rcases hfr2_rest with hfr2 | ⟨efr2, ekem_rest, rfl, hfr2, hkem_rest⟩
            · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2_rest), [], [], ?_,
                e2ar_pubKey33_dealloc_mem,
                Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, e2ar_box16_mem,
                  Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2_rest, rfl, hkbox,
                  Or.inr ⟨ekpk, efr2_rest, rfl, hkpk, hfr2⟩⟩),
                optStageEnv_nil _, optStageEnv_nil _⟩
              simp only [p2Sub1Events, List.append_assoc, List.append_nil]
            · rcases hkem_rest with hkem | ⟨ekem, efr3_rest, rfl, hkem, hfr3_rest⟩
              · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                  boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2), ekem_rest, [], ?_,
                  e2ar_pubKey33_dealloc_mem,
                  Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, e2ar_box16_mem,
                    Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                  Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2, rfl, hkbox,
                    Or.inr ⟨ekpk, efr2, rfl, hkpk, hfr2⟩⟩),
                  Or.inr (Or.inl hkem), optStageEnv_nil _⟩
                simp only [p2Sub1Events, List.append_assoc, List.append_nil]
              · rcases hfr3_rest with hfr3 | ⟨efr3, e21_all, rfl, hfr3, h21_all⟩
                · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                    boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2),
                    ekem ++ efr3_rest, [], ?_,
                    e2ar_pubKey33_dealloc_mem,
                    Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, e2ar_box16_mem,
                      Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                    Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2, rfl, hkbox,
                      Or.inr ⟨ekpk, efr2, rfl, hkpk, hfr2⟩⟩),
                    Or.inr (Or.inr ⟨ekem, efr3_rest, rfl, hkem, hfr3⟩), optStageEnv_nil _⟩
                  simp only [p2Sub1Events, List.append_assoc, List.append_nil]
                · refine ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
                    boxAllocEvents 16 ++ (espk ++ efr1), ekbox ++ (ekpk ++ efr2),
                    ekem ++ efr3, e21_all, ?_,
                    e2ar_pubKey33_dealloc_mem,
                    Or.inr (Or.inr ⟨boxAllocEvents 16, espk ++ efr1, rfl, e2ar_box16_mem,
                      Or.inr ⟨espk, efr1, rfl, hspk, hfr1⟩⟩),
                    Or.inr (Or.inr ⟨ekbox, ekpk ++ efr2, rfl, hkbox,
                      Or.inr ⟨ekpk, efr2, rfl, hkpk, hfr2⟩⟩),
                    Or.inr (Or.inr ⟨ekem, efr3, rfl, hkem, hfr3⟩),
                    Or.inr (e2ar_seqEnv_mono e2ar_p2Sub3TailAlloc_mem (fun _ hf => hf) h21_all)⟩
                  simp only [p2Sub1Events, List.append_assoc]

private theorem e2ar_p2Sub4Ok_decomp {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {opkId? : Option (BitVec 32)} {e4 : List AllocEvent}
    (h4 : P2Sub4OkEnv 16 pkPoll 16 opkId? e4) :
    ∃ e6 ekp_box,
      e4 = e6 ++ ekp_box ∧
      OptStageEnv
        (if opkId?.isSome then W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) else (· = []))
        e6 ∧
      OptStageEnv (BoxAllocEnv 16) ekp_box := by
  cases opkId? with
  | none =>
    exact ⟨[], e4, rfl, optStageEnv_nil _, Or.inr ((p2Sub4NoneEnv_iff_boxAllocEnv 16 e4).mp h4)⟩
  | some id =>
    dsimp only [P2Sub4OkEnv, Option.isSome_some, Option.getD_some, ↓reduceIte] at h4 ⊢
    rcases h4 with hpbox | ⟨epbox, epk_rest, rfl, hpbox, hpk_rest⟩
    · exact ⟨e4, [], (List.append_nil _).symm, Or.inr (Or.inl hpbox), optStageEnv_nil _⟩
    · rcases hpk_rest with hpk | ⟨epk, efr_rest, rfl, hpk, hfr_rest⟩
      · exact ⟨epbox ++ epk_rest, [], (List.append_nil _).symm,
          Or.inr (Or.inr ⟨epbox, epk_rest, rfl, hpbox, Or.inl hpk⟩), optStageEnv_nil _⟩
      · rcases hfr_rest with hfr | ⟨efr, ekp_box, rfl, hfr, hkp_box⟩
        · exact ⟨epbox ++ (epk ++ efr_rest), [], (List.append_nil _).symm,
            Or.inr (Or.inr ⟨epbox, epk ++ efr_rest, rfl, hpbox, Or.inr ⟨epk, efr_rest, rfl, hpk, hfr⟩⟩),
            optStageEnv_nil _⟩
        · refine ⟨epbox ++ (epk ++ efr), ekp_box, ?_,
            Or.inr (Or.inr ⟨epbox, epk ++ efr, rfl, hpbox, Or.inr ⟨epk, efr, rfl, hpk, hfr⟩⟩),
            Or.inr hkp_box⟩
          simp only [List.append_assoc]

private theorem e2ar_p2Sub1To4Ok_decomp {spkPoll kpkPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    {opkId? : Option (BitVec 32)} {e14 : List AllocEvent}
    (h14 : P2Sub1To4OkEnv 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId? e14) :
    ∃ e1 e2 e3 e4 e5 e6 ekp_box,
      e14 = (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) e1 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 spkPoll) e2 ∧
      OptStageEnv (W4BoxedStoreStepEnv 16 kpkPoll) e3 ∧
      OptStageEnv (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs) e4 ∧
      OptStageEnv (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs) e5 ∧
      OptStageEnv
        (if opkId?.isSome then W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) else (· = []))
        e6 ∧
      OptStageEnv (BoxAllocEnv 16) ekp_box := by
  rcases h14 with h13 | ⟨es13, es4, rfl, h13, h4⟩
  · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := e2ar_p2Sub1To3Ok_decomp h13
    refine ⟨e1, e2, e3, e4, e5, [], [], ?_, he1, he2, he3, he4, he5,
      optStageEnv_nil _, optStageEnv_nil _⟩
    simp only [List.append_nil]
  · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := e2ar_p2Sub1To3Ok_decomp h13
    obtain ⟨e6, ekp_box, rfl, he6, hekp⟩ := e2ar_p2Sub4Ok_decomp h4
    refine ⟨e1, e2, e3, e4, e5, e6, ekp_box, ?_, he1, he2, he3, he4, he5, he6, hekp⟩
    simp only [List.append_assoc]

private def e2ar_dummySpqrGhost : InitialStateGhost :=
  { pA := 0#64
    ret := 0#64
    akPtr := 1#64
    p := { direction := .b2a, version := .v1, minVersion := .v1, authKey := [] } }

private theorem e2ar_pathC_wrap_pathA {α : Type}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {spkId kpkId opkId : BitVec 32}
    {F : ShaCompress} {x_res : DoReserveCall} {x_spqr : InitialStateGhost}
    {evs : List AllocEvent}
    (h : W4BinaryStageP2PathAWideEnvAllFixed
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs) :
    W4BinaryStageP2PathCWideEnvAllFixed
      G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs := by
  refine e2ar_seqEnv_optStage_nil_left (e2ar_seqEnv_optStage_nil_left ?_)
  exact e2ar_seqEnv_mono (fun _ a => a)
    (fun _ x1 => e2ar_seqEnv_mono (fun _ a => a)
      (fun _ x2 => e2ar_seqEnv_mono (fun _ a => a)
        (fun _ x3 => e2ar_seqEnv_mono (fun _ a => a)
          (fun _ x4 => e2ar_seqEnv_mono (fun _ a => a)
            (fun _ x5 => e2ar_seqEnv_mono (fun _ a => a)
              (fun _ x6 => e2ar_seqEnv_mono (fun _ a => a)
                (fun _ x7 => e2ar_seqEnv_mono (fun _ a => a)
                  (fun _ x8 => e2ar_seqEnv_mono (fun _ a => a)
                    (fun _ xt => e2ar_seqEnv_optStage_nil_left xt) x8) x7) x6) x5) x4) x3) x2) x1) h

private theorem e2ar_arm1_to_pathA
    {rd : ReadRule} {files : FsFiles}
    {spkId : BitVec 32} (kpkId : BitVec 32) (opkId? : Option (BitVec 32))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    {evs : List AllocEvent} (h1 : P2Sub1To3Arm1Env 16 spkPoll evs) :
    W4BinaryStageP2PathAWideEnvAllFixed
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  obtain ⟨e1, e2, heq, he1, he2⟩ := e2ar_p2Sub1To3Arm1_decomp h1
  rw [hspkEq] at he2
  have heq' : evs = (e1 ++ e2 ++ [] ++ [] ++ []) ++ [] := by simp only [heq, List.append_nil]
  rw [heq']
  exact e2ar_chain5_of_parts he1 he2 (optStageEnv_nil _) (optStageEnv_nil _) (optStageEnv_nil _)
    (Or.inl rfl)

private theorem e2ar_arm2_to_pathA
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} (opkId? : Option (BitVec 32))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll : List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    {evs : List AllocEvent} (h2 : P2Sub1To3Arm2Env 16 spkPoll 16 kpkPoll evs) :
    W4BinaryStageP2PathAWideEnvAllFixed
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  obtain ⟨e1, e2, e3, heq, he1, he2, he3⟩ := e2ar_p2Sub1To3Arm2_decomp h2
  rw [hspkEq] at he2
  rw [hkpkEq] at he3
  have heq' : evs = (e1 ++ e2 ++ e3 ++ [] ++ []) ++ [] := by simp only [heq, List.append_nil]
  rw [heq']
  exact e2ar_chain5_of_parts he1 he2 he3 (optStageEnv_nil _) (optStageEnv_nil _) (Or.inl rfl)

private theorem e2ar_arm3_to_pathA
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    {evs : List AllocEvent} (h3 : P2Sub1To4Arm3Env 16 spkPoll 16 kpkPoll 16 pkPoll opkId? evs) :
    W4BinaryStageP2PathAWideEnvAllFixed
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  cases opkId? with
  | none => exact False.elim h3
  | some id =>
    dsimp only [P2Sub1To4Arm3Env, Option.isSome_some, Option.getD_some, ↓reduceIte] at h3 hpkEq ⊢
    rcases h3 with h13 | ⟨es13, epk_all, rfl, h13, hpk_all⟩
    · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := e2ar_p2Sub1To3Ok_decomp h13
      rw [hspkEq] at he2
      rw [hkpkEq] at he3
      have hrew : e1 ++ e2 ++ e3 ++ e4 ++ e5 = (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ [] :=
        (List.append_nil _).symm
      rw [hrew]
      exact e2ar_chain5_of_parts he1 he2 he3 he4 he5 (Or.inl rfl)
    · obtain ⟨e1, e2, e3, e4, e5, rfl, he1, he2, he3, he4, he5⟩ := e2ar_p2Sub1To3Ok_decomp h13
      rw [hspkEq] at he2
      rw [hkpkEq] at he3
      have hpk_mem : W4BinaryPkGetStepEnvAllFixed rd files id epk_all := by
        rw [← hpkEq]; exact hpk_all
      exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
        (Or.inr (Or.inl (Or.inr hpk_mem)))

private theorem e2ar_arm4_to_pathA
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll kpPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    (hkpSub : ∀ e, W4OptBoxedStoreStepEnv 16 (SeqEnv kpPoll FreeOnlyEvs) e →
      W4BinarySelfKpStepEnvAllFixed rd files e)
    {evs : List AllocEvent}
    (h : P2V1Arm4Env 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId? kpPoll evs) :
    W4BinaryStageP2PathAWideEnvAllFixed
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h14 | ⟨e14, ekp_tail, rfl, h14, hkp_tail⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
      e2ar_p2Sub1To4Ok_decomp h14
    rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
    have hkp_step : OptStageEnv (W4BinarySelfKpStepEnvAllFixed rd files) ekp_box :=
      Or.inr (hkpSub ekp_box (Or.inl hekp))
    rw [List.append_assoc ((e1 ++ e2 ++ e3 ++ e4 ++ e5))]
    exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
      (Or.inr (e2ar_seqEnv_opt_tail he6 (Or.inr (Or.inl hkp_step))))
  · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
      e2ar_p2Sub1To4Ok_decomp h14
    rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
    have hkp_step : OptStageEnv (W4BinarySelfKpStepEnvAllFixed rd files) (ekp_box ++ ekp_tail) :=
      Or.inr (hkpSub _ (Or.inr ⟨ekp_box, ekp_tail, rfl, hekp, hkp_tail⟩))
    have hrew : ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++ ekp_tail =
        (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ (e6 ++ (ekp_box ++ ekp_tail)) := by
      simp only [List.append_assoc]
    rw [hrew]
    exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
      (Or.inr (e2ar_seqEnv_opt_tail he6 (Or.inr (Or.inl hkp_step))))

private theorem e2ar_arm5_to_pathA
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    {P : Primitives} {inp : AcceptKeysInput}
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {spkPoll kpkPoll kpPoll : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    (hkpSub : ∀ e, W4OptBoxedStoreStepEnv 16 (SeqEnv kpPoll FreeOnlyEvs) e →
      W4BinarySelfKpStepEnvAllFixed rd files e)
    {evs : List AllocEvent}
    (h : P2V1Arm5EnvOfAcceptErr 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId?
      kpPoll (AcceptOptFieldsEnv P inp) evs) :
    W4BinaryStageP2PathAWideEnvAllFixed
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h14 | ⟨e14, e_after, rfl, h14, hafter⟩
  · exact e2ar_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub (Or.inl h14)
  · rcases hafter with hkp | ⟨ekp, efr_acc, rfl, hkp, hfr_acc⟩
    · exact e2ar_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
        (Or.inr ⟨e14, e_after, rfl, h14, Or.inl hkp⟩)
    · rcases hfr_acc with hfr | ⟨efr, eacc_all, rfl, hfr, hacc_all⟩
      · exact e2ar_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
          (Or.inr ⟨e14, ekp ++ efr_acc, rfl, h14, Or.inr ⟨ekp, efr_acc, rfl, hkp, hfr⟩⟩)
      · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
          e2ar_p2Sub1To4Ok_decomp h14
        rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
        have hkp_step : OptStageEnv (W4BinarySelfKpStepEnvAllFixed rd files)
            (ekp_box ++ (ekp ++ efr)) :=
          Or.inr (hkpSub _ (Or.inr ⟨ekp_box, ekp ++ efr, rfl, hekp,
            Or.inr ⟨ekp, efr, rfl, hkp, hfr⟩⟩))
        have hacc_bob :
            OptStageEnv (W4BinaryInitBobWideEnv F x_res opkId?.isSome x_spqr) eacc_all :=
          Or.inr (Or.inl (Or.inr (e2ar_seqEnv_mono
            (fun _ ha => e2ar_acceptOptFieldsEnv_sub_w4BoundedEvs ha)
            (fun _ hf => hf) hacc_all)))
        have hrew :
            ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++ (ekp ++ (efr ++ eacc_all)) =
              (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++ eacc_all)) := by
          simp only [List.append_assoc]
        rw [hrew]
        exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
          (Or.inr (e2ar_seqEnv_opt_tail he6
            (Or.inr (e2ar_seqEnv_opt_tail hkp_step (Or.inr (Or.inl hacc_bob))))))

private theorem e2ar_arm6OrOk_to_pathA
    {rd : ReadRule} {files : FsFiles}
    {spkId kpkId : BitVec 32} {opkId? : Option (BitVec 32)}
    {F : ShaCompress} (x_res : DoReserveCall) {x_spqr : InitialStateGhost}
    {spkPoll kpkPoll kpPoll regPoll BobForInp : List AllocEvent → Prop}
    {pkPoll : BitVec 32 → List AllocEvent → Prop}
    (hspkEq : W4BoxedStoreStepEnv 16 spkPoll = W4BinarySpkGetStepEnvAllFixed rd files spkId)
    (hkpkEq : W4BoxedStoreStepEnv 16 kpkPoll = W4BinaryKpkGetStepEnvAllFixed rd files kpkId)
    (hpkEq : W4BoxedStoreStepEnv 16 (pkPoll (opkId?.getD 0#32)) =
      W4BinaryPkGetStepEnvAllFixed rd files (opkId?.getD 0#32))
    (hregEq : W4BoxedStoreStepEnv 16 regPoll = W4BinarySelfRegIdStepEnvAllFixed rd files)
    (hkpSub : ∀ e, W4OptBoxedStoreStepEnv 16 (SeqEnv kpPoll FreeOnlyEvs) e →
      W4BinarySelfKpStepEnvAllFixed rd files e)
    (hbobSub : ∀ e, BobForInp e → W4BinaryInitBobWideEnv F x_res opkId?.isSome x_spqr e)
    {evs : List AllocEvent}
    (h : P2V1OkEnvOfBob 16 spkPoll 16 kpkPoll 16 pkPoll 16 opkId? kpPoll BobForInp 16 regPoll evs) :
    W4BinaryStageP2PathAWideEnvAllFixed
      opkId?.isSome rd files spkId kpkId (opkId?.getD 0#32) F x_res x_spqr evs := by
  rcases h with h14 | ⟨e14, e_after, rfl, h14, hafter⟩
  · exact e2ar_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub (Or.inl h14)
  · rcases hafter with hkp | ⟨ekp, efr_bob, rfl, hkp, hfr_bob⟩
    · exact e2ar_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
        (Or.inr ⟨e14, e_after, rfl, h14, Or.inl hkp⟩)
    · rcases hfr_bob with hfr | ⟨efr, ebob_reg, rfl, hfr, hbob_reg⟩
      · exact e2ar_arm4_to_pathA F x_res x_spqr hspkEq hkpkEq hpkEq hkpSub
          (Or.inr ⟨e14, ekp ++ efr_bob, rfl, h14, Or.inr ⟨ekp, efr_bob, rfl, hkp, hfr⟩⟩)
      · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl, he1, he2, he3, he4, he5, he6, hekp⟩ :=
          e2ar_p2Sub1To4Ok_decomp h14
        rw [hspkEq] at he2; rw [hkpkEq] at he3; rw [hpkEq] at he6
        have hkp_step : OptStageEnv (W4BinarySelfKpStepEnvAllFixed rd files)
            (ekp_box ++ (ekp ++ efr)) :=
          Or.inr (hkpSub _ (Or.inr ⟨ekp_box, ekp ++ efr, rfl, hekp,
            Or.inr ⟨ekp, efr, rfl, hkp, hfr⟩⟩))
        rcases hbob_reg with hbob | ⟨ebob, ereg6, rfl, hbob, hreg6⟩
        · have hrew :
              ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++ (ekp ++ (efr ++ ebob_reg)) =
                (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                  (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++ ebob_reg)) := by
            simp only [List.append_assoc]
          rw [hrew]
          exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
            (Or.inr (e2ar_seqEnv_opt_tail he6
              (Or.inr (e2ar_seqEnv_opt_tail hkp_step
                (Or.inr (Or.inl (Or.inr (hbobSub _ hbob))))))))
        · have hreg_mem : W4BinarySelfRegIdStepEnvAllFixed rd files ereg6 := by
            rw [← hregEq]; exact hreg6
          have hrew :
              ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++
                  (ekp ++ (efr ++ (ebob ++ ereg6))) =
                (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                  (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++ (ebob ++ ereg6))) := by
            simp only [List.append_assoc]
          rw [hrew]
          exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
            (Or.inr (e2ar_seqEnv_opt_tail he6
              (Or.inr (e2ar_seqEnv_opt_tail hkp_step
                (Or.inr (e2ar_seqEnv_opt_tail (Or.inr (hbobSub _ hbob))
                  (Or.inr (Or.inl (Or.inr hreg_mem)))))))))

private theorem e2ar_overEnd_dealloc_freeOnly :
    FreeOnlyEvs (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_append, List.mem_singleton] at hev
  rcases hev with rfl | rfl
  · exact ⟨1, 1568, rfl⟩
  · exact ⟨1, 3168, rfl⟩

/-- Stage-P2 Path-C (`Over`) error-envelope (`P2OverPathCErrEnvOf` at `InitializeBobV1OptFieldsEnv`
and `AcceptOptFieldsEnv`) inclusion into `W4BinaryStageP2PathCWideEnvAllFixed`. -/
theorem h7w_p2OverErr_sub_w4StageP2PathCAllFixed [LibsignalPlacement] {α : Type}
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (x_res : DoReserveCall)
    {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h :
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
      let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
      P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs g r evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      W4BinaryStageP2PathCWideEnvAllFixed
        G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs := by
  have hkpSub' : ∀ e,
      W4OptBoxedStoreStepEnv 16
        (SeqEnv
          (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd g.F
              StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
            (SeqEnv
              (OptIkpTryFromEnv
                (StoresGhost.opened.identity.own.get cliIo.rd g.F (utf8 "identity-key-pair")))
              FreeOnlyEvs))
          FreeOnlyEvs) e →
      W4BinarySelfKpStepEnvAllFixed cliIo.rd g.F e :=
    fun _ hx => e2ar_cliSelfKpOptBoxed_sub_allFixed hx
  dsimp only at h
  unfold P2OverPathCErrEnvOf at h
  cases hm : pkToE? g.msg with
  | none => rw [hm] at h; exact False.elim h
  | some m =>
    rw [hm] at h
    dsimp only at h
    rw [hdrOpkIdBv?_mkPathAHdr] at h
    rcases h with h1 | h2 | h3 | h4 | h56
    · exact ⟨m, e2ar_dummySpqrGhost, rfl, rfl, by decide,
        e2ar_pathC_wrap_pathA
          (e2ar_arm1_to_pathA m.kpkId m.opkId W.C.F x_res e2ar_dummySpqrGhost rfl h1)⟩
    · exact ⟨m, e2ar_dummySpqrGhost, rfl, rfl, by decide,
        e2ar_pathC_wrap_pathA
          (e2ar_arm2_to_pathA m.opkId W.C.F x_res e2ar_dummySpqrGhost rfl rfl h2)⟩
    · exact ⟨m, e2ar_dummySpqrGhost, rfl, rfl, by decide,
        e2ar_pathC_wrap_pathA
          (e2ar_arm3_to_pathA W.C.F x_res e2ar_dummySpqrGhost rfl rfl rfl h3)⟩
    · exact ⟨m, e2ar_dummySpqrGhost, rfl, rfl, by decide,
        e2ar_pathC_wrap_pathA
          (e2ar_arm4_to_pathA W.C.F x_res e2ar_dummySpqrGhost rfl rfl rfl hkpSub' h4)⟩
    · cases hk : pkStoreKeys g.F m with
      | none => rw [hk] at h56; exact False.elim h56
      | some k =>
        rw [hk] at h56
        cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd g.F with
        | error _ => rw [hkp] at h56; exact False.elim h56
        | ok kp =>
          rw [hkp] at h56
          dsimp only at h56
          rcases h56 with h5 | h6
          · exact ⟨m, e2ar_dummySpqrGhost, rfl, rfl, by decide,
              e2ar_pathC_wrap_pathA
                (e2ar_arm5_to_pathA W.C.F x_res e2ar_dummySpqrGhost rfl rfl rfl hkpSub' h5)⟩
          · cases hacc : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
              (ofSignalPqxdhAcceptKeysInput
                (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) with
            | none => rw [hacc] at h6; exact False.elim h6
            | some drKey =>
              rw [hacc] at h6
              dsimp only at h6
              have hlen32 : (bobSpqrGhost 0#64 drKey.pqrKey).p.authKey.length ≤ 32 := by
                have hsz :=
                  (acceptKeys_some_lengths
                    (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩) hacc).2.1
                dsimp only [bobSpqrGhost, bobSpqrParams, bytesToBv8]
                rw [List.length_map]
                omega
              exact ⟨m, bobSpqrGhost 0#64 drKey.pqrKey, rfl, rfl, hlen32,
                e2ar_pathC_wrap_pathA
                  (e2ar_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                    (fun _ hb => e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide x_res _ hb)
                    (show P2V1OkEnvOfBob _ _ _ _ _ _ _ _ _ _ _ _ _ from h6))⟩

/-- Stage-P2 Path-C (`Over`) normal-exit (`P2OverPathCOkEnvOf` at `InitializeBobV1OptFieldsEnv`
and `PromoteOverArchiveCanonSessEnv`) inclusion into `W4BinaryStageP2PathCWideEnvAllFixed`. -/
theorem h7w_p2OverOk_sub_w4StageP2PathCAllFixed [LibsignalPlacement] {α : Type}
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (x_res : DoReserveCall)
    {g : DecPkGhost} {r : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h :
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
      let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
      P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv
        kitEnvs g r evs) :
    ∃ (m : PreKeyMessageFields) (sess : Session (List (BitVec 8))) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      r.currentSession = some sess ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      ∀ r_arch : SessionRecord (List (BitVec 8)),
        r_arch.currentSession = some (clearPending sess) →
        W4BinaryStageP2PathCWideEnvAllFixed
          G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
          m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
          W.C.F x_res x_spqr evs := by
  have hkpSub' : ∀ e,
      W4OptBoxedStoreStepEnv 16
        (SeqEnv
          (SeqEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd g.F
              StoresGhost.opened.identity.own (utf8 "identity-key-pair"))
            (SeqEnv
              (OptIkpTryFromEnv
                (StoresGhost.opened.identity.own.get cliIo.rd g.F (utf8 "identity-key-pair")))
              FreeOnlyEvs))
          FreeOnlyEvs) e →
      W4BinarySelfKpStepEnvAllFixed cliIo.rd g.F e :=
    fun _ hx => e2ar_cliSelfKpOptBoxed_sub_allFixed hx
  dsimp only at h
  unfold P2OverPathCOkEnvOf at h
  cases hm : pkToE? g.msg with
  | none => rw [hm] at h; exact False.elim h
  | some m =>
    rw [hm] at h
    dsimp only at h
    cases hcur : r.currentSession with
    | none => rw [hcur] at h; exact False.elim h
    | some sess =>
      rw [hcur] at h
      dsimp only at h
      cases hk : pkStoreKeys g.F m with
      | none => rw [hk] at h; exact False.elim h
      | some k =>
        rw [hk] at h
        cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd g.F with
        | error _ => rw [hkp] at h; exact False.elim h
        | ok kp =>
          rw [hkp] at h
          dsimp only at h
          cases hacc : acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
              (ofSignalPqxdhAcceptKeysInput
                (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ k m)) with
          | none => rw [hacc] at h; exact False.elim h
          | some drKey =>
            rw [hacc] at h
            dsimp only at h
            rw [hdrOpkIdBv?_mkPathAHdr] at h
            have hlen32 : (bobSpqrGhost 0#64 drKey.pqrKey).p.authKey.length ≤ 32 := by
              have hsz :=
                (acceptKeys_some_lengths
                  (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩) hacc).2.1
              dsimp only [bobSpqrGhost, bobSpqrParams, bytesToBv8]
              rw [List.length_map]
              omega
            refine ⟨m, sess, bobSpqrGhost 0#64 drKey.pqrKey, rfl, rfl, rfl, hlen32, ?_⟩
            intro r_arch hr_arch
            rcases h with h14 | ⟨e14, e_after, rfl, h14, hafter⟩
            · exact e2ar_pathC_wrap_pathA
                (e2ar_arm4_to_pathA W.C.F x_res (bobSpqrGhost 0#64 drKey.pqrKey)
                  rfl rfl rfl hkpSub' (Or.inl h14))
            · rcases hafter with hkp' | ⟨ekp, efr_bob, rfl, hkp', hfr_bob⟩
              · exact e2ar_pathC_wrap_pathA
                  (e2ar_arm4_to_pathA W.C.F x_res (bobSpqrGhost 0#64 drKey.pqrKey)
                    rfl rfl rfl hkpSub' (Or.inr ⟨e14, e_after, rfl, h14, Or.inl hkp'⟩))
              · rcases hfr_bob with hfr | ⟨efr, ebob_reg, rfl, hfr, hbob_reg⟩
                · exact e2ar_pathC_wrap_pathA
                    (e2ar_arm4_to_pathA W.C.F x_res (bobSpqrGhost 0#64 drKey.pqrKey)
                      rfl rfl rfl hkpSub'
                      (Or.inr ⟨e14, ekp ++ efr_bob, rfl, h14, Or.inr ⟨ekp, efr_bob, rfl, hkp', hfr⟩⟩))
                · rcases hbob_reg with hbob | ⟨ebob, ereg_all, rfl, hbob, hreg_all⟩
                  · exact e2ar_pathC_wrap_pathA
                      (e2ar_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                        (fun _ hb => e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide x_res _ hb)
                        (Or.inr ⟨e14, ekp ++ (efr ++ ebob_reg), rfl, h14,
                          Or.inr ⟨ekp, efr ++ ebob_reg, rfl, hkp',
                            Or.inr ⟨efr, ebob_reg, rfl, hfr, Or.inl hbob⟩⟩⟩))
                  · rcases hreg_all with hrbox | ⟨erbox, erpoll_tail, rfl, hrbox, hrpoll_tail⟩
                    · exact e2ar_pathC_wrap_pathA
                        (e2ar_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                          (fun _ hb => e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide x_res _ hb)
                          (Or.inr ⟨e14, ekp ++ (efr ++ (ebob ++ ereg_all)), rfl, h14,
                            Or.inr ⟨ekp, efr ++ (ebob ++ ereg_all), rfl, hkp',
                              Or.inr ⟨efr, ebob ++ ereg_all, rfl, hfr,
                                Or.inr ⟨ebob, ereg_all, rfl, hbob, Or.inl hrbox⟩⟩⟩⟩))
                    · rcases hrpoll_tail with hrpoll | ⟨erpoll, eprom_tail, rfl, hrpoll, hprom_tail⟩
                      · exact e2ar_pathC_wrap_pathA
                          (e2ar_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                            (fun _ hb => e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide x_res _ hb)
                            (Or.inr ⟨e14, ekp ++ (efr ++ (ebob ++ (erbox ++ erpoll_tail))), rfl, h14,
                              Or.inr ⟨ekp, efr ++ (ebob ++ (erbox ++ erpoll_tail)), rfl, hkp',
                                Or.inr ⟨efr, ebob ++ (erbox ++ erpoll_tail), rfl, hfr,
                                  Or.inr ⟨ebob, erbox ++ erpoll_tail, rfl, hbob,
                                    Or.inr ⟨erbox, erpoll_tail, rfl, hrbox, Or.inl hrpoll⟩⟩⟩⟩⟩))
                      · rcases hprom_tail with rfl | ⟨ed16, eprom_end, rfl, rfl, hprom_end⟩
                        · exact e2ar_pathC_wrap_pathA
                            (e2ar_arm6OrOk_to_pathA x_res rfl rfl rfl rfl hkpSub'
                              (fun _ hb =>
                                e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide x_res _ hb)
                              (Or.inr ⟨e14,
                                ekp ++ (efr ++ (ebob ++ (erbox ++ (erpoll ++ rustDeallocEvents 16 8)))),
                                rfl, h14,
                                Or.inr ⟨ekp,
                                  efr ++ (ebob ++ (erbox ++ (erpoll ++ rustDeallocEvents 16 8))),
                                  rfl, hkp',
                                  Or.inr ⟨efr,
                                    ebob ++ (erbox ++ (erpoll ++ rustDeallocEvents 16 8)),
                                    rfl, hfr,
                                    Or.inr ⟨ebob,
                                      erbox ++ (erpoll ++ rustDeallocEvents 16 8),
                                      rfl, hbob,
                                      Or.inr ⟨erbox, erpoll ++ rustDeallocEvents 16 8, rfl, hrbox,
                                        Or.inr ⟨erpoll, rustDeallocEvents 16 8, rfl, hrpoll,
                                          rustDealloc8_freeOnly rfl⟩⟩⟩⟩⟩⟩))
                        · obtain ⟨e1, e2, e3, e4, e5, e6, ekp_box, rfl,
                            he1, he2, he3, he4, he5, he6, hekp⟩ := e2ar_p2Sub1To4Ok_decomp h14
                          have hkp_step :
                              OptStageEnv (W4BinarySelfKpStepEnvAllFixed cliIo.rd g.F)
                                (ekp_box ++ (ekp ++ efr)) :=
                            Or.inr (hkpSub' _ (Or.inr ⟨ekp_box, ekp ++ efr, rfl, hekp,
                              Or.inr ⟨ekp, efr, rfl, hkp', hfr⟩⟩))
                          have hbob_mem :
                              OptStageEnv (W4BinaryInitBobWideEnv W.C.F x_res
                                m.opkId.isSome (bobSpqrGhost 0#64 drKey.pqrKey)) ebob :=
                            Or.inr (e2ar_initializeBobV1OptFieldsEnv_sub_w4InitBobWide x_res _ hbob)
                          have hreg_mem :
                              OptStageEnv (W4BinarySelfRegIdStepEnvAllFixed cliIo.rd g.F)
                                (erbox ++ (erpoll ++ rustDeallocEvents 16 8)) :=
                            Or.inr (Or.inr ⟨erbox, erpoll ++ rustDeallocEvents 16 8, rfl, hrbox,
                              Or.inr ⟨erpoll, rustDeallocEvents 16 8, rfl, hrpoll,
                                rustDealloc8_freeOnly rfl⟩⟩)
                          have hprom_mem :
                              SeqEnv (OptStageEnv (W4BinaryPromoteArchiveEnv g_arch r_arch))
                                W4ErrTailWideEnv eprom_end := by
                            rcases hprom_end with hp | ⟨ep, ed_end, rfl, hp, rfl⟩
                            · exact Or.inl (Or.inr
                                (h7w_promoteOverArchiveCanonSess_sub_w4PromoteArchive
                                  g_arch hr_arch hp))
                            · exact Or.inr ⟨ep, rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1,
                                rfl,
                                Or.inr (h7w_promoteOverArchiveCanonSess_sub_w4PromoteArchive
                                  g_arch hr_arch hp),
                                w4ErrTailWideEnv_of_freeOnly e2ar_overEnd_dealloc_freeOnly⟩
                          refine e2ar_seqEnv_optStage_nil_left (e2ar_seqEnv_optStage_nil_left ?_)
                          have hregSz :
                              (cliPollSelfKitPlaced A g.F g.peer
                                (cliKitStk cliRunBudgets)).regIdBoxSize = 16 := rfl
                          have hrew :
                              ((e1 ++ e2 ++ e3 ++ e4 ++ e5) ++ e6 ++ ekp_box) ++
                                  (ekp ++ (efr ++ (ebob ++
                                    (erbox ++ (erpoll ++
                                      (rustDeallocEvents 16 8 ++ eprom_end)))))) =
                                (e1 ++ e2 ++ e3 ++ e4 ++ e5) ++
                                  (e6 ++ ((ekp_box ++ (ekp ++ efr)) ++
                                    (ebob ++ ((erbox ++ (erpoll ++ rustDeallocEvents 16 8)) ++
                                      eprom_end)))) := by
                            simp only [List.append_assoc]
                          rw [hregSz, hrew]
                          exact e2ar_chain5_of_parts he1 he2 he3 he4 he5
                            (Or.inr (e2ar_seqEnv_opt_tail he6
                              (Or.inr (e2ar_seqEnv_opt_tail hkp_step
                                (Or.inr (e2ar_seqEnv_opt_tail hbob_mem
                                  (Or.inr (e2ar_seqEnv_opt_tail hreg_mem
                                    (Or.inr hprom_mem)))))))))

/-- Combined `StageP2OverEnv` inclusion into `W4BinaryStageP2PathCWideEnvAllFixed`. -/
theorem h7w_stageP2Over_sub_w4StageP2PathCAllFixed [LibsignalPlacement] {α : Type}
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (x_res : DoReserveCall)
    {g : DecPkGhost} {r r_arch : SessionRecord (List (BitVec 8))}
    {s_old : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hcur : r.currentSession = some s_old)
    (hr_arch : r_arch.currentSession = some (clearPending s_old))
    (h :
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
      let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
      StageP2OverEnv
        (P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          kitEnvs)
        (P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          PromoteOverArchiveCanonSessEnv
          kitEnvs)
        g r evs) :
    ∃ (m : PreKeyMessageFields) (x_spqr : InitialStateGhost),
      pkToE? g.msg = some m ∧
      x_spqr.p.version = .v1 ∧
      x_spqr.p.authKey.length ≤ 32 ∧
      W4BinaryStageP2PathCWideEnvAllFixed
        G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
        m.opkId.isSome cliIo.rd g.F m.spkId m.kpkId (m.opkId.getD 0#32)
        W.C.F x_res x_spqr evs := by
  rcases h with herr | hok
  · exact h7w_p2OverErr_sub_w4StageP2PathCAllFixed A X W G_cur st_cur CurTrialFailEnv
      DecEnv TrialEnv DropEnv xs g_arch r_arch x_res herr
  · obtain ⟨m, sess, x_spqr, hm, hsess, hver, hlen, hp2⟩ :=
      h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W G_cur st_cur CurTrialFailEnv
        DecEnv TrialEnv DropEnv xs g_arch x_res hok
    have hse : sess = s_old := Option.some.inj (hsess.symm.trans hcur)
    subst hse
    exact ⟨m, x_spqr, hm, hver, hlen, hp2 r_arch hr_arch⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0EnvSub
