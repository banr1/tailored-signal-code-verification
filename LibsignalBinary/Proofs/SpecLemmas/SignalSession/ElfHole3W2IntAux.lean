/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFob2W2InnerLinked
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv

/-!
# Guarded-Tight `decryptSignal` (`W2`, Block `463`) Slot Envelope and Integration

**Checked by Lean.** Defines the input-reachability-guarded `decryptSignal` slot allocation envelope
`w2i_cliDecryptSignalSlotEnvGuarded` (`PeerSpqrStateTight640` implying `CliDecryptSignalSlotEnv` at
`TryDecryptCliLinkedEnv`, and `⊤` when the guard fails), proves `¬ FitsEnv M lim st (fun _ => True)`
so the false-guard branch is vacuously sound in `FitsEnv` preconditions, establishes `msgG`-insensitive
ghost congruence (`r3a_congr`), and lifts per-state guarded SPQR codec leaf contracts (blocks `325`,
`333`, `334`) to the `OkPlaced` slot obligation on block `463`.

The unguarded `W2RealTdEnv` envelope is not used because `consume_message_key` interleaves up to
`maxForwardJumps = 25000` iterations (`TryDecryptCliLinkedEnv`) and unguarded SPQR codec leaf
inclusions fail on arbitrary protobuf bytes (`fob2_not_statesFromPbEnv_sub_tight`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole3W2IntAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator MessageKeys Mut RatchetState SessionState ShaCompress
   SignalProtocolError TripleRatchet)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   pbToPqRatchetState spqrAuthApi spqrHkdfWith spqrPolyApi spqrV1 spqrV1Recv)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet
  (RecordDecryptGhost SendCall SpqrModel TrGhost TryDecryptGhost VecArg spqrRecvStack
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost ServiceIdParser SessionGhost UuidParser coinsOf protocolAddressAt serializeAddresses
   serviceIdParse signalMessageAt uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRunBudgets cliRunNeeds cliWrOk storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost RunSem decResAt idVtPlaced mkSlot sessVtPlaced slotOut slotTrace withCodeOk)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed cliDecryptSignalNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (cliExternsPlaced_rngFill encodeInjOn_deserializeScopeP_Q loadRec loadRec_unique lsRngFillSym
   scopeIn scopeKit trTrapExternsPlaced)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight isEkSide st_bCodec st_bRecvCt_tight st_bRecvEk_tight st_bSize_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliEnvOfPure TryDecryptCliLinkedEnv
   tryDecryptCmkSeg4Env tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
  (spqrRecvBranchHyps_tightLinked spqrRecvC07C09aTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvEqualTightEnv SpqrRecvTightEnv V1ChainAndEncodeTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_decode_props topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionSomeEnv FromStoreCallEnv
   FromTrustedFalseEnv FromTrustedTrueEnv LoadPollStepEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (w2IdVt_placed_ok w2SessVt_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (decSigSlotSpecBasePlaced decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (cliDecryptSignal_slot_full_placed decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv spqrRecvPlacedInnerSpecXTOfEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFob2W2InnerLinked
  (fob2_w2_inner_stateGuarded_ok_of_spqr)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv statesFromPbPlacedSpecXOfEnv
   statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (s3CommitDefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv
   s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (s7Env vmacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (verifyMacWithAddressesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromVEnv RecordDecryptEnv TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-! ## Unconstrained-Envelope Unsatisfiability and Guarded Slot Envelope -/

/-- `FitsEnv M lim st (fun _ => True)` is unsatisfiable: an allocation exceeding
`MallocngMaxAllocSize` belongs to `fun _ => True` yet violates `AllocEvent.withinMaxAlloc`. -/
theorem w2i_not_fitsEnv_top {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st (fun _ => True) := fun h =>
  Nat.not_succ_le_self MallocngMaxAllocSize
    (h [AllocEvent.alloc (MallocngMaxAllocSize + 1)] trivial).1.1

/-- Segment-4-parametric `FromS2GenEnv` wrapper generalizing `TryDecryptCliEnvOfPure` and
`TryDecryptCliLinkedEnvOf`. -/
def w2i_TryDecryptCliEnvGen (C : Crypto) (S : SpqrModel)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) s4Env (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

/-- Segment-4-parametric `PeerSpqrStateTight640`-guarded `decryptSignal` slot envelope. -/
noncomputable def w2i_cliDecryptSignalSlotEnvGuardedOf [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (x : DecSigGhost) (evs : List AllocEvent) : Prop :=
  LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
    W.C.F W.Q.K x.F x.peer.val →
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
      (w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
        (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B)
      x evs

/-- `PeerSpqrStateTight640`-guarded `decryptSignal` slot envelope specialized to
`TryDecryptCliLinkedEnv W.C W.Q.K` (reducing to `fun _ => True` when `PeerSpqrStateTight640` fails,
which `w2i_not_fitsEnv_top` excludes under `FitsEnv`). -/
noncomputable def w2i_cliDecryptSignalSlotEnvGuarded [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (x : DecSigGhost) (evs : List AllocEvent) : Prop :=
  LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
    W.C.F W.Q.K x.F x.peer.val →
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (TryDecryptCliLinkedEnv W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B)
      x evs

theorem w2i_cliDecryptSignalSlotEnvGuarded_eq_of [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets) :
    w2i_cliDecryptSignalSlotEnvGuarded W A B =
      w2i_cliDecryptSignalSlotEnvGuardedOf W (tryDecryptCmkSeg4Env FmtWriteEnv) A B := rfl

/-! ## Ghost Congruence (`r3a_congr`) -/

private theorem w2i_seqEnv_congr {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : E₁ = E₁') (h2 : E₂ = E₂') :
    SeqEnv E₁ E₂ = SeqEnv E₁' E₂' := by
  subst h1; subst h2; rfl

private theorem w2i_or_congr {P P' Q Q' : Prop} (hp : P = P') (hq : Q = Q') :
    (P ∨ Q) = (P' ∨ Q') := by
  rw [hp, hq]

private theorem w2i_and_congr {P P' Q Q' : Prop} (hp : P = P') (hq : Q = Q') :
    (P ∧ Q) = (P' ∧ Q') := by
  rw [hp, hq]

private theorem w2i_exists_congr {α : Sort _} {P Q : α → Prop} (h : ∀ a, P a = Q a) :
    (∃ a, P a) = (∃ a, Q a) := by
  simp only [h]

private theorem w2i_serializeAddresses_congr (parse : ServiceIdParser)
    (s₁ s₂ r₁ r₂ : AddrGhost)
    (hsb : s₁.name.bytes = s₂.name.bytes) (hsd : s₁.device = s₂.device)
    (hrb : r₁.name.bytes = r₂.name.bytes) (hrd : r₁.device = r₂.device) :
    serializeAddresses parse s₁ r₁ = serializeAddresses parse s₂ r₂ := by
  unfold serializeAddresses
  rw [hsb, hsd, hrb, hrd]

private theorem w2i_fromS2GenEnv_ghost_congr_gen
    (C : Crypto) (S : SpqrModel)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (x₁ x₂ : TryDecryptGhost)
    (hs4 : s4Env x₁ = s4Env x₂)
    (hrem_b : x₁.rem.name.bytes = x₂.rem.name.bytes) (hrem_d : x₁.rem.device = x₂.rem.device)
    (hloc_b : x₁.loc.name.bytes = x₂.loc.name.bytes) (hloc_d : x₁.loc.device = x₂.loc.device)
    (hmsg : x₁.msg = x₂.msg) (hmt : x₁.msgType = x₂.msgType) (hrest : x₁.rest = x₂.rest) :
    FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) s4Env (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₁ =
      FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) s4Env (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₂ := by
  have hser :
      serializeAddresses (serviceIdParse uuidTryParse) x₁.rem x₁.loc =
        serializeAddresses (serviceIdParse uuidTryParse) x₂.rem x₂.loc :=
    w2i_serializeAddresses_congr (serviceIdParse uuidTryParse) x₁.rem x₂.rem x₁.loc x₂.loc
      hrem_b hrem_d hloc_b hloc_d
  have hs3 : s3DefaultEnv C x₁ = s3DefaultEnv C x₂ := by
    funext trG tr
    unfold s3DefaultEnv s3EnvOf s3CommitDefaultEnv
    dsimp only
    rw [hmsg, hrest]
  have hs5 : PqRecvEnv S RecvBytesEnv fmtEnv x₁ = PqRecvEnv S RecvBytesEnv fmtEnv x₂ := by
    funext tr
    unfold PqRecvEnv
    rw [hmsg]
  have hs7 : s7Env C.F uuidTryParse x₁ = s7Env C.F uuidTryParse x₂ := by
    funext tr mks newPqrState
    have hv : vmacEvents C.F uuidTryParse x₁ tr mks = vmacEvents C.F uuidTryParse x₂ tr mks := by
      unfold vmacEvents verifyMacWithAddressesEvents
      dsimp only
      rw [hmsg, hser]
    unfold s7Env
    rw [hv]
  have hs8 : s8Env x₁ = s8Env x₂ := by
    funext mks newPqrState
    unfold s8Env
    rw [hmsg]
  have hs8g : FromS8GenEnv (stdAesOpt C) s8Env s9Env x₁ =
      FromS8GenEnv (stdAesOpt C) s8Env s9Env x₂ := by
    funext trG tr st1 mks newPqrState
    unfold FromS8GenEnv s9Env
    rw [hmsg, hs8]
  have hs7g : FromS7GenEnv C uuidTryParse (stdAesOpt C) (s7Env C.F uuidTryParse) s8Env s9Env x₁ =
      FromS7GenEnv C uuidTryParse (stdAesOpt C) (s7Env C.F uuidTryParse) s8Env s9Env x₂ := by
    funext trG tr st1 mks newPqrState
    unfold FromS7GenEnv
    rw [hmsg, hser, hs7, hs8g]
  have hs6g : FromS6GenEnv C uuidTryParse (stdAesOpt C) s6FreeOnlyEnv
      (s7Env C.F uuidTryParse) s8Env s9Env x₁ =
      FromS6GenEnv C uuidTryParse (stdAesOpt C) s6FreeOnlyEnv
        (s7Env C.F uuidTryParse) s8Env s9Env x₂ := by
    funext trG tr st1 mkg newPqrState pqrKey
    unfold FromS6GenEnv
    rw [hs7g]
  have hs5g : FromS5GenEnv C uuidTryParse S (stdAesOpt C) (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₁ =
      FromS5GenEnv C uuidTryParse S (stdAesOpt C) (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₂ := by
    funext trG tr st1 mkg
    unfold FromS5GenEnv
    rw [hmsg, hs5, hs6g]
  have hs4g : FromS4GenEnv C uuidTryParse S (stdAesOpt C) s4Env
      (PqRecvEnv S RecvBytesEnv fmtEnv) s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₁ =
      FromS4GenEnv C uuidTryParse S (stdAesOpt C) s4Env
        (PqRecvEnv S RecvBytesEnv fmtEnv) s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₂ := by
    funext trG tr st1 ck
    unfold FromS4GenEnv
    rw [hmsg, hmt, hs4, hs5g]
  have hs3g : FromS3GenEnv C uuidTryParse S (stdAesOpt C) (s3DefaultEnv C)
      s4Env (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₁ =
      FromS3GenEnv C uuidTryParse S (stdAesOpt C) (s3DefaultEnv C)
        s4Env (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env x₂ := by
    funext trG tr st1
    unfold FromS3GenEnv
    rw [hmsg, hrest, hs3, hs4g]
  funext trG tr st1
  unfold FromS2GenEnv
  rw [hmsg, hs4g, hs3g]

theorem w2i_tryDecryptCliEnvGen_congr
    (C : Crypto) (S : SpqrModel)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a₁ a₂ : TryDecryptEnvArgs)
    (hs4 : s4Env (tryDecryptEnvArgsToGhost a₁) = s4Env (tryDecryptEnvArgsToGhost a₂))
    (hG : a₁.G = a₂.G) (hst : a₁.st = a₂.st)
    (hrem_b : a₁.rem.name.bytes = a₂.rem.name.bytes) (hrem_d : a₁.rem.device = a₂.rem.device)
    (hloc_b : a₁.loc.name.bytes = a₂.loc.name.bytes) (hloc_d : a₁.loc.device = a₂.loc.device)
    (hmsg : a₁.msg = a₂.msg) (hmt : a₁.msgType = a₂.msgType) (hrest : a₁.rest = a₂.rest) :
    w2i_TryDecryptCliEnvGen C S s4Env RecvBytesEnv fmtEnv a₁ =
      w2i_TryDecryptCliEnvGen C S s4Env RecvBytesEnv fmtEnv a₂ := by
  unfold w2i_TryDecryptCliEnvGen
  rw [hst, hG]
  cases Mut.exec TripleRatchet.fromSessionState a₂.st with
  | mk res st1 =>
    cases res with
    | error _ => rfl
    | ok tr0 =>
      dsimp only
      rw [w2i_fromS2GenEnv_ghost_congr_gen C S s4Env RecvBytesEnv fmtEnv
        (tryDecryptEnvArgsToGhost a₁) (tryDecryptEnvArgsToGhost a₂)
        hs4 hrem_b hrem_d hloc_b hloc_d hmsg hmt hrest]

/-- `TryDecryptCliEnvOfPure` is invariant under changes to `a.msgG` and address pointer/capacity
ghosts. -/
theorem w2i_tryDecryptCliEnvOfPure_congr
    (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a₁ a₂ : TryDecryptEnvArgs)
    (hG : a₁.G = a₂.G) (hst : a₁.st = a₂.st)
    (hrem_b : a₁.rem.name.bytes = a₂.rem.name.bytes) (hrem_d : a₁.rem.device = a₂.rem.device)
    (hloc_b : a₁.loc.name.bytes = a₂.loc.name.bytes) (hloc_d : a₁.loc.device = a₂.loc.device)
    (hmsg : a₁.msg = a₂.msg) (hmt : a₁.msgType = a₂.msgType) (hrest : a₁.rest = a₂.rest) :
    TryDecryptCliEnvOfPure C S fmtWriteEnv RecvBytesEnv fmtEnv a₁ =
      TryDecryptCliEnvOfPure C S fmtWriteEnv RecvBytesEnv fmtEnv a₂ := by
  have hs4 :
      tryDecryptCmkSeg4Env fmtWriteEnv (tryDecryptEnvArgsToGhost a₁) =
        tryDecryptCmkSeg4Env fmtWriteEnv (tryDecryptEnvArgsToGhost a₂) := by
    funext trG tr ck
    unfold tryDecryptCmkSeg4Env
    dsimp only [tryDecryptEnvArgsToGhost]
    rw [hmsg]
  exact w2i_tryDecryptCliEnvGen_congr C S (tryDecryptCmkSeg4Env fmtWriteEnv)
    RecvBytesEnv fmtEnv a₁ a₂ hs4 hG hst hrem_b hrem_d hloc_b hloc_d hmsg hmt hrest

/-- `r3a` ghost congruence for `CliDecryptSignalSlotEnv` at any `msgG`-insensitive `TdEnv`. -/
theorem w2i_cliDecryptSignalSlotEnv_ofTd_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (TdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (hTd : ∀ (a₁ a₂ : TryDecryptEnvArgs),
      a₁.G = a₂.G → a₁.st = a₂.st →
      a₁.rem.name.bytes = a₂.rem.name.bytes → a₁.rem.device = a₂.rem.device →
      a₁.loc.name.bytes = a₂.loc.name.bytes → a₁.loc.device = a₂.loc.device →
      a₁.msg = a₂.msg → a₁.msgType = a₂.msgType → a₁.rest = a₂.rest →
      TdEnv a₁ = TdEnv a₂)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets TdEnv
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets TdEnv
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost0 gc peerV meG m) := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let x₁ := r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m
  let x₂ := r3aDecSigGhost0 gc peerV meG m
  let z₁ := toDecryptGhost x₁
  let z₂ := toDecryptGhost x₂
  let kit₁ := decSessKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
  let kit₂ := decSessKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
  let ke₁ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ke₂ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ikit₁ := decIdKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
  let ikit₂ := decIdKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
  let ike₁ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ike₂ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  have hload_step :
      LoadPollStepEnv kit₁ ke₁ st0 z₁.rem.val = LoadPollStepEnv kit₂ ke₂ st0 z₂.rem.val :=
    w2i_seqEnv_congr rfl rfl
  have htrust_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
          ikit₁ ike₁ ist0 z₁.rem.val k .receiving =
        LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
          ikit₂ ike₂ ist0 z₂.rem.val k .receiving :=
    fun _ => w2i_seqEnv_congr rfl (w2i_seqEnv_congr rfl rfl)
  have hsave_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
          ikit₁ ike₁ (ikit₁.trustUpdate ist0 z₁.rem.val k .receiving (.ok true)) z₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
          ikit₂ ike₂ (ikit₂.trustUpdate ist0 z₂.rem.val k .receiving (.ok true)) z₂.rem.val k :=
    fun _ => w2i_seqEnv_congr rfl (w2i_seqEnv_congr rfl rfl)
  have hstore_call : ∀ rec',
      FromStoreCallEnv kit₁ ke₁ st0 z₁.rem.val rec' =
        FromStoreCallEnv kit₂ ke₂ st0 z₂.rem.val rec' :=
    fun _ => w2i_seqEnv_congr (w2i_seqEnv_congr rfl (w2i_seqEnv_congr rfl rfl)) rfl
  have hsc : StringCloneEnv z₁.rem.name = StringCloneEnv z₂.rem.name := by
    have hb : z₁.rem.name.bytes = z₂.rem.name.bytes := rfl
    funext evs
    dsimp [StringCloneEnv]
    rw [hb]
  have htf : FromTrustedFalseEnv z₁ = FromTrustedFalseEnv z₂ :=
    w2i_seqEnv_congr hsc rfl
  have htt : ∀ rec' k,
      FromTrustedTrueEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
        FromTrustedTrueEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
    fun rec' k =>
      w2i_seqEnv_congr (hsave_step k)
        (funext fun evs => w2i_or_congr rfl (congrFun (hstore_call rec') evs))
  have hkr : ∀ rec' k,
      FromKeyReadyEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
        FromKeyReadyEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
    fun rec' k =>
      w2i_seqEnv_congr (htrust_step k)
        (funext fun evs =>
          w2i_or_congr rfl (w2i_or_congr (congrFun htf evs) (congrFun (htt rec' k) evs)))
  have hdecRec : ∀ rec,
      decryptRecord P.C (pqxdhSpqrModel P) uuidTryParse z₁ rec =
        decryptRecord P.C (pqxdhSpqrModel P) uuidTryParse z₂ rec := by
    intro rec
    unfold decryptRecord
    rfl
  have hps : ∀ rec,
      FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec =
        FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec :=
    fun rec => funext fun evs =>
      w2i_or_congr rfl
        (w2i_exists_congr fun pt =>
          w2i_exists_congr fun rec' =>
            w2i_exists_congr fun _ =>
              w2i_exists_congr fun k =>
                w2i_and_congr (congrArg (· = .ok (pt, rec')) (hdecRec rec))
                  (w2i_and_congr rfl
                    (w2i_and_congr rfl (congrFun (hkr rec' k) evs))))
  have hrd : ∀ G ses_st,
      RecordDecryptEnv TdEnv (recGhostOf z₁ 0#64 G ses_st) =
        RecordDecryptEnv TdEnv (recGhostOf z₂ 0#64 G ses_st) := by
    intro G ses_st
    funext evs
    unfold RecordDecryptEnv FromVEnv
    have htd : ∀ G₁,
        TdEnv (recordTryDecryptEnvArgs (recGhostOf z₁ 0#64 G ses_st) G₁) =
          TdEnv (recordTryDecryptEnvArgs (recGhostOf z₂ 0#64 G ses_st) G₁) := by
      intro G₁
      exact hTd _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hcond₁ : ((recGhostOf z₁ 0#64 G ses_st).st.version.toNat =
        (recGhostOf z₁ 0#64 G ses_st).msg.messageVersion.toNat) =
      (ses_st.version.toNat = m.messageVersion.toNat) := rfl
    have hcond₂ : ((recGhostOf z₂ 0#64 G ses_st).st.version.toNat =
        (recGhostOf z₂ 0#64 G ses_st).msg.messageVersion.toNat) =
      (ses_st.version.toNat = m.messageVersion.toNat) := rfl
    by_cases hv : ses_st.version.toNat = m.messageVersion.toNat
    · simp only [hcond₁, hcond₂, hv, ↓reduceIte]
      exact w2i_exists_congr fun G₁ =>
        w2i_and_congr rfl (congrFun (w2i_seqEnv_congr rfl (w2i_seqEnv_congr (htd G₁) rfl)) evs)
    · simp only [hcond₁, hcond₂, hv, ↓reduceIte]
      rfl
  have hrs : ∀ rec G ses_st,
      FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec G ses_st =
        FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec G ses_st :=
    fun rec G ses_st => w2i_seqEnv_congr (hrd G ses_st) (hps rec)
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 scopeKit z₁ =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 scopeKit z₂ :=
    w2i_seqEnv_congr rfl
      (funext fun evs =>
        w2i_or_congr rfl
          (w2i_or_congr (congrFun htf evs)
            (w2i_or_congr rfl
              (w2i_exists_congr fun rec =>
                w2i_exists_congr fun ses =>
                  w2i_exists_congr fun G =>
                    w2i_and_congr rfl
                      (w2i_and_congr rfl
                        (w2i_and_congr rfl
                          (congrFun (hrs rec G ses.state) evs)))))))
  funext evs
  exact congrFun (w2i_seqEnv_congr hload_step hlp) evs

/-- Segment-4-parametric `r3a` ghost congruence for `w2i_cliDecryptSignalSlotEnvGuardedOf`. -/
theorem w2i_cliDecryptSignalSlotEnvGuardedOf_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (hs4 : ∀ (x₁ x₂ : TryDecryptGhost), x₁.msg = x₂.msg → s4Env x₁ = s4Env x₂)
    (A : RustCliAllocBudget M)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env A cliRunBudgets
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env A cliRunBudgets
        (r3aDecSigGhost0 gc peerV meG m) := by
  funext evs
  unfold w2i_cliDecryptSignalSlotEnvGuardedOf
  have hinner := congrFun
    (w2i_cliDecryptSignalSlotEnv_ofTd_r3a_congr W A
      (w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
        (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
      (fun a₁ a₂ hG hst hrb hrd hlb hld hmsg hmt hrest =>
        w2i_tryDecryptCliEnvGen_congr W.C (spqrV1 W.C.F W.Q.K) s4Env
          (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv a₁ a₂
          (hs4 _ _ hmsg) hG hst hrb hrd hlb hld hmsg hmt hrest)
      gc fsp w peerV meG msgG m) evs
  have hF : (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m).F =
      (r3aDecSigGhost0 gc peerV meG m).F := rfl
  have hp : (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m).peer.val =
      (r3aDecSigGhost0 gc peerV meG m).peer.val := rfl
  rw [hF, hp, hinner]

theorem w2i_cliDecryptSignalSlotEnv_linked_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets (TryDecryptCliLinkedEnv W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets (TryDecryptCliLinkedEnv W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (r3aDecSigGhost0 gc peerV meG m) :=
  w2i_cliDecryptSignalSlotEnv_ofTd_r3a_congr W A (TryDecryptCliLinkedEnv W.C W.Q.K)
    (fun a₁ a₂ hG hst hrb hrd hlb hld hmsg hmt hrest =>
      w2i_tryDecryptCliEnvOfPure_congr W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv
        (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv a₁ a₂
        hG hst hrb hrd hlb hld hmsg hmt hrest)
    gc fsp w peerV meG msgG m

/-- `r3a` ghost congruence for `w2i_cliDecryptSignalSlotEnvGuarded`. -/
theorem w2i_cliDecryptSignalSlotEnvGuarded_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    w2i_cliDecryptSignalSlotEnvGuarded W A cliRunBudgets
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      w2i_cliDecryptSignalSlotEnvGuarded W A cliRunBudgets
        (r3aDecSigGhost0 gc peerV meG m) :=
  w2i_cliDecryptSignalSlotEnvGuardedOf_r3a_congr W (tryDecryptCmkSeg4Env FmtWriteEnv)
    (fun _ _ hmsg => by
      funext trG tr ck
      unfold tryDecryptCmkSeg4Env
      rw [hmsg])
    A gc fsp w peerV meG msgG m

/-! ## Slot-`463` Guard Upgrade (`TopStateTight` to `PeerSpqrStateTight640`) -/

/-- `TopStateTight`-guarded `spqr::recv` byte-slice allocation envelope. -/
def w2i_SpqrRecvTopStateGuardedBytesEnv (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight F K stBs →
    SpqrRecvC07C09aBytesEnv F K stBs msgBs evs

noncomputable def w2i_TryDecryptTopStateGuardedEnvOf (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
    (w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv

/-- `TopStateTight`-guarded `TryDecryptCliEnvOfPure` envelope. -/
noncomputable def w2i_TryDecryptTopStateGuardedEnv (W : CliHooks) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliEnvOfPure W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv
    (w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv

private theorem w2i_fromSessionState_ok_pqrState {PQ : Type} [Inhabited PQ]
    {s s1 : SessionState PQ} {tr0 : TripleRatchet PQ}
    (h : Mut.exec TripleRatchet.fromSessionState s = (.ok tr0, s1)) :
    tr0.pqrState = s.pqRatchetState := by
  unfold Mut.exec TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at h
  rcases s with ⟨_, _, _ | rem, _, _, _, _, _, _⟩
  · cases h
  · cases h; rfl

private theorem w2i_pqRecvEnv_topStateGuarded_eq (W : CliHooks)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight W.C.F W.Q.K tr.pqrState) :
    PqRecvEnv (spqrV1 W.C.F W.Q.K) (w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K)
        FormatInnerEnv x tr =
      PqRecvEnv (spqrV1 W.C.F W.Q.K) (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K)
        FormatInnerEnv x tr := by
  have hrecv :
      w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K tr.pqrState x.msg.pqRatchet =
        SpqrRecvC07C09aBytesEnv W.C.F W.Q.K tr.pqrState x.msg.pqRatchet := by
    funext evs
    exact propext ⟨fun h => h hTop, fun h _ => h⟩
  unfold PqRecvEnv
  rw [hrecv]

private theorem w2i_tryDecryptTopStateGuardedEnvOf_eq_linked_of_top (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (a : TryDecryptEnvArgs)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState) :
    w2i_TryDecryptTopStateGuardedEnvOf W s4Env a =
      w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
        (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv a := by
  unfold w2i_TryDecryptTopStateGuardedEnvOf w2i_TryDecryptCliEnvGen
  cases hfrom : Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ => rfl
    | ok tr0 =>
      dsimp only
      apply congrArg (SeqEnv FreeOnlyEvs)
      let x := tryDecryptEnvArgsToGhost a
      let S := spqrV1 W.C.F W.Q.K
      have hTop0 : TopStateTight W.C.F W.Q.K tr0.pqrState :=
        (w2i_fromSessionState_ok_pqrState hfrom).symm ▸ hTop
      have hs5g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
          (mkg : MessageKeyGenerator),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg =
            FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg := by
        intro trG tr mkg hT
        unfold FromS5GenEnv
        rw [w2i_pqRecvEnv_topStateGuarded_eq W x tr hT]
      have hs4g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck =
            FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck := by
        intro trG tr ck hT
        unfold FromS4GenEnv
        cases Mut.exec
            (RatchetState.consumeMessageKey W.C.F x.msg.senderRatchetKey ck x.msg.counter x.msgType)
            tr.ratchet with
        | mk r4 r2 =>
          cases r4 with
          | error _ => rfl
          | ok mkg =>
            dsimp only
            exact congrArg (SeqEnv (s4Env x trG tr ck))
              (hs5g trG { tr with ratchet := r2 } mkg hT)
      have hs3g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 =
            FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 := by
        intro trG tr hT
        unfold FromS3GenEnv
        cases Mut.exec (RatchetState.dhRatchetStep W.C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | mk r3 r1 =>
          cases r3 with
          | error _ => rfl
          | ok ck =>
            dsimp only
            exact congrArg (SeqEnv (s3DefaultEnv W.C x trG tr))
              (hs4g _ { tr with ratchet := r1 } ck hT)
      unfold FromS2GenEnv
      cases tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error _ => rfl
      | ok cko =>
        cases cko with
        | some ck =>
          dsimp only
          exact hs4g (s1InitTrGhost a.G) tr0 ck hTop0
        | none =>
          dsimp only
          exact hs3g (s1InitTrGhost a.G) tr0 hTop0

theorem w2i_cliDecryptSignalSlotEnv_topStateGuardedOf_eq_linked_of_peer [LibsignalPlacement]
    {M : AllocCostModel} (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (x : DecSigGhost)
    (hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2i_TryDecryptTopStateGuardedEnvOf W s4Env)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
        (w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
          (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let z := toDecryptGhost x
  let kit := decSessKitPlaced A.repAlloc x.F x.peer B
  let ke := decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer
  let ikit := decIdKitPlaced A.repAlloc x.F x.peer B
  let ike := decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  let TdLinked := w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
    (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv
  have hrd : ∀ G (ses_st : SessionState (List (BitVec 8))),
      TopStateTight W.C.F W.Q.K ses_st.pqRatchetState →
      RecordDecryptEnv (w2i_TryDecryptTopStateGuardedEnvOf W s4Env) (recGhostOf z 0#64 G ses_st) =
        RecordDecryptEnv TdLinked (recGhostOf z 0#64 G ses_st) := by
    intro G ses_st hTop
    funext evs
    unfold RecordDecryptEnv FromVEnv
    by_cases hv : (recGhostOf z 0#64 G ses_st).st.version.toNat =
        (recGhostOf z 0#64 G ses_st).msg.messageVersion.toNat
    · simp only [hv, ↓reduceIte]
      refine w2i_exists_congr fun G₁ => ?_
      have htd := w2i_tryDecryptTopStateGuardedEnvOf_eq_linked_of_top W s4Env
        (recordTryDecryptEnvArgs (recGhostOf z 0#64 G ses_st) G₁) hTop
      exact w2i_and_congr rfl (congrFun (w2i_seqEnv_congr rfl (w2i_seqEnv_congr htd rfl)) evs)
    · simp only [hv, ↓reduceIte]
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (w2i_TryDecryptTopStateGuardedEnvOf W s4Env) kit ke st0 ikit ike ist0 scopeKit z =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse
          TdLinked kit ke st0 ikit ike ist0 scopeKit z := by
    refine w2i_seqEnv_congr rfl (funext fun evs => ?_)
    refine w2i_or_congr rfl (w2i_or_congr rfl (w2i_or_congr rfl ?_))
    refine w2i_exists_congr fun rec =>
      w2i_exists_congr fun ses =>
        w2i_exists_congr fun G => propext ⟨?_, ?_⟩
    · rintro ⟨hScAt, hcur, hGV, hrs⟩
      have hTop : TopStateTight W.C.F W.Q.K ses.state.pqRatchetState := by
        obtain ⟨bs, hbs, hla⟩ := hScAt.2
        have hlr : loadRec scopeKit x.F x.peer.val = .ok (some rec) :=
          (loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)).symm
        have hPeer' := hPeer
        unfold PeerSpqrStateTight640 at hPeer'
        rw [hlr] at hPeer'
        exact hPeer' ses hcur
      have hrs_eq :
          FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              (w2i_TryDecryptTopStateGuardedEnvOf W s4Env) kit ke st0 ikit ike ist0 z rec G ses.state =
            FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              TdLinked kit ke st0 ikit ike ist0 z rec G ses.state :=
        w2i_seqEnv_congr (hrd G ses.state hTop) rfl
      exact ⟨hScAt, hcur, hGV, Eq.mp (congrFun hrs_eq evs) hrs⟩
    · rintro ⟨hScAt, hcur, hGV, hrs⟩
      have hTop : TopStateTight W.C.F W.Q.K ses.state.pqRatchetState := by
        obtain ⟨bs, hbs, hla⟩ := hScAt.2
        have hlr : loadRec scopeKit x.F x.peer.val = .ok (some rec) :=
          (loadRec_unique encodeInjOn_deserializeScopeP_Q (hbs ▸ hla)).symm
        have hPeer' := hPeer
        unfold PeerSpqrStateTight640 at hPeer'
        rw [hlr] at hPeer'
        exact hPeer' ses hcur
      have hrs_eq :
          FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              (w2i_TryDecryptTopStateGuardedEnvOf W s4Env) kit ke st0 ikit ike ist0 z rec G ses.state =
            FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
              TdLinked kit ke st0 ikit ike ist0 z rec G ses.state :=
        w2i_seqEnv_congr (hrd G ses.state hTop) rfl
      exact ⟨hScAt, hcur, hGV, Eq.mpr (congrFun hrs_eq evs) hrs⟩
  unfold CliDecryptSignalSlotEnv WithStoresDecEnv
  exact w2i_seqEnv_congr rfl hlp

/-- Under `PeerSpqrStateTight640`, the `TopStateTight`-guarded `CliDecryptSignalSlotEnv` agrees
pointwise with `CliDecryptSignalSlotEnv` at `TryDecryptCliLinkedEnv`. -/
theorem w2i_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer [LibsignalPlacement]
    {M : AllocCostModel} (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets)
    (x : DecSigGhost)
    (hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2i_TryDecryptTopStateGuardedEnv W)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (TryDecryptCliLinkedEnv W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x :=
  w2i_cliDecryptSignalSlotEnv_topStateGuardedOf_eq_linked_of_peer W
    (tryDecryptCmkSeg4Env FmtWriteEnv) A B x hPeer

/-- Lifts `decSigSlotSpecFrozenPlaced` from `w2i_TryDecryptTopStateGuardedEnvOf` to
`w2i_cliDecryptSignalSlotEnvGuardedOf` using `w2i_not_fitsEnv_top` on the negated guard branch. -/
theorem w2i_decSigSlotSpecFrozenPlaced_mono_guardedOf [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2i_TryDecryptTopStateGuardedEnvOf W s4Env)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B))
        S stk)) :
    subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim (w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env A B) S stk) := by
  refine subroutine_ok_mono hok (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
    · have henv :
          w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env A B x =
            CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2i_TryDecryptTopStateGuardedEnvOf W s4Env)
              (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
              (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
        have h1 :
            w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env A B x =
              CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
                (w2i_TryDecryptCliEnvGen W.C (spqrV1 W.C.F W.Q.K) s4Env
                  (SpqrRecvC07C09aBytesEnv W.C.F W.Q.K) FormatInnerEnv)
                (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
                (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
          funext evs
          exact propext ⟨fun f => f hPeer, fun hp _ => hp⟩
        exact h1.trans
          (w2i_cliDecryptSignalSlotEnv_topStateGuardedOf_eq_linked_of_peer W s4Env A B x hPeer).symm
      dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
        decSigSlotSpecBasePlaced] at hpre ⊢
      rwa [henv] at hpre
    · dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
        decSigSlotSpecBasePlaced] at hpre
      let H_sp : SepProp :=
        slotFramePlaced A lim st x.toSlotCtx s0 ∗ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗ R
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x0 = x.msgA ∧ s0.readReg64 .x1 = x.peerA ∧ s0.readReg64 .x2 = x.meA ∧
            s0.readReg64 .x3 = x.stores + 0xf0#64 ∧ s0.readReg64 .x4 = sessVtPlaced ∧
            s0.readReg64 .x5 = x.stores ∧ s0.readReg64 .x6 = idVtPlaced ∧
            s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
            stk ≤ s0.sp.toNat ∧ FitsEnv M lim st (w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env A B x)⌝ ∗
          H_sp := by
        dsimp only [H_sp]
        exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
      rw [satisfies_pure_sepConj] at hpre'
      have hfit := hpre'.1.2.2.2.2.2.2.2.2.2.2.2
      have htop : FitsEnv M lim st (fun _ => True) :=
        FitsEnv.mono (fun _ _ h => False.elim (hPeer h)) hfit
      exact False.elim (w2i_not_fitsEnv_top htop)
  · dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
      decSigSlotSpecBasePlaced] at hpost ⊢
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_mono fun evs =>
        Entails.sepExists_mono fun g' =>
          Entails.sepExists_mono fun e => ?_)) hpost
    apply Entails.pure_left
    rintro ⟨hevs, htr, hout⟩
    refine Entails.pure_right ⟨?_, htr, hout⟩ (Entails.refl _)
    intro hPeer
    exact Eq.mp
      (congrFun
        (w2i_cliDecryptSignalSlotEnv_topStateGuardedOf_eq_linked_of_peer W s4Env A B x hPeer) evs)
      hevs

/-- Specialization of `w2i_decSigSlotSpecFrozenPlaced_mono_guardedOf` to
`w2i_cliDecryptSignalSlotEnvGuarded`. -/
theorem w2i_decSigSlotSpecFrozenPlaced_mono_guarded [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (W : CliHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w2i_TryDecryptTopStateGuardedEnv W)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B))
        S stk)) :
    subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim (w2i_cliDecryptSignalSlotEnvGuarded W A B) S stk) :=
  w2i_decSigSlotSpecFrozenPlaced_mono_guardedOf W (tryDecryptCmkSeg4Env FmtWriteEnv) A lim B S stk hok

/-- Lifts `InnerDecryptFrozenPlacedOk` at `w2i_TryDecryptTopStateGuardedEnvOf` to the `OkPlaced`
slot contract on block `463` (`lsProg_579`). -/
theorem w2i_hole3_w2_inner_guardedOf_of_inner
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (γ : GhostName) (tp : BitVec 64)
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hInner :
      letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
      InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliRunBudgets
        (w2i_TryDecryptTopStateGuardedEnvOf W s4Env)
        (decBinarySessKitPlacedBudgetFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc cliRunBudgets)) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2i_cliDecryptSignalSlotEnvGuardedOf W s4Env
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  intro stk hstk hstk64
  dsimp only [mkSlot] at hstk ⊢
  have hstk' : cliDecryptSignalNeed cliRunBudgets ≤ stk := hstk
  have hSlot :
      subroutine_ok (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (lsmpl.base 463)
        (decSigSlotSpecFrozenPlaced A cliBudgetLimits
          (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets
            (w2i_TryDecryptTopStateGuardedEnvOf W s4Env)
            (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
            (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets))
          (cliRunSemD2c_placed X W) stk) :=
    cliDecryptSignal_slot_full_placed (i := 579)
      mmpl ghFixed W A cliBudgetLimits cliRunBudgets (cliRunSemD2c_placed X W) scopeIn
      (w2i_TryDecryptTopStateGuardedEnvOf W s4Env)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hHooks.runHooks
      (w2SessVt_placed_ok A.repAlloc cliRunBudgets h547)
      (w2IdVt_placed_ok A.repAlloc cliRunBudgets h547)
      hInner
      encodeInjOn_deserializeScopeP_Q (fun _ h => h)
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩)
      stk hstk' hstk64
  exact w2i_decSigSlotSpecFrozenPlaced_mono_guardedOf W s4Env A cliBudgetLimits cliRunBudgets
    (cliRunSemD2c_placed X W) stk hSlot

/-! ## Per-State SPQR Codec Leaf Guards and `hole3_w2_inner` Producers -/

/-- Per-state input guard `TopStateTight F K stBytes` for `spqr::decode_state` (block `325`). -/
def w2i_DecodeStateGuard (F : ShaCompress) (K : MlKem) (stBytes : Bytes) : Prop :=
  LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight F K stBytes

/-- Per-state input guard for `<States>::from_pb` (block `333`): `pb = st.into_pb` for some
`BOkTight st`, with `rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb`. -/
def w2i_FromPbStateGuard (F : ShaCompress) (pb : V1State) : Prop :=
  (∃ st : States spqrPolyApi (spqrAuthApi F), BOkTight st ∧ pb = st.into_pb) ∧
    rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb

/-- Per-state input guard for `<States>::into_pb` (block `334`): `BOkTight st1` and
`rawV1State st1.into_pb ≤ 46880`. -/
def w2i_IntoPbStateGuard {F : ShaCompress} (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  BOkTight st1 ∧ rawV1State st1.into_pb ≤ 46880

def w2i_DecodeStateGuardedEnv (F : ShaCompress) (K : MlKem)
    (g : DecodeStateGhost) (evs : List AllocEvent) : Prop :=
  w2i_DecodeStateGuard F K g.st.bytes → DecodeStateTightEnv evs

def w2i_StatesFromPbGuardedEnv (F : ShaCompress)
    (pb : V1State) (evs : List AllocEvent) : Prop :=
  w2i_FromPbStateGuard F pb → StatesFromPbTightEnv evs

def w2i_StatesIntoPbGuardedEnv {F : ShaCompress}
    (g : StatesIntoPbGhost F) (evs : List AllocEvent) : Prop :=
  w2i_IntoPbStateGuard g.st → StatesIntoPbTightEnv evs

/-- Extracts `w2i_FromPbStateGuard F pb` on the V1 inner-state branch of `spqr::recv` from
`TopStateTight F K stBytes`. -/
theorem w2i_topStateTight_fromPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb)) :
    w2i_FromPbStateGuard F pb := by
  have hprops := (topStateTight_decode_props hTop hdec).2.2.1 pb hinner
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, st, _, _, _, vn?, ch?, _, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hinner
  cases hinner
  exact ⟨⟨st, hw.hbok, rfl⟩, hprops⟩

/-- Extracts `w2i_IntoPbStateGuard v.state` on the post-`States.recv` branch of `spqr::recv` from
`TopStateTight F K stBytes`. -/
theorem w2i_topStateTight_intoPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb))
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    {sckaMsg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hrecv : States.recv K st0 sckaMsg = .ok v) :
    w2i_IntoPbStateGuard v.state := by
  obtain ⟨⟨st, hbok, rfl⟩, -⟩ := w2i_topStateTight_fromPbStateGuard hTop hdec hinner
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hbok.1
  rw [hcodec] at hfrom
  have hst0 := Except.ok.inj hfrom; subst hst0
  rcases v with ⟨key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st
    · exact st_bRecvCt_tight F K hek hbok hrecv
    · exact st_bRecvEk_tight F K hek hbok hrecv
  exact ⟨hbok1, st_bSize_tight F st1 hbok1⟩

private theorem w2i_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hpre | ⟨evs₁, evs₂, rfl, he1, he2⟩
  · exact Or.inl (h1 evs hpre)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ he1, h2 evs₂ he2⟩

/-- Under `TopStateTight` and per-state guarded inclusions for `FromPbEnv` and `IntoPbEnv`,
`SpqrRecvTightLinkedEnv` refines into `SpqrRecvC07C09aTightLinkedEnv`. -/
theorem w2i_spqrRecvTightLinkedEnv_imp_c07c09a_of_topStateTight
    {F : ShaCompress} {K : MlKem}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hFromPb_sub : ∀ pb evs, w2i_FromPbStateGuard F pb → FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ g evs, w2i_IntoPbStateGuard g.st → IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    {stBytes : Bytes} (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : SpqrRecvTightLinkedEnv F K (fun _ => DecodeStateTightEnv) FromPbEnv IntoPbEnv
      StatesRecvProtoEnv stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvC07C09aTightLinkedEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  rcases h with ⟨hTight, hLink⟩
  refine ⟨?_, hLink⟩
  rcases hTight with hfree | hseq
  · exact Or.inl hfree
  · refine Or.inr (w2i_seqEnv_mono (fun _ hd => hd) (fun evsAfterDec hafter => ?_) hseq)
    rcases hafter with hfree1 | ⟨hdec, hbr⟩
    · exact Or.inl hfree1
    · refine Or.inr ⟨hdec, ?_⟩
      rcases hbr with hless | hgt | ⟨hinner, heq⟩
      · exact Or.inl hless
      · exact Or.inr (Or.inl hgt)
      · refine Or.inr (Or.inr ⟨hinner, ?_⟩)
        have hPbG : w2i_FromPbStateGuard F pb :=
          w2i_topStateTight_fromPbStateGuard hTop hdec hinner
        refine w2i_seqEnv_mono (fun _ hf => hf) (fun evsAfterMd hmd => ?_) heq
        rcases hmd with hfree2 | hfromSeq
        · exact Or.inl hfree2
        · refine Or.inr (w2i_seqEnv_mono (fun evsF hf => hFromPb_sub pb evsF hPbG hf)
            (fun evsAfterFrom haf => ?_) hfromSeq)
          rcases haf with hfree3 | ⟨hfrom, hrecvSeq⟩
          · exact Or.inl hfree3
          · refine Or.inr ⟨hfrom, w2i_seqEnv_mono (fun _ hr => hr) (fun evsAfterRecv har => ?_) hrecvSeq⟩
            rcases har with hfree4 | ⟨hrecv, hxS, hv1c⟩
            · exact Or.inl hfree4
            · refine Or.inr ⟨hrecv, hxS, ?_⟩
              have hIntoG : w2i_IntoPbStateGuard xSInto.st :=
                hxS.symm ▸ w2i_topStateTight_intoPbStateGuard hTop hdec hinner hfrom hrecv
              refine w2i_seqEnv_mono (fun _ hc => hc) (fun evs1 he1 => ?_) hv1c
              rcases he1 with hfree5 | ⟨hc1, hc2, haddSeq⟩
              · exact Or.inl hfree5
              · refine Or.inr ⟨hc1, hc2, w2i_seqEnv_mono (fun _ ha => ha) (fun evs2 he2 => ?_) haddSeq⟩
                rcases he2 with hfree6 | hrkSeq
                · exact Or.inl hfree6
                · refine Or.inr (w2i_seqEnv_mono (fun _ hrk => hrk) (fun evs3 he3 => ?_) hrkSeq)
                  rcases he3 with hfree7 | ⟨hrkOk, hintoSeq⟩
                  · exact Or.inl hfree7
                  · exact Or.inr ⟨hrkOk,
                      w2i_seqEnv_mono (fun evsI hi => hIntoPb_sub xSInto evsI hIntoG hi)
                        (fun _ ht => ht) hintoSeq⟩

private theorem w2i_trTrapExternsPlaced_isPanic
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        some Rust.panicked := by
  intro sym hsym
  have hp := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at hp
  have hne : sym ≠ lsRngFillSym := by
    intro heq
    subst heq
    have hnone := cliExternsPlaced_rngFill mmpl gh W
    rw [hnone] at hp
    cases hp
  have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
  simp only [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq, Bool.false_eq_true, ↓reduceIte]
  exact hp.symm

/-- Derives the block-`329` (`spqr::recv`) seam at `w2i_SpqrRecvTopStateGuardedBytesEnv` from
`SpqrRecvPlacedContractsOfEnv` at per-state guarded codec leaf envelopes. -/
theorem w2i_spqrRecv_topStateGuarded_seam_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hDecPre_sub : ∀ g evs, w2i_DecodeStateGuard W.C.F W.Q.K g.st.bytes →
      DecodePreEnv g evs → DecodeStateTightEnv evs)
    (hDecPost_sub : ∀ g evs, w2i_DecodeStateGuard W.C.F W.Q.K g.st.bytes →
      DecodePostEnv g evs → DecodeStateTightEnv evs)
    (hFromPb_sub : ∀ pb evs, w2i_FromPbStateGuard W.C.F pb →
      FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, w2i_IntoPbStateGuard g.st →
      IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      DecodePreEnv DecodePostEnv
      (InitInnerEnv W.C.F)
      FromPbEnv
      (fun g => StatesRecvProtoEnv g.self g.msg)
      IntoPbEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes))) := by
  refine spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv
      (fun (st msg : VecArg) => w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (w2i_trTrapExternsPlaced_isPanic mmpl gh W)
      hRecvC
      (fun st _ _ _ _ _ => spqrRecvC07C09aTightLinkedEnv_nil_exists W.C.F W.Q.K st.bytes)
      (fun st msg s0 st_cost _ _ _ _ hfit => ?_))
  by_cases hTop : TopStateTight W.C.F W.Q.K st.bytes
  · refine spqrRecvBranchHyps_tightLinked
      (DecodeStateEnv' := fun _ => DecodeStateTightEnv)
      (StatesFromPbEnv' := FromPbEnv)
      (StatesIntoPbEnv' := IntoPbEnv)
      (StatesRecvEnv' := StatesRecvProtoEnv)
      st msg s0 st_cost
      (fun evs hpre => hDecPre_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpre)
      (fun evs hpost => hDecPost_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpost)
      (fun _ _ h => h)
      (fun _ _ _ h => h)
      (fun _ _ h => h)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =>
        FitsEnv.mono
          (fun evs hevs _ =>
            ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
              w2i_spqrRecvTightLinkedEnv_imp_c07c09a_of_topStateTight
                hFromPb_sub hIntoPb_sub hTop hevs⟩)
          hfit)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs _ =>
        ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
          w2i_spqrRecvTightLinkedEnv_imp_c07c09a_of_topStateTight
            hFromPb_sub hIntoPb_sub hTop hevs⟩)
  · exact False.elim
      (w2i_not_fitsEnv_top (FitsEnv.mono (fun _ _ h => False.elim (hTop h)) hfit))

/-- Substitutes per-state guarded `decodeState_ok` (block `325`), `statesFromPb_ok` (block `333`),
and `statesIntoPb_ok` (block `334`) into `SpqrRecvPlacedContractsOfEnv` and lifts
`SpqrV1PlacedSeamsOfEnv` to `w2i_SpqrRecvTopStateGuardedBytesEnv`. -/
theorem w2i_spqrV1PlacedSeams_topStateGuarded_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {OldDecPre OldDecPost : DecodeStateGhost → List AllocEvent → Prop}
    {OldFromPb : V1State → List AllocEvent → Prop}
    {OldIntoPb : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hBase : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv PrevRecvEnv SendEnv)
    (hRecvBase : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      OldDecPre OldDecPost (InitInnerEnv W.C.F) OldFromPb
      (fun g => StatesRecvProtoEnv g.self g.msg) OldIntoPb
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (hDec : subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv H_inner A lim DecodePreEnv DecodePostEnv)))
    (hFromPb : subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim W.C.F FromPbEnv)))
    (hIntoPb : subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim W.C.F IntoPbEnv)))
    (hDecPre_sub : ∀ g evs, w2i_DecodeStateGuard W.C.F W.Q.K g.st.bytes →
      DecodePreEnv g evs → DecodeStateTightEnv evs)
    (hDecPost_sub : ∀ g evs, w2i_DecodeStateGuard W.C.F W.Q.K g.st.bytes →
      DecodePostEnv g evs → DecodeStateTightEnv evs)
    (hFromPb_sub : ∀ pb evs, w2i_FromPbStateGuard W.C.F pb →
      FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, w2i_IntoPbStateGuard g.st →
      IntoPbEnv g evs → StatesIntoPbTightEnv evs) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => w2i_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes) SendEnv where
  spqrInitialState := hBase.spqrInitialState
  spqrRecv := w2i_spqrRecv_topStateGuarded_seam_of_contracts mmpl gh W
    hDecPre_sub hDecPost_sub hFromPb_sub hIntoPb_sub
    { dealloc_ok := hRecvBase.dealloc_ok
      memcpy_ok := hRecvBase.memcpy_ok
      dropEpochSlice_ok := hRecvBase.dropEpochSlice_ok
      dropOptProtoInnerState_ok := hRecvBase.dropOptProtoInnerState_ok
      dropOptProtoChain_ok := hRecvBase.dropOptProtoChain_ok
      dropChain_ok := hRecvBase.dropChain_ok
      dropPqRatchetState_ok := hRecvBase.dropPqRatchetState_ok
      dropStates_ok := hRecvBase.dropStates_ok
      decodeState_ok := hDec
      initInner_ok := hRecvBase.initInner_ok
      chainFrom_ok := hRecvBase.chainFrom_ok
      chainFromPb_ok := hRecvBase.chainFromPb_ok
      chainNew_ok := hRecvBase.chainNew_ok
      chainAddEpoch_ok := hRecvBase.chainAddEpoch_ok
      chainRecvKey_ok := hRecvBase.chainRecvKey_ok
      chainIntoPb_ok := hRecvBase.chainIntoPb_ok
      messageDeserialize_ok := hRecvBase.messageDeserialize_ok
      statesFromPb_ok := hFromPb
      statesRecv_ok := hRecvBase.statesRecv_ok
      statesIntoPb_ok := hIntoPb
      encodeToVec_ok := hRecvBase.encodeToVec_ok
      h_inner_eq := hRecvBase.h_inner_eq }
  spqrSendCoins := hBase.spqrSendCoins

/-- Produces the block-`463` `OkPlaced` slot witness at `w2i_cliDecryptSignalSlotEnvGuarded` from
`SpqrV1PlacedSeamsOfEnv` at `w2i_SpqrRecvTopStateGuardedBytesEnv`. -/
theorem w2i_hole3_w2_inner_guarded_of_spqr
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrGuarded : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv
      (fun st msg evs =>
        LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight W.C.F W.Q.K st.bytes →
          SpqrRecvC07C09aBytesEnv W.C.F W.Q.K st.bytes msg.bytes evs)
      SendEnv) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2i_cliDecryptSignalSlotEnvGuarded W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) :=
  w2i_hole3_w2_inner_guardedOf_of_inner hLs hblk hext_nodup ghFixed X W
    (tryDecryptCmkSeg4Env FmtWriteEnv) γ tp hHooks h547
    (fob2_w2_inner_stateGuarded_ok_of_spqr hLs hblk hext_nodup ghFixed hPl_mng W γ tp
      (LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight W.C.F W.Q.K)
      hGSpqr hFs hsat hHooks h547 hSpqrGuarded)

/-- Envelope-parametric block-`463` `OkPlaced` slot producer from per-state guarded SPQR codec leaf
contracts (`hDec`, `hFromPb`, `hIntoPb`) and their tight-inclusion lemmas. -/
theorem w2i_hole3_w2_inner_guarded_of_leaves
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {H_inner : V1InnerHeapPred}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {OldDecPre OldDecPost : DecodeStateGhost → List AllocEvent → Prop}
    {OldFromPb : V1State → List AllocEvent → Prop}
    {OldIntoPb : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrBase : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv PrevRecvEnv SendEnv)
    (hRecvBase : @SpqrRecvPlacedContractsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel H_inner
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F W.Q.K
      OldDecPre OldDecPost (InitInnerEnv W.C.F) OldFromPb
      (fun g => StatesRecvProtoEnv g.self g.msg) OldIntoPb
      (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
    (hDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok
        (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
        (mpl.base 325)
        (withLsCodeRoLoaded lsmpl
          (decodeStatePlacedSpecXOfEnv H_inner
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            DecodePreEnv DecodePostEnv)))
    (hFromPb :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok
        (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
        (mpl.base 333)
        (withLsCodeRoLoaded lsmpl
          (statesFromPbPlacedSpecXOfEnv fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F
            FromPbEnv)))
    (hIntoPb :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok
        (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
        (mpl.base 334)
        (withLsCodeRoLoaded lsmpl
          (statesIntoPbPlacedSpecXOfEnv fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F
            IntoPbEnv)))
    (hDecPre_sub : ∀ g evs, w2i_DecodeStateGuard W.C.F W.Q.K g.st.bytes →
      DecodePreEnv g evs → DecodeStateTightEnv evs)
    (hDecPost_sub : ∀ g evs, w2i_DecodeStateGuard W.C.F W.Q.K g.st.bytes →
      DecodePostEnv g evs → DecodeStateTightEnv evs)
    (hFromPb_sub : ∀ pb evs, w2i_FromPbStateGuard W.C.F pb →
      FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, w2i_IntoPbStateGuard g.st →
      IntoPbEnv g evs → StatesIntoPbTightEnv evs) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2i_cliDecryptSignalSlotEnvGuarded W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact w2i_hole3_w2_inner_guarded_of_spqr hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
    hGSpqr hFs hsat hHooks h547
    (w2i_spqrV1PlacedSeams_topStateGuarded_of_leaves hSpqrBase hRecvBase
      hDec hFromPb hIntoPb hDecPre_sub hDecPost_sub hFromPb_sub hIntoPb_sub)

/-- Block-`463` `OkPlaced` slot producer specialized to `w2i_DecodeStateGuardedEnv`,
`w2i_StatesFromPbGuardedEnv`, and `w2i_StatesIntoPbGuardedEnv`. -/
theorem w2i_hole3_w2_inner_guarded
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {H_inner : V1InnerHeapPred}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {PrevRecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {OldDecPre OldDecPost : DecodeStateGhost → List AllocEvent → Prop}
    {OldFromPb : V1State → List AllocEvent → Prop}
    {OldIntoPb : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hGSpqr : @CliGhostSpqrAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSpqrBase : @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      mmpl ghFixed W InitEnv PrevRecvEnv SendEnv)
    (hRecvBase : @SpqrRecvPlacedContractsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel H_inner
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F W.Q.K
      OldDecPre OldDecPost (InitInnerEnv W.C.F) OldFromPb
      (fun g => StatesRecvProtoEnv g.self g.msg) OldIntoPb
      (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
    (hDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok
        (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
        (mpl.base 325)
        (withLsCodeRoLoaded lsmpl
          (decodeStatePlacedSpecXOfEnv H_inner
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            (w2i_DecodeStateGuardedEnv W.C.F W.Q.K)
            (w2i_DecodeStateGuardedEnv W.C.F W.Q.K))))
    (hFromPb :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok
        (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
        (mpl.base 333)
        (withLsCodeRoLoaded lsmpl
          (statesFromPbPlacedSpecXOfEnv fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F
            (w2i_StatesFromPbGuardedEnv W.C.F))))
    (hIntoPb :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok
        (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))))
        (mpl.base 334)
        (withLsCodeRoLoaded lsmpl
          (statesIntoPbPlacedSpecXOfEnv fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits W.C.F
            w2i_StatesIntoPbGuardedEnv))) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (w2i_cliDecryptSignalSlotEnvGuarded W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) :=
  w2i_hole3_w2_inner_guarded_of_leaves hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
    hGSpqr hFs hsat hHooks h547 hSpqrBase hRecvBase hDec hFromPb hIntoPb
    (fun _ _ hG hf => hf hG)
    (fun _ _ hG hf => hf hG)
    (fun _ _ hG hf => hf hG)
    (fun _ _ hG hf => hf hG)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole3W2IntAux
