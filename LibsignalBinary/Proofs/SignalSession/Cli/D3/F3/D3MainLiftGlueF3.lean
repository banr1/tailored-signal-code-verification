/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2AuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidMatchElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine

/-!
# Two-Placement `579 → 617` & Real-Externs `MainOk*F3` Lift Glue

Lifts Block-`579` `runSpecTightPlaced` contracts across `MainIoOfPlaced`,
`MainEntryBudgetFitsCapOf`, and `Block617TransferFixedHyp` to real-externs Block `617`
(`cliExternsPlaced mmpl`), instantiating `MainOkPathBD3F3`, `MainInitSemF3`,
`MainOkValidMatchD3F3`, `MainOkUntypedD3F3`, and `MainOkParseNoneD3F3`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPl_111 libsignalMutatedBlocks
  libsignalSessionExterns libsignalSessionLib lsmpl lsρ
)
open CryptoVerification.E2E (
  PEParams PreKeyMessageFields UnreachedPqxdhPrimitives wirePrekey
)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification.SignalSession (
  CliHooks Inputs PqParty PqSessionMatches PqxdhPartyInSpecDomain cliExternsPlaced
  cliProcessInputs lsReadFileSym observe pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome
)
open CryptoVerification.SignalSession.Cli (CommitOk MainResult RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunBudgets_placed
  cliRunNeeds cliWrOk domainArgv_pqRecv instLsCodeInvCodeRoLoaded mProgPlaced mainFrameSize
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost InitGhost PksmGhost RunHsOk RunNeeds RunSem SlotAns addrValOf runAns runFiles
  runProgPlaced runRel
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (
  InitOk₀ cliDecryptPrekeyNeed cliInitiateNeed commitOk_pqRecvPrekey_decPkDef
  decPkDef initDef pkToE? pksmParseAgrees_S0 pksmTyped_S0 pqDecryptPrekeyAgrees_decPkDef
)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunRefine (runBounds_pqRecv)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_fromUtf8_eq cliGhostExterns_memrchr_eq encodeInjOn_deserializeScopeP_Q
  filesOk₀ runEncOk_pqRecv scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (DecPkOkD3 decPkOkD3_pqRecv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget (
  DecPkD3MatchingPathBOfReadEnv decPkPathBSlotOk_full_of_readEnv_placedBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (
  MainOkPathBD3F3 cliRunSemPathB
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkValidMatchD3F3 runAns_pqRecvPrekey_eq_canonical
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  CliPqOrD3RecvInputs MainOkParseNoneD3F3 cliRunSemF3 defaultExtrasF3 encodeInjOn_scopeIn
  pqD3ScopedRun ratchetScopeCoversPq_scopeIn runFilesOk_pqRecv_cli_f3 runHsOk_pqRecvPrekey_body_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (
  MainOkUntypedD3F3 cliRunSemD3 mainOkParseNoneD3F3_of_untyped
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  b2MainSpecTightNeedLocksFineAt cliBudgetLimits
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliStaticsPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv (
  subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (
  MainEntryBudgetFitsCapOf b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed
  cliGhostExterns_handleErrorMain cliGhostExterns_strlen domScopedRun
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (
  MainIoOfPlaced ReadStdinBoundedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (
  initFsState_cliProcessInputs_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget (
  CliSlotCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  CliSlotEnvs decIdKitBudgetEnv decSessKitBudgetEnv w1IdKitBudgetEnv w1SessKitBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget (
  runNeed_cli_le_resStack_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (
  CliInitD3Inputs MainInitSemF3 initD3ScopedRun initRunSemOk_of_filesOk₀
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (
  CliPubCalleesPlaced cliPubCallees_placed_ok cliRunArmEnvs cliRunCalleesEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget (
  r2EncGhost r2PeerGhost0
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (
  r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (
  RunEnv run_ok_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3PrevEmptyVRegsPlacedStmt pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  PksmLoopEnv PksmTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget (
  subsetA4PksmTryFromPlaced_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (
  cliPksmTryFrom_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget (
  CliDecryptSignalSlotEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget (
  cliDecryptSignal_slotOk_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget (
  cliEncrypt_slotOk_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (
  RunCalleesPlaced RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks allocContractsFsPlaced_of_hooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget (
  hc_kemDeserialize_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Upstream Seam Predicates (`CliInitSlotOkPlacedAt` & `Block617TransferFixedHyp`) -/

/-- Block-`521` `initiate` slot contract predicate. -/
def CliInitSlotOkPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
    sEnvs.initiate = InitEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
    needs.initiate = cliInitiateNeed cliRunBudgets →
    (slotsOfPlaced A lim sEnvs S needs).initiate.OkPlaced
      (lsProg_579 H) (lsmpl.base 521)

/-- Block-`617` ghost-to-real extern transfer predicate on `f3CliGhostHooksFixed`. -/
def Block617TransferFixedHyp
    (mpl mmpl : Obj.MultiPlacement) (ghFixed : CliGhostHooks)
    (CodeOk_ghost CodeOk_real : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop),
    (∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)) →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)

/-! ## 2. Two-Arg `(mmpl) (gh) (W)` Block-`579` `runSpecTightPlaced` Composition -/

/-- Packages `CliSlotEnvs`, `InitEnv`, and `DecPkEnv` into `SemPlacedBudget.RunSlotEnvs`. -/
noncomputable def runSlotEnvsF3 [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (slotEnvs : CliSlotEnvs)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets slotEnvs.spqrSend
    (w1SessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
    (w1IdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
  decryptSignal := CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets slotEnvs.tryDecrypt
    (decSessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
    (decIdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
  initiate := InitEnv
  decryptPrekey := DecPkEnv

/-- `PksmTryFromEnv` depends only on `x.bytes`. -/
theorem pksmTryFromEnv_addr_indep {x y : PksmGhost} (h : x.bytes = y.bytes) :
    PksmTryFromEnv x = PksmTryFromEnv y := by
  ext evs
  constructor
  · intro hevs
    rcases hevs with _ | ⟨hc, h3, h4, hl⟩ | ⟨hc, h3, h4, hl, ha⟩
    · exact .nil
    · exact .loopOnly (h ▸ hc) h3 h4 (by dsimp only [PksmLoopEnv] at hl ⊢; rw [← h]; exact hl)
    · exact .loopAfter (h ▸ hc) h3 h4 (by dsimp only [PksmLoopEnv] at hl ⊢; rw [← h]; exact hl)
        (h ▸ ha)
  · intro hevs
    rcases hevs with _ | ⟨hc, h3, h4, hl⟩ | ⟨hc, h3, h4, hl, ha⟩
    · exact .nil
    · exact .loopOnly (h.symm ▸ hc) h3 h4 (by dsimp only [PksmLoopEnv] at hl ⊢; rw [h]; exact hl)
    · exact .loopAfter (h.symm ▸ hc) h3 h4 (by dsimp only [PksmLoopEnv] at hl ⊢; rw [h]; exact hl)
        (h.symm ▸ ha)

/-- Assembles `CliPubCalleesPlaced mmpl gh W A lim ReadEnv sEnvs PksmTryFromEnv` on Block `579`
with `hpksm_addr` discharged via `pksmTryFromEnv_addr_indep`. -/
theorem cliPubCallees_f3_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64))
    (henc_addr : ∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y) :
    CliPubCalleesPlaced mmpl gh W A lim ReadEnv sEnvs PksmTryFromEnv :=
  cliPubCallees_placed_ok mmpl gh W hh hRead hinit_addr henc_addr hdec_ghost
    (fun _ _ h => pksmTryFromEnv_addr_indep h) hdp_ghost

/-- Two-arg `(mmpl) (gh) (W)` `RunCalleesPlaced` assembly on Block `579` for `cliRunSemF3`. -/
theorem runCallees_cli_f3_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {parseFn : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpub : CliPubCalleesPlaced mmpl gh W A lim ReadEnv
      (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv)
    (hslots : CliSlotCalleesPlaced mmpl gh X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W))
      A lim InitEnv X W)
    (hdecPk : (slotsOfPlaced A lim (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv)
      (cliRunSemF3 X W decPk decPkOk parseFn) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    RunCalleesPlaced A lim (cliRunCalleesEnvs ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
      (slotsOfPlaced A lim (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv)
        (cliRunSemF3 X W decPk decPkOk parseFn) (cliRunNeeds decPkNeed)) := by
  let S := cliRunSemF3 X W decPk decPkOk parseFn
  let sEnvs := runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv
  let needs := cliRunNeeds decPkNeed
  exact
    { readFile := hpub.readFile
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt :=
        cliEncrypt_slotOk_placed mmpl gh W A lim cliRunBudgets S scopeIn sEnvs needs
          slotEnvs.spqrSend
          (w1SessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
          (w1IdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
          hh hslots.w1Inner encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
          (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl rfl
      decryptSignal :=
        cliDecryptSignal_slotOk_placed mmpl gh W A lim cliRunBudgets S scopeIn sEnvs needs
          slotEnvs.tryDecrypt
          (decSessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
          (decIdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
          hh hslots.w2SessVt hslots.w2IdVt hslots.w2Inner encodeInjOn_deserializeScopeP_Q
          (fun _ h => h) rfl (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl rfl
      initiate := hinit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hdecPk
      kemDeserialize :=
        hc_kemDeserialize_placed
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }

/-- Block-`579` `runSpecTightPlaced` contract on `mProgPlaced` (Block `617`), discharging
`PreKeySignalMessage::try_from` (Block `111`) from `CliGhostAllocHooks`. -/
theorem hrun_cli_f3_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {decPkNeed : Nat}
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpub : CliPubCalleesPlaced mmpl gh W A lim ReadEnv
      (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv)
    (hslots : CliSlotCalleesPlaced mmpl gh X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W))
      A lim InitEnv X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : (slotsOfPlaced A lim (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv)
      (cliRunSemF3 X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
          (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv
          (cliRunSemF3 X W decPk decPkOk pksmParse)))
        uuidTryParse (runRel (cliRunSemF3 X W decPk decPkOk pksmParse)) cliWrOk cliResStack) :=
  run_ok_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    (hpub.arms (cliRunSemF3 X W decPk decPkOk pksmParse) decPkNeed)
    hh
    (runCallees_cli_f3_placed mmpl gh X W hh hpub hslots hinit hdecPk)
    (cliPksmTryFrom_placed_at_block
      (callerProg := runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      (subsetA4PksmTryFromPlaced_cli mmpl gh W hG) (fun _ => rfl))
    (runNeed_cli_le_resStack_placed A lim (runSlotEnvsF3 W A slotEnvs InitEnv DecPkEnv) hdecPkNeed)
    (by decide)
    (by decide)

/-! ## 3. Arbitrary-Domain `579 → 617 → Real Externs` Lift -/

/-- Lifts a Block-`579` `runSpecTightPlaced` contract and `MainEntryBudgetFitsCapOf` on
`domScopedRun Dom (runRel S)` across `579 → 617` and `Block617TransferFixedHyp` to
`cliExternsPlaced mmpl`. -/
theorem mainSubroutineD3F3_of_domScopedRunTight
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    (hCI : @CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv
      (libsignalPlacementOf mpl hblk hext_nodup) CodeOk_ghost)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnvOf : GhostName → BitVec 64 → RunCall → List AllocEvent → Prop}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      CodeOk_ghost CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : ∀ (γ : GhostName) (tp : BitVec 64),
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
        uuidTryParse (RunEnvOf γ tp) (domScopedRun Dom (runRel S)))
    (hrun : ∀ (γ : GhostName) (tp : BitVec 64),
      @subroutine_ok _
        (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 579)
        (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (libsignalPlacementOf mpl hblk hext_nodup) _
          CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (RunEnvOf γ tp) uuidTryParse (runRel S) cliWrOk cliResStack)) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel S)) cliProcessInputs) := by
  refine hTr W (domScopedRun Dom (runRel S)) fun γ tp => ?_
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  have hM24 :=
    b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed
      (ext := fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
      (W := W) (lim := cliBudgetLimits)
      hblk hext_nodup hCI Dom S
      hlibc initFsState_cliProcessInputs_eq
      (allocContractsFsPlaced_of_hooks mmpl ghFixed W (hG γ tp))
      (hioOf γ tp)
      (cliGhostExterns_strlen mmpl ghFixed W)
      (cliGhostExterns_fromUtf8_eq mmpl ghFixed W)
      (cliGhostExterns_memrchr_eq mmpl ghFixed W)
      (cliGhostExterns_handleErrorMain mmpl ghFixed W)
      hstk (hfitCap γ tp) (hrun γ tp)
  exact
    (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff mpl
      (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W (mpl.base 617)
      libcAddr CodeOk_ghost (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      cliBudgetLimits fineCostModel.init cliMainStk
      (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.cliStaticsPlacedAt mpl)
      (domScopedRun Dom (runRel S)) cliProcessInputs).mp hM24

/-- End-to-end lift from slot contracts (W1–W4 and `CliInitSlotOkPlacedAt`),
`MainEntryBudgetFitsCapOf`, and `Block617TransferFixedHyp` to real-externs Block `617`. -/
theorem mainSubroutineD3F3_of_slots
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    (Dom : Inputs → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {slotEnvs : GhostName → BitVec 64 → CliSlotEnvs}
    {InitEnv : GhostName → BitVec 64 → InitGhost → List AllocEvent → Prop}
    {DecPkEnv : GhostName → BitVec 64 → DecPkGhost → List AllocEvent → Prop}
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : ∀ (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
        (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
          W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          (slotEnvs γ tp) (InitEnv γ tp) (DecPkEnv γ tp))
        PksmTryFromEnv)
    (hslots : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        mmpl ghFixed X W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (slotEnvs γ tp))
    (hinit : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (InitEnv γ tp) X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          (slotEnvs γ tp) (InitEnv γ tp) (DecPkEnv γ tp))
        (cliRunSemF3 X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
        uuidTryParse
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
          (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs γ tp) (InitEnv γ tp) (DecPkEnv γ tp))
          PksmTryFromEnv (cliRunSemF3 X W decPk decPkOk pksmParse)))
        (domScopedRun Dom (runRel (cliRunSemF3 X W decPk decPkOk pksmParse)))) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel (cliRunSemF3 X W decPk decPkOk pksmParse)))
          cliProcessInputs) :=
  mainSubroutineD3F3_of_domScopedRunTight hblk hext_nodup ghFixed
    (@instLsCodeInvCodeRoLoaded (libsignalPlacementOf mpl hblk hext_nodup)) Dom
    (cliRunSemF3 X W decPk decPkOk pksmParse) hlibc hTr hG hioOf hstk hfitCap
    fun γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact hrun_cli_f3_placed mmpl ghFixed X W (hG γ tp) (hh γ tp) (hpub γ tp)
        (hslots γ tp) (hinit γ tp) hdecPkNeed (hdecPk γ tp)

/-! ## 4. Concrete D3 `MainOk*F3` Lifts (`PathB`, `Init`, `ValidMatch`, `Untyped`, `ParseNone`) -/

private theorem toClosureRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-- Establishes `MainOkPathBD3F3`, discharging slot `520` via
`decPkPathBSlotOk_full_of_readEnv_placedBudget`. -/
theorem mainOkPathBD3F3_of_seams
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (tdEnv : CliHooks → GhostName → BitVec 64 → TryDecryptEnvArgs → List AllocEvent → Prop)
    (slotEnvs : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → CliSlotEnvs)
    (InitEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      InitGhost → List AllocEvent → Prop)
    (DecPkEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
          (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
            W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
          PksmTryFromEnv)
    (hslots : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed X W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (slotEnvs X W γ tp))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv X W γ tp) X W)
    (hReadPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits cliRunBudgets_placed.readFile ReadEnv))
    (hDeserPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits SessDeserializeCancelEnv))
    (hStageP3 : @StageP3PrevEmptyVRegsPlacedStmt (libsignalPlacementOf mpl hblk hext_nodup))
    (hTryDecPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 508)
        (withLsCodeRoLoaded mpl
          (pollTryDecryptPlacedSpecTPTight W.C (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) (tdEnv W γ tp))))
    (hsEnv : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ g evs,
        DecPkD3MatchingPathBOfReadEnv (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          W cliRunBudgets_placed ReadEnv (tdEnv W γ tp) g evs →
        DecPkEnv X W γ tp g evs)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
            PksmTryFromEnv (cliRunSemPathB X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W)))) :
    MainOkPathBD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk := by
  intro h547 X W
  exact mainSubroutineD3F3_of_slots hblk hext_nodup ghFixed
    (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) X W
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed)
    hlibc hTr hG (hioOf W) hstk (hh h547 W) (hpub h547 X W) (hslots h547 X W) (hinit h547 X W)
    (by decide)
    (fun γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact decPkPathBSlotOk_full_of_readEnv_placedBudget X mmpl ghFixed W h547
        (toClosureRunHooksPlaced (hh h547 W γ tp)) (hReadPoll h547 W γ tp)
        (hDeserPoll h547 W γ tp) hStageP3 (hTryDecPoll h547 W γ tp)
        (cliRunSemPathB X W)
        (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
        (hsEnv X W γ tp) rfl rfl
        (fun _ _ _ _ h => ⟨h.party, h.loadedMatch, h.keyPairLt, h.preKeysWf, h.baseKeysLt⟩)
        rfl)
    (hfitCap h547 X W)

/-- Establishes `MainInitSemF3` at `cliRunSemF3 X W` from any valid slot-`520` `OkPlaced`
witness. -/
theorem mainInitSemF3_of_slot
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (slotEnvs : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → CliSlotEnvs)
    (InitEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      InitGhost → List AllocEvent → Prop)
    (DecPkEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (decPk : UnreachedPqxdhPrimitives → CliHooks →
      FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : UnreachedPqxdhPrimitives → CliHooks →
      FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
          (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
            W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
          PksmTryFromEnv)
    (hslots : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed X W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (slotEnvs X W γ tp))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv X W γ tp) X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
          (cliRunSemF3 X W (decPk X W) (decPkOk X W) pksmParse)
          (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
            PksmTryFromEnv (cliRunSemF3 X W (decPk X W) (decPkOk X W) pksmParse)))
          (initD3ScopedRun ⟨W.C, W.Q⟩
            (runRel (cliRunSemF3 X W (decPk X W) (decPkOk X W) pksmParse)))) :
    MainInitSemF3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk := by
  intro h547 X W
  refine ⟨cliRunSemF3 X W (decPk X W) (decPkOk X W) pksmParse,
    initRunSemOk_of_filesOk₀ rfl rfl rfl, ?_⟩
  exact mainSubroutineD3F3_of_slots hblk hext_nodup ghFixed
    (CliInitD3Inputs ⟨W.C, W.Q⟩) X W
    hlibc hTr hG (hioOf W) hstk (hh h547 W) (hpub h547 X W) (hslots h547 X W) (hinit h547 X W)
    hdecPkNeed (hdecPk h547 X W) (hfitCap h547 X W)

/-- Establishes `MainInitSemF3` by instantiating slot `520` with `cliRunSemPathB X W`. -/
theorem mainInitSemF3_of_seams
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (tdEnv : CliHooks → GhostName → BitVec 64 → TryDecryptEnvArgs → List AllocEvent → Prop)
    (slotEnvs : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → CliSlotEnvs)
    (InitEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      InitGhost → List AllocEvent → Prop)
    (DecPkEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
          (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
            W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
          PksmTryFromEnv)
    (hslots : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed X W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (slotEnvs X W γ tp))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv X W γ tp) X W)
    (hReadPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits cliRunBudgets_placed.readFile ReadEnv))
    (hDeserPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits SessDeserializeCancelEnv))
    (hStageP3 : @StageP3PrevEmptyVRegsPlacedStmt (libsignalPlacementOf mpl hblk hext_nodup))
    (hTryDecPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 508)
        (withLsCodeRoLoaded mpl
          (pollTryDecryptPlacedSpecTPTight W.C (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) (tdEnv W γ tp))))
    (hsEnv : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ g evs,
        DecPkD3MatchingPathBOfReadEnv (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          W cliRunBudgets_placed ReadEnv (tdEnv W γ tp) g evs →
        DecPkEnv X W γ tp g evs)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
            PksmTryFromEnv (cliRunSemPathB X W)))
          (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W)))) :
    MainInitSemF3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainInitSemF3_of_slot hblk hext_nodup ghFixed slotEnvs InitEnv DecPkEnv
    (fun X W => decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (fun _ W => LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3.DecPkOkPathB
      ⟨W.C, W.Q⟩ scopeIn)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed)
    hlibc hTr hG hioOf hstk hh hpub hslots hinit (by decide)
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact decPkPathBSlotOk_full_of_readEnv_placedBudget X mmpl ghFixed W h547
        (toClosureRunHooksPlaced (hh h547 W γ tp)) (hReadPoll h547 W γ tp)
        (hDeserPoll h547 W γ tp) hStageP3 (hTryDecPoll h547 W γ tp)
        (cliRunSemPathB X W)
        (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
        (hsEnv X W γ tp) rfl rfl
        (fun _ _ _ _ h => ⟨h.party, h.loadedMatch, h.keyPairLt, h.preKeysWf, h.baseKeysLt⟩)
        rfl)
    hfitCap

/-- `RunSem` for non-canonical valid pre-key `recv` (`DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn`). -/
noncomputable def cliRunSemD3ValidMatch (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSemF3 X W (decPkDef X ⟨W.C, W.Q⟩ scopeIn) (DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn) pksmParse

/-- Pure `pqD3ScopedRun` + `observe` + `CommitOk` witness for `cliRunSemD3ValidMatch X W` on
non-canonical valid pre-key `recv` inputs (`validMatch`). -/
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
      CommitOk inp (MainResult.ofAnswer a) := by
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
    runAns_pqRecvPrekey_eq_canonical S X WP scopeIn rfl rfl
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

/-- Reduces `MainOkValidMatchD3F3` to `b2MainSpecTightNeedLocksFineAt` on
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W))`. -/
theorem mainOkValidMatchD3F3_of_runSem
    {mpl mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hmain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W)))
            cliProcessInputs)) :
    MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr brkStart stk := by
  intro h547 X W
  refine ⟨pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W)),
    hmain h547 X W, ?_⟩
  intro st hwf body pm m rc hbody hparse hpk hm hmatch
  exact ⟨runAns (cliRunSemD3ValidMatch X W) (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
    runRel_pqRecv_validMatch X W st body pm m rc hwf hbody hparse hpk hm hmatch⟩

/-- Establishes `MainOkValidMatchD3F3` from `mainSubroutineD3F3_of_slots` and a slot-`520`
`OkPlaced` witness for `cliRunSemD3ValidMatch X W`. -/
theorem mainOkValidMatchD3F3_of_seams
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (slotEnvs : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → CliSlotEnvs)
    (InitEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      InitGhost → List AllocEvent → Prop)
    (DecPkEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
          (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
            W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
          PksmTryFromEnv)
    (hslots : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed X W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (slotEnvs X W γ tp))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv X W γ tp) X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
          (cliRunSemD3ValidMatch X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              (slotEnvs X W γ tp) (InitEnv X W γ tp) (DecPkEnv X W γ tp))
            PksmTryFromEnv (cliRunSemD3ValidMatch X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W)))) :
    MainOkValidMatchD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkValidMatchD3F3_of_runSem fun h547 X W =>
    mainSubroutineD3F3_of_slots hblk hext_nodup ghFixed
      (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) X W
      hlibc hTr hG (hioOf W) hstk (hh h547 W) (hpub h547 X W) (hslots h547 X W) (hinit h547 X W)
      hdecPkNeed (hdecPk h547 X W) (hfitCap h547 X W)

/-- Establishes `MainOkUntypedD3F3` at `cliRunSemD3 W` from `mainSubroutineD3F3_of_slots`
and a slot-`520` `OkPlaced` witness. -/
theorem mainOkUntypedD3F3_of_seams
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (slotEnvs : CliHooks → GhostName → BitVec 64 → CliSlotEnvs)
    (InitEnv : CliHooks → GhostName → BitVec 64 → InitGhost → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → GhostName → BitVec 64 → DecPkGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
          (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
            W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs W γ tp) (InitEnv W γ tp) (DecPkEnv W γ tp))
          PksmTryFromEnv)
    (hslots : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed defaultExtrasF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits (slotEnvs W γ tp))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv W γ tp) defaultExtrasF3 W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs W γ tp) (InitEnv W γ tp) (DecPkEnv W γ tp))
          (cliRunSemD3 W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              (slotEnvs W γ tp) (InitEnv W γ tp) (DecPkEnv W γ tp))
            PksmTryFromEnv (cliRunSemD3 W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W)))) :
    MainOkUntypedD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk := by
  intro h547 W
  exact mainSubroutineD3F3_of_slots hblk hext_nodup ghFixed
    (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) defaultExtrasF3 W
    hlibc hTr hG (hioOf W) hstk (hh h547 W) (hpub h547 W) (hslots h547 W) (hinit h547 W)
    hdecPkNeed (hdecPk h547 W) (hfitCap h547 W)

theorem mainOkParseNoneD3F3_of_seams
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (slotEnvs : CliHooks → GhostName → BitVec 64 → CliSlotEnvs)
    (InitEnv : CliHooks → GhostName → BitVec 64 → InitGhost → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → GhostName → BitVec 64 → DecPkGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalCodeRoLoaded mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @RunHooksPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hpub : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliPubCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv
          (@runSlotEnvsF3 (libsignalPlacementOf mpl hblk hext_nodup) _
            W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs W γ tp) (InitEnv W γ tp) (DecPkEnv W γ tp))
          PksmTryFromEnv)
    (hslots : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliSlotCalleesPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
          mmpl ghFixed defaultExtrasF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits (slotEnvs W γ tp))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @CliInitSlotOkPlacedAt (libsignalPlacementOf mpl hblk hext_nodup) _
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv W γ tp) defaultExtrasF3 W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            (slotEnvs W γ tp) (InitEnv W γ tp) (DecPkEnv W γ tp))
          (cliRunSemD3 W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            (runSlotEnvsF3 W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              (slotEnvs W γ tp) (InitEnv W γ tp) (DecPkEnv W γ tp))
            PksmTryFromEnv (cliRunSemD3 W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W)))) :
    MainOkParseNoneD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  mainOkParseNoneD3F3_of_untyped
    (mainOkUntypedD3F3_of_seams hblk hext_nodup ghFixed slotEnvs InitEnv DecPkEnv hlibc hTr hG
      hioOf hstk hh hpub hslots hinit hdecPkNeed hdecPk hfitCap)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
