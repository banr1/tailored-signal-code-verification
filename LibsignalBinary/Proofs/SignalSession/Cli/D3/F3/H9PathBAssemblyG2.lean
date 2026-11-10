/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import ProofLib.SepLogic.WPFrozen

/-!
# Parametric `LibsignalFrozen` Matching-Session Path-B Assembly

Provides `sEnvs`-polymorphic and `ReadEnv`-parametric `LibsignalFrozen` slot-transport and assembly
theorems for `MainOkPathBD3F3`, transporting `encrypt`, `decryptSignal`, and `init` slot contracts
from `cliRunSemD2c_placed` to `cliRunSemPathB` and lifting Path-B `decryptPrekey` at Slot 520.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
  libsignalSessionExterns lsmpl lsρ
)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsFrozen extHookStack withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.Record (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib lsReadFileSym
)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunBudgets_placed cliRunNeeds
  cliRunSemD2c_placed cliWrOk instLsCodeInvFrozen mProgPlaced mainFrameSize
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost DecSigGhost EncGhost InitGhost RunNeeds RunSem addrValOf mkSlot runProgPlaced runRel
  unixEpoch
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed decPkDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget (
  DecPkD3MatchingPathBOfReadEnv decPkPathBSlotOk_full_of_readEnv_placedBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 (
  Block617TransferFixedHyp mainSubroutineD3F3_of_domScopedRunTight pksmTryFromEnv_addr_indep
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (
  MainOkPathBD3F3 cliRunSemPathB
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  CliPqOrD3RecvInputs pqD3ScopedRun
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (hRead_of_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  b2MainSpecTightNeedLocksFineAt cliBudgetLimits
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliStaticsPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (
  MainEntryBudgetFitsCapOf domScopedRun
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (
  MainIoOfPlaced ReadStdinBoundedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget (
  runNeed_cli_le_resStack_placed
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
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget (
  CliInitSlotOkPlaced CliPubCalleesFrozenPlaced CliRunHooksBundle cliPubCallees_d2c_frozen_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (
  RunEnv run_ok_frozen_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs decPkSlotSpecFrozenPlaced decPkSlotSpecPlaced decSigSlotSpecBasePlaced
  decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf encSlotSpecPlaced slotsOfPlaced
  slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3PrevEmptyVRegsPlacedStmt pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  PksmTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget (
  subsetA4PksmTryFromPlaced_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (
  cliPksmTryFrom_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget (
  decSigDef_eq_runProofs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (
  RunCalleesPlaced RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  decPkSlotSpecBasePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget (
  hc_kemDeserialize_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (
  sessDeserialize_cli_dcan_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. `[LibsignalFullPlacement]` Builders -/

/-- Constructs `[LibsignalFullPlacement]` extending `libsignalPlacementOf mpl hblk hext_nodup` from `Placeable mpl`. -/
@[instance_reducible]
def h9g_libsignalFullPlacementOfPlaceable (mpl : MultiPlacement)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hFullPl : libsignalSessionLib.Placeable mpl) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hFullPl

@[instance_reducible]
noncomputable def h9g_libsignalFullPlacementOfLinkedAt {elfBytes : List (BitVec 8)}
    (mpl : MultiPlacement) (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement :=
  h9g_libsignalFullPlacementOfPlaceable mpl hblk hext_nodup hLs.choose_spec.2.1

/-! ## 2. `RunSem` Congruence Bridges (`cliRunSemD2c_placed` → `cliRunSemPathB`) -/

private theorem h9g_runProofs_encDef_eq_agree (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    CryptoVerification.SignalSession.Cli.RunProofs.encDef P Scope =
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef P Scope := by
  have hFinal : ∀ F calls,
      CryptoVerification.SignalSession.Cli.RunProofs.cliFinal F calls =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal F calls := by
    intro F calls
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliFinal
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal
    have hStep :
        CryptoVerification.SignalSession.Cli.RunProofs.cliStep F =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers Scope F peer
        (CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer) =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer) := by
    intro F peer
    have hKey :
        CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer := by
      unfold CryptoVerification.SignalSession.Cli.RunProofs.encKey
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey
      rcases loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers
    rcases CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer with _ | _ <;>
      rfl
  funext F peer me ptext coins
  unfold CryptoVerification.SignalSession.Cli.RunProofs.encDef
    CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef
  rw [hAns F peer]
  generalize CryptoGames.LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
      (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer))
    ptext peer me unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

/-- `encSlotSpecPlaced` depends on `S : RunSem` only through `(S.filesOk, S.encOk, S.encrypt)`. -/
theorem h9g_encSlotSpecPlaced_congr_sem [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EncEnv : EncGhost → List AllocEvent → Prop) (S₁ S₂ : RunSem) (stk : Nat)
    (hfiles : S₁.filesOk = S₂.filesOk) (hencOk : S₁.encOk = S₂.encOk)
    (henc : S₁.encrypt = S₂.encrypt) :
    encSlotSpecPlaced A lim EncEnv S₁ stk = encSlotSpecPlaced A lim EncEnv S₂ stk := by
  unfold encSlotSpecPlaced
  rw [hfiles, hencOk, henc]

/-- `decSigSlotSpecFrozenPlaced` depends on `S : RunSem` only through `(S.filesOk, S.decryptSignal)`. -/
theorem h9g_decSigSlotSpecFrozenPlaced_congr_sem [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S₁ S₂ : RunSem) (stk : Nat)
    (hfiles : S₁.filesOk = S₂.filesOk) (hdecSig : S₁.decryptSignal = S₂.decryptSignal) :
    decSigSlotSpecFrozenPlaced A lim DecSigEnv S₁ stk =
      decSigSlotSpecFrozenPlaced A lim DecSigEnv S₂ stk := by
  unfold decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf decSigSlotSpecBasePlaced
  rw [hfiles, hdecSig]

/-- Transports an `encrypt` `OkPlaced` witness from `cliRunSemD2c_placed X W` to `cliRunSemPathB X W`. -/
theorem h9g_encSlotOk_d2c_to_pathB [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {EncEnv : EncGhost → List AllocEvent → Prop} {need : Nat}
    {prog : Program} {entry : BitVec 64}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h : (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemD2c_placed X W)) need).OkPlaced
      prog entry) :
    (mkSlot (encSlotSpecPlaced A lim EncEnv (cliRunSemPathB X W)) need).OkPlaced
      prog entry := by
  intro stk h1 h2
  have heq := h9g_encSlotSpecPlaced_congr_sem A lim EncEnv
    (cliRunSemD2c_placed X W) (cliRunSemPathB X W) stk rfl rfl
    (h9g_runProofs_encDef_eq_agree ⟨W.C, W.Q⟩ scopeIn)
  simpa only [mkSlot, heq] using h stk h1 h2

/-- Transports a frozen `decryptSignal` `OkPlaced` witness from `cliRunSemD2c_placed X W` to `cliRunSemPathB X W`. -/
theorem h9g_decSigFrozenSlotOk_d2c_to_pathB [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecSigEnv : DecSigGhost → List AllocEvent → Prop} {need : Nat}
    {prog : Program} {entry : BitVec 64}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h : (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD2c_placed X W))
      need).OkPlaced prog entry) :
    (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemPathB X W)) need).OkPlaced
      prog entry := by
  intro stk h1 h2
  have heq := h9g_decSigSlotSpecFrozenPlaced_congr_sem A lim DecSigEnv
    (cliRunSemD2c_placed X W) (cliRunSemPathB X W) stk rfl
    (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
  simpa only [mkSlot, heq] using h stk h1 h2

theorem h9g_initSlotOk_pathB_of_cliInitSlotOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop} {sEnvs : RunSlotEnvs} {decPkNeed : Nat}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hInit : CliInitSlotOkPlaced mmpl gh A lim InitEnv X W)
    (hsInit : sEnvs.initiate = InitEnv) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W)
      (cliRunNeeds decPkNeed)).initiate.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521) :=
  hInit (cliRunSemPathB X W) sEnvs (cliRunNeeds decPkNeed) hsInit rfl rfl rfl rfl

/-! ## 3. `LibsignalFrozen` Slot-520 Monotonicity and Path-B Slot Contract -/

/-- Lifts any `decPkSlotSpecPlaced` (`StoreKit.withLsCodeRoLoaded lsmpl`) contract to
`decPkSlotSpecFrozenPlaced` (`withLsFrozen lsmpl`) via `LibsignalCodeRoLoaded.of_libsignalFrozen`. -/
theorem h9g_decPkSlotSpecFrozenPlaced_of_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (h : subroutine_ok prog entry (decPkSlotSpecPlaced A lim DecPkEnv S stk)) :
    subroutine_ok prog entry (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ :=
        extract_withLsFrozen (spec := decPkSlotSpecBasePlaced A lim DecPkEnv S stk) hp
      change _ ⊨
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (decPkSlotSpecBasePlaced A lim DecPkEnv S stk)).pre _ _ ∗ _
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨LibsignalCodeRoLoaded.of_libsignalFrozen hfr, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem h9g_slotOk_decPkFrozenPlaced_of_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {sEnvs : RunSlotEnvs} {S : RunSem} {needs : RunNeeds}
    (h : (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced prog entry) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced prog entry :=
  fun stk h1 h2 => h9g_decPkSlotSpecFrozenPlaced_of_placed (h stk h1 h2)

/-- Discharges both `hRead` (`lsReadFileSym`) and `hDeser` (`lsmpl.base 46` at
`SessDeserializeCancelEnv`) on `dpPollProgPlaced` from `HookSat` and `CliGhostAllocHooks`. -/
theorem h9g_poll_readFile_and_sessDeser_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    [HasFineReallocCredit M]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile ReadEnv) ∧
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv) :=
  ⟨hRead_of_hookSat
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) hsat,
   CryptoVerification.SignalSession.Cli.Store.PlacedCommon.ls_transfer_lscro
      (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (sessDeserialize_cli_dcan_placed_ok mmpl gh W hG (fun _ hr => hr))⟩

private theorem h9g_toClosureRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-- Lifts `decPkPathBSlotOk_full_of_readEnv_placedBudget` to
`(slotsOfSigPkFrozenPlaced …).decryptPrekey.OkPlaced` at `cliRunSemPathB X W`. -/
theorem h9g_decPkPathBSlotOk_frozen_of_readEnv [LibsignalPlacement] {M : AllocCostModel}
    [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBOfReadEnv A.repAlloc W cliRunBudgets_placed ReadEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  obtain ⟨hRead, hDeser⟩ := h9g_poll_readFile_and_sessDeser_of_hooks mmpl gh W hG hsat
  exact h9g_slotOk_decPkFrozenPlaced_of_placed
    (decPkPathBSlotOk_full_of_readEnv_placedBudget X mmpl gh W h547
      (h9g_toClosureRunHooksPlaced hHooks.runHooks) hRead hDeser hStageP3 hTryDec
      (cliRunSemPathB X W) sEnvs (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
      hsEnv rfl rfl
      (by intro _ _ _ _ ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩)
      rfl)

/-! ## 4. Parametric `LibsignalFrozen` Block-`579 → 617 → MainOkPathBD3F3` Assemblers -/

theorem h9g_cliPubCallees_f3_frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
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
    CliPubCalleesFrozenPlaced mmpl gh A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W :=
  cliPubCallees_d2c_frozen_ok mmpl gh W hHooks hinit_addr henc_addr hdec_ghost
    (fun _ _ h => pksmTryFromEnv_addr_indep h) hdp_ghost

/-- `sEnvs`-polymorphic `[LibsignalFullPlacement]` Block-`579`
`runSpecTightPlaced (LibsignalFrozen lsmpl)` assembly for `cliRunSemPathB X W`. -/
theorem h9g_hrun_pathB_sEnvs_frozen_placed [LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    {decPkNeed : Nat}
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hpub : CliPubCalleesFrozenPlaced mmpl gh A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W)
    (henc :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W)
        (cliRunNeeds decPkNeed)).encrypt.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hdecSig :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W)
        (cliRunNeeds decPkNeed)).decryptSignal.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hinit :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W)
        (cliRunNeeds decPkNeed)).initiate.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W)
        (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv
          (cliRunSemPathB X W)))
        uuidTryParse (runRel (cliRunSemPathB X W)) cliWrOk cliResStack) := by
  let S := cliRunSemPathB X W
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  have hcallees : RunCalleesPlaced A lim (cliRunCalleesEnvs ReadEnv) H cliRunBudgets
      (slotsOfSigPkFrozenPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) :=
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := henc
      decryptSignal := hdecSig
      initiate := hinit
      decryptPrekey := hdecPk
      kemDeserialize :=
        hc_kemDeserialize_placed (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }
  exact
    run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced H) (i := 617)
      (hpub.arms S decPkNeed)
      hh
      hcallees
      (cliPksmTryFrom_placed_at_block
        (callerProg := runProgPlaced H) (i := 579)
        (subsetA4PksmTryFromPlaced_cli mmpl gh W hG) (fun _ => rfl))
      (runNeed_cli_le_resStack_placed A lim sEnvs (S := S) hdecPkNeed)
      (by decide)
      (by decide)

/-- `sEnvs`-polymorphic `LibsignalFrozen mpl` lift from Block 579 through Block 617 to real externs for `cliRunSemPathB`. -/
theorem h9g_mainSubroutinePathBD3F3_of_sEnvs_frozen
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hFullPl : libsignalSessionLib.Placeable mpl)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    (Dom : Inputs → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (sEnvs : GhostName → BitVec 64 → RunSlotEnvs)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hpub : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliPubCalleesFrozenPlaced
        mmpl ghFixed (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliRunCalleesEnvs ReadEnv) (sEnvs γ tp)
        (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) (sEnvs γ tp) PksmTryFromEnv) W)
    (henc : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfSigPkFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs γ tp)
        (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).encrypt.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfSigPkFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs γ tp)
        (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptSignal.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfSigPkFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs γ tp)
        (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).initiate.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfSigPkFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs γ tp)
        (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : ∀ (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
        uuidTryParse
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) (sEnvs γ tp) PksmTryFromEnv
          (cliRunSemPathB X W)))
        (domScopedRun Dom (runRel (cliRunSemPathB X W)))) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (domScopedRun Dom (runRel (cliRunSemPathB X W)))
          cliProcessInputs) :=
  mainSubroutineD3F3_of_domScopedRunTight hblk hext_nodup ghFixed
    (@instLsCodeInvFrozen (libsignalPlacementOf mpl hblk hext_nodup))
    Dom (cliRunSemPathB X W) hlibc hTr hG hioOf hstk hfitCap
    fun γ tp => by
      letI : LibsignalFullPlacement :=
        h9g_libsignalFullPlacementOfPlaceable mpl hblk hext_nodup hFullPl
      exact h9g_hrun_pathB_sEnvs_frozen_placed mmpl ghFixed X W (hG γ tp) (hHooks γ tp) (hpub γ tp)
        (henc γ tp) (hdecSig γ tp) (hinit γ tp) hdecPkNeed (hdecPk γ tp)

/-- Proves `MainOkPathBD3F3` under `LibsignalFrozen mpl` for arbitrary `(ReadEnv, sEnvs)` from the
four `slotsOfSigPkFrozenPlaced` slot contracts and `MainEntryBudgetFitsCapOf`. -/
theorem h9g_pathB_assembly_of_fitsCap
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hFullPl : libsignalSessionLib.Placeable mpl)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (sEnvs : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hinit_addr : ∀ X W γ tp g d2 fsp,
      (sEnvs X W γ tp).initiate (r1cInitGhost g d2 fsp) =
        (sEnvs X W γ tp).initiate (r1cInitGhost g d2 0#64))
    (henc_addr : ∀ X W γ tp g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      (sEnvs X W γ tp).encrypt (r2EncGhost g peerG meG fsp) =
        (sEnvs X W γ tp).encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ X W γ tp g fsp w peerV meG msgG m,
      (sEnvs X W γ tp).decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        (sEnvs X W γ tp).decryptSignal (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      (sEnvs X W γ tp).decryptPrekey x = (sEnvs X W γ tp).decryptPrekey y)
    (henc : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).encrypt.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptSignal.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).initiate.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) (sEnvs X W γ tp) PksmTryFromEnv
            (cliRunSemPathB X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W)))) :
    MainOkPathBD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  fun h547 X W =>
    h9g_mainSubroutinePathBD3F3_of_sEnvs_frozen hblk hext_nodup hFullPl ghFixed
      (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) X W (sEnvs X W)
      hlibc hTr hG (hioOf W) hstk (hHooks h547 W)
      (fun γ tp => by
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        exact h9g_cliPubCallees_f3_frozen_placed mmpl ghFixed W (hHooks h547 W γ tp)
          (hinit_addr X W γ tp) (henc_addr X W γ tp) (hdec_ghost X W γ tp) (hdp_ghost X W γ tp))
      (henc h547 X W) (hdecSig h547 X W) (hinit h547 X W)
      hdecPkNeed (hdecPk h547 X W) (hfitCap h547 X W)

/-- Proves `MainOkPathBD3F3` from `LinkedAt elfBytes mpl`, `encrypt` / `decryptSignal` slot
contracts at `cliRunSemD2c_placed`, `CliInitSlotOkPlaced`, Path-B Slot-520, and `MainEntryBudgetFitsCapOf`. -/
theorem h9g_pathB_assembly_of_d2cSlots_and_fitsCap
    {elfBytes : List (BitVec 8)} {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (sEnvs : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (InitEnv : CliHooks → InitGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hsInit : ∀ X W γ tp, (sEnvs X W γ tp).initiate = InitEnv W)
    (hinit_addr : ∀ X W γ tp g d2 fsp,
      (sEnvs X W γ tp).initiate (r1cInitGhost g d2 fsp) =
        (sEnvs X W γ tp).initiate (r1cInitGhost g d2 0#64))
    (henc_addr : ∀ X W γ tp g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      (sEnvs X W γ tp).encrypt (r2EncGhost g peerG meG fsp) =
        (sEnvs X W γ tp).encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ X W γ tp g fsp w peerV meG msgG m,
      (sEnvs X W γ tp).decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        (sEnvs X W γ tp).decryptSignal (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      (sEnvs X W γ tp).decryptPrekey x = (sEnvs X W γ tp).decryptPrekey y)
    (hW1 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvs X W γ tp).encrypt (cliRunSemD2c_placed X W))
          (cliRunNeeds decPkNeed).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hW2 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (sEnvs X W γ tp).decryptSignal (cliRunSemD2c_placed X W))
          (cliRunNeeds decPkNeed).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hW3 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitEnv W) X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (sEnvs X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) (sEnvs X W γ tp) PksmTryFromEnv
            (cliRunSemPathB X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W)))) :
    MainOkPathBD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h9g_pathB_assembly_of_fitsCap hblk hext_nodup hLs.choose_spec.2.1 ghFixed sEnvs
    hlibc hTr hG hioOf hstk hHooks hinit_addr henc_addr hdec_ghost hdp_ghost
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h9g_encSlotOk_d2c_to_pathB X W (hW1 h547 X W γ tp))
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h9g_decSigFrozenSlotOk_d2c_to_pathB X W (hW2 h547 X W γ tp))
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h9g_initSlotOk_pathB_of_cliInitSlotOkPlaced mmpl ghFixed X W
        (hW3 h547 X W γ tp) (hsInit X W γ tp))
    hdecPkNeed hdecPk hfitCap

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2
