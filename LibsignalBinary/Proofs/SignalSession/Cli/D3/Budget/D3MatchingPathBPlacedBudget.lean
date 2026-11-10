/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3MatchingPathBAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3ParseRejectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# Budget-Threaded Matching-Session Path-B Slot, `main` Lift, and `W4RecvPrekeyRealEnv` Inclusion

Defines the non-canonical matching-session Path-B semantics (`cliRunSemPathB`, `cliRunSemPathBFull`)
and slot envelopes (`DecPkD3MatchingPathBEnv`, `DecPkD3MatchingPathBCliEnv`), proves the block-`520`
`decrypt_prekey` slot contracts and block-`617` `mainSpecTightPlacedAt` lifts, and establishes
`SingleSlotFineSpec`, closed `1 MiB` slot-cap inequalities, `W4RecvPrekeyRealDomOf`, and inclusion
into `W4RecvPrekeyRealEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage Session SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E
  (PEParams RecordExtras UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs PqParty PqxdhPartyInSpecDomain cliExternsPlaced
   isCliPanicSymbolPlaced lsReadFileSym observe pqRecvInputs pqxdhExpectedOutcome)
open CryptoVerification.SignalSession.Cli (CommitOk MainResult StoresGhost cliStaticsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall cliIo cliMainStk cliRunBudgets_placed cliWrOk
   domainArgv_pqRecv parseArgs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem addrValOf dpPollNeed mkSlot runAns runFiles runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOk₀ SessMatchesPm cliDecryptPrekeyNeed
   commitOk_pqRecvPrekey_decPkDef decPkDef dpWrapFrame)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollSessKitPlaced dpPollEntryPlaced dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunRefine (runBounds_pqRecv)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ runEncOk_pqRecv scopeIn
   scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (phaseGroupSpec_exists_guarded)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf (peerSpqrStateTight640_of_pqRecv_wf)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealEnv W4RecvPrekeyRealParams mkW4RecvPrekeySlotParams
   w4RecvPrekeyRealEnv_nonvacuous_alloc w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4RecvPrekeyRealDomOf W4TryDecryptCallDomOf
   W4TryDecryptPathACDomOf w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live
   w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak w4RecvPrekeyReal1MiB_i_eq
   w4RecvPrekeyReal1MiB_i_singleSlotFineSpec)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (DecPkOkPathB cliRunSem_placed encodeInjOn_scopeIn_placed observe_runAns_pqRecv_matchingPathB
   pqRecvMatchingModel pqSessionOf ratchetScopeCoversPq_scopeIn_placed
   runFilesOk_pqRecv_cli_placed runHsOk_pqRecv_matchingPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudget
  (MatchingPathBPollEnv decPk_matchingPathB_poll_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decPkSlotSpecPlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3PrevEmptyVRegsPlacedStmt pollTryDecryptPlacedSpecTPTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollSessBudgetEnv cliPollSess_kitPlacedOkSE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
  (K₀_statePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
  (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
  (cliDecryptPrekey_ok_state_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (dpSlotPollKStatePlaced dpSlot_ok_state_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv mainSpecTightPlacedAt readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext name
  by_cases hp : Rust.isPanicSymbol name = true
  · have hother : cliGhostExterns gh (cliExternsPlaced mmpl W) name = cliExternsPlaced mmpl W name :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustDeallocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustReallocSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustAllocZeroedSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsRustNoAllocShimSymCli] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

/-! ## 1. Matching-Session Path-B Semantics (`cliRunSemPathB`, `cliRunSemPathBFull`) & Envelopes -/

/-- Conjunction of `DecPkOk₀` and `DecPkOkPathB`. -/
def DecPkOkPathBFull (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  DecPkOk₀ W Scope F peer me pm ∧ DecPkOkPathB W Scope F peer me pm

/-- `RunSem` instantiated with `decPkDef`, `DecPkOkPathB`, and `Pksm.pksmParse`. -/
noncomputable def cliRunSemPathB (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSem_placed X W (decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn) pksmParse

/-- `RunSem` instantiated with `decPkDef`, `DecPkOkPathBFull`, and `Pksm.pksmParse`. -/
noncomputable def cliRunSemPathBFull (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSem_placed X W (decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (DecPkOkPathBFull ⟨W.C, W.Q⟩ scopeIn) pksmParse

/-- Establishes `runRel`, `observe`, and `CommitOk` at `cliRunSemPathB X W` for any `body` with
`Pksm.pksmParse body = some pm` and `(wirePrekey :: body).length ≤ 2 ^ 32` under a matching current
session `st.session = some (x, g)`. -/
theorem runRel_pqRecv_matchingPathB (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hlen : (wirePrekey :: body).length ≤ 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hmatch : SessMatchesPm (pqSessionOf x g) pm) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    let a := runAns (cliRunSemPathB X W) inp
    runRel (cliRunSemPathB X W) inp a ∧
      observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvMatchingModel WP st x g pm rc) ∧
      CommitOk inp (MainResult.ofAnswer a) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  refine ⟨⟨domainArgv_pqRecv WP st (wirePrekey :: body) rc,
      runBounds_pqRecv WP st (wirePrekey :: body) rc hlen,
      runFilesOk_pqRecv_cli_placed (S := cliRunSemPathB X W) rfl WP st (wirePrekey :: body) rc hwf,
      runEncOk_pqRecv (cliRunSemPathB X W) WP st (wirePrekey :: body) rc,
      runHsOk_pqRecv_matchingPathB (cliRunSemPathB X W) WP scopeIn
        (fun _ _ _ _ h => h) rfl encodeInjOn_scopeIn_placed (ratchetScopeCoversPq_scopeIn_placed WP)
        st x g body pm rc hwf hsess hparse hmatch,
      rfl⟩,
    observe_runAns_pqRecv_matchingPathB (cliRunSemPathB X W) X WP scopeIn
      rfl rfl encodeInjOn_scopeIn_placed (ratchetScopeCoversPq_scopeIn_placed WP)
      st x g body pm rc hwf hsess hparse hmatch,
    commitOk_pqRecvPrekey_decPkDef (S := cliRunSemPathB X W) (X := X) (W := WP)
      (Scope := scopeIn) rfl st body rc⟩

/-- Parametric D3 matching-session Path-B `decrypt_prekey` slot allocation envelope
(`cliDecryptPrekey` wrapper prologue/epilogue is stack-only, so the slot envelope equals
`MatchingPathBPollEnv`). -/
def DecPkD3MatchingPathBEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  MatchingPathBPollEnv A W B ReadEnv DeserEnv kitEnv4 tdEnv g

/-- `ReadEnv`-parametric CLI specialization of `DecPkD3MatchingPathBEnv` wired to
`SessDeserializeCancelEnv` and `cliPollSessBudgetEnv`. -/
abbrev DecPkD3MatchingPathBOfReadEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  DecPkD3MatchingPathBEnv A W B ReadEnv SessDeserializeCancelEnv
    (fun F0 peer =>
      cliPollSessBudgetEnv A F0 peer (cliKitStk B) SessDeserializeCancelEnv ReadEnv)
    tdEnv g

/-- Concrete CLI specialization of `DecPkD3MatchingPathBEnv` wired to `ReadFileRuleEnv cliIo.rd`,
`SessDeserializeCancelEnv`, and `cliPollSessBudgetEnv`. -/
def DecPkD3MatchingPathBCliEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (g : DecPkGhost) : List AllocEvent → Prop :=
  DecPkD3MatchingPathBOfReadEnv A W B (ReadFileRuleEnv cliIo.rd) tdEnv g

/-! ## 2. Block-`520` Slot Theorems & Block-`617` `mainSpecTightPlacedAt` Lift -/

/-- Caller-block (`i < 619`) budget-threaded `decPkSlotSpecPlaced` reduction for matching-session
Path-B `decrypt_prekey` (`lsmpl.base 520`). -/
theorem cliDecryptPrekey_slot_matchingPathB_placedBudget_at_block [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3MatchingPathBEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced A lim DecPkEnv S stk) := by
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
    rw [withPanics_cliGhostExterns_eq mmpl gh W]
    exact hcaller
  exact dpSlot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
      (K₀_statePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' h1 h2 => by
        rw [withPanics_cliGhostExterns_eq mmpl gh W]
        exact decPk_matchingPathB_poll_placedBudget A lim ReadEnv DeserEnv tdEnv DecPkEnv
          hStageP3 hDropNz mmpl gh W X B S Scope
          (toSkeletonRunHooks hh) hRead hDeser hSkit hTryDec hinjK hsub hS hok hevs_sub
          stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

/-- Pointwise `(mkSlot (decPkSlotSpecPlaced ...) needs.decryptPrekey).OkPlaced` wrapper on any
caller block `i < 619`. -/
theorem cliDecryptPrekey_slotOk_matchingPathB_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3MatchingPathBEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv g evs →
      DecPkEnv g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_matchingPathB_placedBudget_at_block A lim B mmpl gh W hi X S Scope
      hDropNz hh hRead hDeser hSkit hStageP3 hTryDec hinjK hsub hS hok hevs_sub
      stk (hneed ▸ h1) h2

/-- Parametric block-`520` slot contract
`(slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced` on
`lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))` for any `S.decPkOk` implying
`DecPkOkPathB`. -/
theorem decPkPathBSlotOk_full_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv
        (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk cliRunBudgets_placed))}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk cliRunBudgets_placed))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBEnv A.repAlloc W cliRunBudgets_placed ReadEnv DeserEnv kitEnv4 tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_matchingPathB_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim cliRunBudgets_placed mmpl gh W (by decide) X S scopeIn needs
    h547 hh hRead hDeser hSkit hStageP3 hTryDec
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv hneed

/-- Specializes `decPkPathBSlotOk_full_placedBudget` to `DecPkD3MatchingPathBOfReadEnv`,
discharging `hSkit` internally via `cliPollSess_kitPlacedOkSE`. -/
theorem decPkPathBSlotOk_full_of_readEnv_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBOfReadEnv A.repAlloc W cliRunBudgets_placed ReadEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkPathBSlotOk_full_placedBudget X mmpl gh W h547 hh hRead hDeser
    (fun F0 peer => cliPollSess_kitPlacedOkSE mmpl gh W cliRunBudgets_placed F0 peer h547 hh hRead hDeser)
    hStageP3 hTryDec S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Concrete CLI specialization of `decPkPathBSlotOk_full_of_readEnv_placedBudget` at
`DecPkD3MatchingPathBCliEnv`. -/
theorem decPkPathBSlotOk_full_cli_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile
        (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBCliEnv A.repAlloc W cliRunBudgets_placed tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkPathBSlotOk_full_of_readEnv_placedBudget X mmpl gh W h547 hh hRead hDeser
    hStageP3 hTryDec S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Lifts `decPkPathBSlotOk_full_cli_placedBudget` onto `SpecsPlacedBudget.mainSpecTightPlacedAt`
(block `617`) over the `CliPqOrD3RecvInputs` scoped relation at `cliRunSemPathB X W`. -/
theorem main_ok_cli_matchingPathB_tight_placed_at [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {prog617 : Program}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile
        (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBCliEnv A.repAlloc W cliRunBudgets_placed tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed)
    (hMainLift :
      (slotsOfPlaced A lim sEnvs (cliRunSemPathB X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok prog617 (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
          (fun i a =>
            (CliPqxdhInputs ⟨W.C, W.Q⟩ i ∨
              ∃ (stP : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
                PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ stP ∧ i = pqRecvInputs ⟨W.C, W.Q⟩ stP ct rc) ∧
            runRel (cliRunSemPathB X W) i a))) :
    subroutine_ok prog617 (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
        (fun i a =>
          (CliPqxdhInputs ⟨W.C, W.Q⟩ i ∨
            ∃ (stP : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
              PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ stP ∧ i = pqRecvInputs ⟨W.C, W.Q⟩ stP ct rc) ∧
          runRel (cliRunSemPathB X W) i a)) :=
  hMainLift
    (decPkPathBSlotOk_full_cli_placedBudget X mmpl gh W h547 hh hRead hDeser hStageP3 hTryDec
      (cliRunSemPathB X W) sEnvs needs hsEnv rfl rfl (fun _ _ _ _ h => h) hneed)

/-- Companion `mainSpecTightPlacedAt` lift at `cliRunSemPathBFull X W`. -/
theorem main_ok_cli_matchingPathBFull_tight_placed_at [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {prog617 : Program}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile
        (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hStageP3 : StageP3PrevEmptyVRegsPlacedStmt)
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBCliEnv A.repAlloc W cliRunBudgets_placed tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed)
    (hMainLift :
      (slotsOfPlaced A lim sEnvs (cliRunSemPathBFull X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok prog617 (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
          (fun i a =>
            (CliPqxdhInputs ⟨W.C, W.Q⟩ i ∨
              ∃ (stP : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
                PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ stP ∧ i = pqRecvInputs ⟨W.C, W.Q⟩ stP ct rc) ∧
            runRel (cliRunSemPathBFull X W) i a))) :
    subroutine_ok prog617 (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
        (fun i a =>
          (CliPqxdhInputs ⟨W.C, W.Q⟩ i ∨
            ∃ (stP : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
              PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ stP ∧ i = pqRecvInputs ⟨W.C, W.Q⟩ stP ct rc) ∧
          runRel (cliRunSemPathBFull X W) i a)) :=
  hMainLift
    (decPkPathBSlotOk_full_cli_placedBudget X mmpl gh W h547 hh hRead hDeser hStageP3 hTryDec
      (cliRunSemPathBFull X W) sEnvs needs hsEnv rfl rfl (fun _ _ _ _ h => h.2) hneed)

/-! ## 3. `SingleSlotFineSpec`, Slot-Cap Bounds, `W4RecvPrekeyRealDomOf`, & Envelope Inclusion -/

theorem phaseCredit_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

/-- Existential Variant (i) W4 real-slot envelope (`(sessionCapBytes, msgCapBytes)`). -/
def MatchingPathBRealSlotEnv (evs : List AllocEvent) : Prop :=
  ∃ w4R : W4RecvPrekeyRealParams,
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs

def decPkD3MatchingPathBCum : Nat := w4RecvPrekeyReal1MiB_i_Cum
def decPkD3MatchingPathBLive : Nat := w4RecvPrekeyReal1MiB_i_Live
def decPkD3MatchingPathBPeak : Nat := w4RecvPrekeyReal1MiB_i_Peak
def decPkD3MatchingPathBMaxReq : Nat := w4RecvPrekeyReal1MiB_i_MaxReq
def decPkD3MatchingPathBGrpS : Nat := w4RecvPrekeyRealGrpS

/-- `SingleSlotFineSpec` for `MatchingPathBRealSlotEnv`. -/
def decPkD3MatchingPathBReal_singleSlotFineSpec :
    SingleSlotFineSpec MatchingPathBRealSlotEnv where
  cum := decPkD3MatchingPathBCum
  live := decPkD3MatchingPathBLive
  peak := decPkD3MatchingPathBPeak
  maxReq := decPkD3MatchingPathBMaxReq
  grpS := decPkD3MatchingPathBGrpS
  credit := phaseCredit_exists_guarded_u fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).credit
  live_le_peak := w4RecvPrekeyReal1MiB_i_eq.2.2.2.2
  groups := phaseGroupSpec_exists_guarded fineCostModel fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).groups

/-- Closed inequalities bounding `MatchingPathBRealSlotEnv` within Variant (i) of the `1 MiB`
`recv` pre-key slot caps (`w4RecvPrekeyReal1MiB_i_*`, `w4RecvPrekeyRealGrpS`). -/
theorem decPkD3MatchingPathB_caps_le :
    decPkD3MatchingPathBLive ≤ decPkD3MatchingPathBPeak ∧
    decPkD3MatchingPathBCum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
    decPkD3MatchingPathBLive ≤ w4RecvPrekeyReal1MiB_i_Live ∧
    decPkD3MatchingPathBPeak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
    decPkD3MatchingPathBMaxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
    decPkD3MatchingPathBGrpS ≤ w4RecvPrekeyRealGrpS :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `PeerSpqrStateTight640` on `CliPqOrD3RecvInputs` (`CliPqxdhInputs` or `pqRecvInputs` of a
spec-domain party). -/
theorem peerSpqrStateTight640_of_cliPqOrD3Recv {P : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 P.C.F P.Q.K (runFiles i) (addrValOf peer) := by
  rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
  · exact peerSpqrStateTight640_of_cliPqInputs_recv hPq hparse
  · exact peerSpqrStateTight640_of_pqRecv_wf hwf hparse

/-- Establishes `W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes` from
`parseArgs = some (.recv peerAddr)` and `cliIo_rd_ok_length_le_sessionCapBytes`. -/
theorem w4RecvPrekeyRealDomOf_matchingPathB {i : Inputs} {peerAddr : AddrV}
    (R : W4RecvPrekeyRealParams)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hrd : R.rd = cliIo.rd)
    (hfiles : R.files = runFiles i)
    (hkpk : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hpeer : R.peer.val = addrValOf peerAddr)
    (hownKey : R.ownKeyName.length ≤ 64)
    (hownReg : R.ownRegName.length ≤ 64)
    (hkpkMark : R.kpkMarkName.length ≤ 64)
    (hresOld : R.x_res.cap.toNat ≤ 4096)
    (hresNew : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096)
    (hspqrKey : R.x_spqr.p.authKey.length ≤ 32)
    (hcurF : R.hasCurSession = false)
    (htrials : R.archivedTrials = [])
    (harchValid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (harchEnc : (encodeRecord R.r_arch).length ≤ 2097152)
    (hout0Valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hout0Enc : (encodeRecord R.r_out0).length ≤ 2097152)
    (hout1 : FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1)
    (htdB : R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B)
    (hacF : R.isPathAC = false) :
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
      cur_dom := Or.inl (fun evs hevs => by
        change (if R.hasCurSession then _ else fun _ => False) evs at hevs
        rw [hcurF] at hevs
        exact hevs)
      arch_valid := harchValid
      arch_enc := harchEnc
      out0_valid := hout0Valid
      out0_enc := hout0Enc
      out1_freshBob := hout1
      trials_len4 := by simp [mkW4RecvPrekeySlotParams, htrials] }
  cur_fail_dom hcs := by rw [hcurF] at hcs; cases hcs
  trials_dom x hx := by rw [htrials] at hx; cases hx
  tdB_dom := htdB
  tdAC_dom hac := by rw [hacF] at hac; cases hac

/-- Concrete allocating non-vacuity witness (`evs = rustAllocEvents 24 8 ≠ []`) for
`MatchingPathBRealSlotEnv` given any `W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R`. -/
theorem matchingPathBRealSlotEnv_nonvacuous_alloc
    {R : W4RecvPrekeyRealParams} (hDom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ MatchingPathBRealSlotEnv evs := by
  obtain ⟨evs, hne, hevs⟩ := w4RecvPrekeyRealEnv_nonvacuous_alloc R
  exact ⟨evs, hne, R, hDom, hevs⟩

/-- Embeds `DecPkD3MatchingPathBCliEnv` into `MatchingPathBRealSlotEnv`
(`∃ w4R, W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs`). -/
theorem decPkD3MatchingPathBEnv_mem_matchingPathBRealSlotEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st ∧ g.i = pqRecvInputs ⟨W.C, W.Q⟩ st ct rc)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (_hfiles : x.F = runFiles g.i)
    (_hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3MatchingPathBCliEnv A W B tdEnv x evs →
        ∃ R : W4RecvPrekeyRealParams,
          R.rd = cliIo.rd ∧
          R.files = runFiles g.i ∧
          (R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort) ∧
          R.peer.val = addrValOf peerAddr ∧
          R.ownKeyName.length ≤ 64 ∧
          R.ownRegName.length ≤ 64 ∧
          R.kpkMarkName.length ≤ 64 ∧
          R.x_res.cap.toNat ≤ 4096 ∧
          reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096 ∧
          R.x_spqr.p.authKey.length ≤ 32 ∧
          R.hasCurSession = false ∧
          R.archivedTrials = [] ∧
          (∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
            SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
          (encodeRecord R.r_arch).length ≤ 2097152 ∧
          (∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
            SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
          (encodeRecord R.r_out0).length ≤ 2097152 ∧
          FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1 ∧
          (R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B) ∧
          R.isPathAC = false ∧
          W4RecvPrekeyRealEnv R evs) :
    ∀ evs, DecPkD3MatchingPathBCliEnv A W B tdEnv x evs →
      MatchingPathBRealSlotEnv evs := by
  intro evs hevs
  have hTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) :=
    peerSpqrStateTight640_of_cliPqOrD3Recv hi hparse
  obtain ⟨R, hrd, hRfiles, hkpk, hRpeer, hownK, hownR, hkpkM, hresO, hresN, hspqrK,
    hcurF, htrials, harchV, harchE, hout0V, hout0E, hout1, htdB, hacF, hRenv⟩ :=
    hStageP3Bridge hTight hstdin evs hevs
  exact ⟨R, w4RecvPrekeyRealDomOf_matchingPathB R hparse hrd hRfiles hkpk hRpeer
    hownK hownR hkpkM hresO hresN hspqrK hcurF htrials harchV harchE
    hout0V hout0E hout1 htdB hacF, hRenv⟩

/-- Embeds `DecPkD3MatchingPathBCliEnv` into the mode-dispatched `.decPkEnv` of
`mkExistentialRealCalleeEnvs img S ⟨W.C, W.Q⟩ g`. -/
theorem decPkD3MatchingPathBEnv_mem_w4RecvPrekeyRealEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost}
    (hc : g.c = .recv peerAddr)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st ∧ g.i = pqRecvInputs ⟨W.C, W.Q⟩ st ct rc)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (hfiles : x.F = runFiles g.i)
    (hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3MatchingPathBCliEnv A W B tdEnv x evs →
        ∃ R : W4RecvPrekeyRealParams,
          R.rd = cliIo.rd ∧
          R.files = runFiles g.i ∧
          (R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort) ∧
          R.peer.val = addrValOf peerAddr ∧
          R.ownKeyName.length ≤ 64 ∧
          R.ownRegName.length ≤ 64 ∧
          R.kpkMarkName.length ≤ 64 ∧
          R.x_res.cap.toNat ≤ 4096 ∧
          reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096 ∧
          R.x_spqr.p.authKey.length ≤ 32 ∧
          R.hasCurSession = false ∧
          R.archivedTrials = [] ∧
          (∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
            SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
          (encodeRecord R.r_arch).length ≤ 2097152 ∧
          (∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
            SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
          (encodeRecord R.r_out0).length ≤ 2097152 ∧
          FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1 ∧
          (R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B) ∧
          R.isPathAC = false ∧
          W4RecvPrekeyRealEnv R evs) :
    ∀ evs, DecPkD3MatchingPathBCliEnv A W B tdEnv x evs →
      (match g.c with | .recv _ => MatchingPathBRealSlotEnv | _ => fun _ => False) evs := by
  intro evs hevs
  have hmem := decPkD3MatchingPathBEnv_mem_matchingPathBRealSlotEnv A W B hi hstdin hparse
    hfiles hpeer hStageP3Bridge evs hevs
  rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
  dsimp only at hc
  subst hc
  exact hmem

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget
