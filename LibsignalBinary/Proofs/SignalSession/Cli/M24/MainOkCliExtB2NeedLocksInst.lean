/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseFailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstNoMatch
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Block `579 → 617` Lift and `MainOkCliExt*B2NeedLocksPlacedAt` Constructors

Lifts Block-`579` `runSpecTightPlaced` contracts to `b2MainSpecTightNeedLocksFineAt` on Block
`617` via `pqScopedRun` and `B2MainRemainingHops`, proves PQXDH and `NoMatch` clause agreement for
`cliRunSemD2c_placed`, and assembles `MainOkCliExtPqB2NeedLocksPlacedAt` and
`MainOkCliExtOverB2NeedLocksPlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey wireWhisper)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs MainOkNoMatchClause OutcomeMatchesModelExceptPath PqParty
   PqSessionMatches PqxdhPartyInSpecDomain cliPqInputs_init cliPqInputs_recvBad
   cliPqInputs_recvPrekey cliPqInputs_recvWhisper cliPqInputs_send
   cliProcessInputs filesOf libsignalSessionLib observe partyAddress pqInitInputs pqInitModel
   pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel
   pqxdhExpectedOutcome preKeyMsgE_bytes_lt_2_32 sessionFile stdinCapBytes strlenHook)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk IsSendOverCap MainResult RunAnswer StoresGhost
   cliInputs cliStaticsPlaced utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced AtM1EndPlaced AtM4EndPlaced AtM4EndTightPlaced AtM4Placed AtM6Placed CallV
   CallW DomainArgv HistOkTight LsCodeInv RunCall argsBuf callCellsPlaced callHeap cliHookStack
   cliIo cliIo_coins cliIo_coinsPath cliIo_commit cliIo_stdin cliMainStk cliResStack
   cliRunSemD2c cliWrOk cli_hstk cli_hstk64 coinsOf commitFiles
   commitOk_pqInit_initDef_placed commitOk_pqRecvBad_placed
   commitOk_pqRecvWhisper_decSigDef_placed commitOk_pqSend_encDef_placed domainArgv_pqInit
   domainArgv_pqRecv domainArgv_pqSend encodeInjOn_scopeIn_placed hparse_of_domains inputOf locals
   m4CellsPlaced m5CellsPlaced m6CellsPlaced mProgPlaced mainFrameSize mainLitsBlk617 mainOom
   mainSaved namedWrites ownedBytes parseArgs ratchetScopeCoversPq_scopeIn_placed
   runFilesOk_pqInit_cli_placed runFilesOk_pqRecv_cli_placed runFilesOk_pqSend_cli_placed
   runHsOk_pqInit_cli_placed runHsOk_pqRecvOther_cli_placed runHsOk_pqSend_cli_placed)
open CryptoVerification.SignalSession.Cli.RunCompose
  (RunSem runAns runRel runRel_dom)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c InitOk₀ PksmTyped commitOk_pqRecvPrekey_decPkDefD2c decPkDefD2c decSigDef
   encDef initDef pksmParseAgrees_S0 pksmTyped_S0 pqDecryptPrekeyAgrees_decPkDefD2c
   pqDecryptSignalAgrees_decSigDef pqEncryptAgrees_encDef
   runAns_pqRecvPrekey_noMatch_exact runAns_pqRecvPrekey_noMatch_exceptNorm
   runHsOk_pqRecvPrekey_d2c)
open CryptoVerification.SignalSession.Cli.RunProofs.InitS0 (pqInitiateAgrees_initDef_proof)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine
  (PksmParseAgrees PqDecryptPrekeyAgrees PqDecryptSignalAgrees PqEncryptAgrees
   PqInitiateAgrees runAns_pqInit runAns_pqRecvBad runAns_pqRecvPrekey runAns_pqRecvWhisper
   runAns_pqSend runBounds_pqInit runBounds_pqRecv runBounds_pqSend)
open CryptoVerification.SignalSession.Cli.Slots
  (encOk₀ filesOk₀ runEncOk_pqInit runEncOk_pqRecv runEncOk_pqSend scopeIn)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Heap.Fine
  (FineBudget fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
  (argvAtROP fineHook_b2_main_ok_tight_needLocks_with_inv_placed_lsmpl libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (strlen_ro_placed_ok_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt
   b2MainSpecTightNeedLocksFineAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudget
  (main_m1_ro_pool_placed_step1)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced runSpecPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

abbrev MainOkNoMatchClausePlaced := MainOkNoMatchClause
noncomputable abbrev cliRunSemD2c_placed := cliRunSemD2c

noncomputable abbrev _root_.CryptoVerification.SignalSession.Cli.MainHops.cliRunSemD2c_placed :
    UnreachedPqxdhPrimitives → CliHooks → RunSem :=
  cliRunSemD2c

abbrev _root_.CryptoVerification.SignalSession.MainOkNoMatchClausePlaced :
    PEParams → UnreachedPqxdhPrimitives → (Inputs → RunAnswer → Prop) → PqParty → Prop :=
  MainOkNoMatchClause

/-! ## `pqScopedRun` and `runSpecTightPlaced` monotonicity -/

theorem cliProcessInputs_eq_cliInputs (i : Inputs) :
    cliProcessInputs i = cliInputs i :=
  rfl

theorem initFsState_cliProcessInputs_eq (i : Inputs) :
    initFsState (cliProcessInputs i) = initFsState (cliInputs i) :=
  rfl

theorem mainFrameSize_le_cliMainStk : mainFrameSize ≤ cliMainStk := by
  decide

/-- Scope `Run₀` to `CliPqxdhInputs WP`. -/
def pqScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop)
    (i : Inputs) (a : RunAnswer) : Prop :=
  CliPqxdhInputs WP i ∧ Run₀ i a

theorem pqScopedRun_dom {WP : PEParams} {S : RunSem} {i : Inputs} {a : RunAnswer}
    (hr : pqScopedRun WP (runRel S) i a) : DomainArgv i :=
  runRel_dom hr.2

/-- Contravariant weakening of `Run` in `runSpecTightPlaced`. -/
theorem subroutine_ok_runSpecTightPlaced_mono_run [LibsignalPlacement]
    {P : Program} {e : BitVec 64} {M : AllocCostModel} {CodeOk : Memory → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run₁ Run₂ : Inputs → RunAnswer → Prop}
    {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (himp : ∀ i a, Run₁ i a → Run₂ i a)
    (h : subroutine_ok P e
      (runSpecTightPlaced CodeOk A lim RunEnv uuidParse Run₂ wrOk resStack)) :
    subroutine_ok P e
      (runSpecTightPlaced CodeOk A lim RunEnv uuidParse Run₁ wrOk resStack) := by
  refine subroutine_ok_mono h
    (fun ⟨g, st⟩ R s0 hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => he)
    (fun _ _ _ _ ho => ho)
  simp only [runSpecTightPlaced, runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, himp g.i g.a hp.1.2.1, hp.1.2.2⟩, hp.2⟩

/-! ## `B2MainRemainingHops` and Block `579 → 617` lifts -/

/-- Block-`617` hop obligations (`step2`..`step6`) at `io := cliIo` and `stk := cliMainStk` for
`fineHookRustCliAllocBudget`. -/
structure B2MainRemainingHops [LibsignalPlacement]
    (CodeOk : Memory → Prop) (mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (W : CliHooks)
    (brkStart : BitVec 64) (lim : BudgetLimits) (γ : GhostName) (tp : BitVec 64)
    (St1 : Inputs → FineBudget → Prop)
    (St2 : Inputs → CallV → FineBudget → Prop)
    (St3 : Inputs → CallV → FineBudget → Prop)
    (St4 : Inputs → CallV → StoresGhost → FineBudget → Prop)
    (St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop)
    (RunEnv : RunCall → List AllocEvent → Prop)
    (Run : Inputs → RunAnswer → Prop) : Prop where
  step2 : ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {st1 : FineBudget} {Statics : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
    St1 i st1 →
    CliInputsOk i → i.argv ≠ [] →
    ps.map (·.2) = i.argv.map bytesOfString →
    AtM1EndPlaced CodeOk s0 s i.argv.length buf →
    (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
    ExitKPoolPlaced CodeOk (ext W) A lim s0 cliMainStk
      (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
    (∀ (s' : State) (w : CallW) (c : CallV) (st2 : FineBudget),
      St2 i c st2 →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
          A.pool lim st2 s' ∗ Statics)
        Q Qp oom) →
    ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
        A.pool lim st1 s ∗ Statics)
      Q Qp oom
  step3 : ∀ {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {st2 : FineBudget}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
    St2 i c st2 →
    s0.fs = initFsState (cliInputs i) → s0.trace = [] →
    cliIo.stdin (initFsState (cliInputs i)) = some i.stdin →
    cliIo.pathOk (utf8 "coins") →
    (∀ r, cliIo.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)) →
    parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
    AtCallPlaced CodeOk s0 s w i.argv.length buf →
    (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
    ExitKPoolPlaced CodeOk (ext W) A lim s0 cliMainStk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp →
    (∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64) (st3 : FineBudget),
      St3 i c st3 →
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
          A.pool lim st3 s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) →
    ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
      (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
        A.pool lim st2 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom
  step4_overCap : ∀ {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
    {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {st3 : FineBudget}
    {Q Qp : State → SepProp → Prop},
    let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
    St3 i (.send peer) st3 →
    cliMainStk ≤ s0.sp.toNat →
    s0.trace = [] →
    parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
    1_000_000 < i.stdin.length →
    AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap →
    (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
    ExitKPoolPlaced CodeOk (ext W) A lim s0 cliMainStk
      (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        s'.trace = s.trace) Q Qp →
    ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
          (inputOf i (.send peer)) ∗
        callHeap A.repAlloc w (.send peer) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
        A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0)
  step4_call :
    let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
    subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A lim RunEnv uuidTryParse Run cliWrOk cliResStack) →
    ∀ {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : FineBudget}
      {Q Qp : State → SepProp → Prop},
      St3 i c st3 →
      cliMainStk ≤ s0.sp.toNat →
      s0.trace = [] →
      Run i a → ¬ IsSendOverCap i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf) →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 cliMainStk
        (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
          s.trace <+: s'.trace) Q Qp →
      (∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st4 : FineBudget),
        St4 i c g st4 →
        a = some (some (namedWrites g.writes, out)) →
        (∀ pw ∈ g.writes, cliIo.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) → s.trace <+: s'.trace →
        AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
        ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
            A.pool lim st4 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0)
  step5 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {out : List (BitVec 8)}
    {s0 s : State} {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {st4 : FineBudget} {Q Qp : State → SepProp → Prop},
    let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
    St4 i c g st4 →
    s0.trace = [] →
    (∀ pw ∈ g.writes, cliIo.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
    AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap →
    (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
    (∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64) (st5 : FineBudget),
      St5 i c g ok st5 →
      (match commitFiles cliIo.wr s.fs.files g.writes with
       | some F => ok = true ∧ s'.fs.files = F
       | none => ok = false) →
      s.trace <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      AtM6Placed CodeOk s0 s' ok i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
          A.pool lim st5 s' ∗ anyHeap)
        Q Qp (mainOom s0)) →
    ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
        A.pool lim st4 s ∗ anyHeap)
      Q Qp (mainOom s0)
  step6 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {s0 s : State} {ok : Bool}
    {buf outCap outPtr inCap inPtr : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))} {st5 : FineBudget}
    {Q Qp : State → SepProp → Prop},
    let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
    St5 i c g ok st5 →
    AtM6Placed CodeOk s0 s ok i.argv.length buf →
    ExitKPoolPlaced CodeOk (ext W) A lim s0 cliMainStk
      (fun code s' => s'.fs.files = s.fs.files ∧
        (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
            ProcessOutcome.traceStreamBytes .stdout s'.trace =
            ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
         else code = 2 ∧ s'.trace = s.trace)) Q Qp →
    ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
            (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (cliMainStk - mainFrameSize) ∗
        A.pool lim st5 s ∗ anyHeap)
      Q Qp (mainOom s0)

/-- Lift Block-`579` `runSpecTightPlaced` and `B2MainRemainingHops` to
`b2MainSpecTightNeedLocksFineAt` on Block `617`. -/
theorem b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop} {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstrlen_row : ext W "strlen" = some strlenHook)
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv Run) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  fineHook_b2_main_ok_tight_needLocks_with_inv_placed_lsmpl
    (io := cliIo) (St0 := St0) (St1 := St1) (St2 := St2) (St3 := St3) (St4 := St4) (St5 := St5)
    hlibc
    ⟨cliIo_stdin, cliIo_coinsPath, cliIo_coins, cliIo_commit⟩
    hfs_eq
    hparse
    mainFrameSize_le_cliMainStk
    hSt0
    (fun hst0 hs0 hok hpan hexit hnext =>
      main_m1_ro_pool_placed_step1 hc_alloc
        (strlen_ro_placed_ok_of_hooks (hookStack := cliHookStack) hstrlen_row)
        cli_hstk cli_hstk64 hSt01 hst0 hs0 hok hpan hexit hnext)
    hhops.step2
    hhops.step3
    hhops.step4_overCap
    (hhops.step4_call hrun)
    hhops.step5
    hhops.step6

theorem b2MainSpecTightNeedLocksFineAt_of_runSem_lsmpl [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlen_row : ext W "strlen" = some strlenHook)
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv (runRel S)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) (runRel S) inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
    hlibc hfs_eq (hparse_of_domains fun _ _ hr => runRel_dom hr)
    hstrlen_row hc_alloc hSt0 hSt01 hrun hhops

theorem b2MainSpecTightNeedLocksFineAt_of_runSem_placed
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlen_row : ext W "strlen" = some strlenHook)
    (hc_alloc : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp St1 St2 St3 St4 St5 RunEnv (runRel S)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) (runRel S) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_runSem_lsmpl S
    hlibc hfs_eq hstrlen_row hc_alloc hSt0 hSt01 hrun hhops

theorem b2MainSpecTightNeedLocksFineAt_of_pqScopedRunSem_lsmpl [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (WP : PEParams) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlen_row : ext W "strlen" = some strlenHook)
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv (pqScopedRun WP (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (pqScopedRun WP (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
    hlibc hfs_eq (hparse_of_domains fun _ _ hr => pqScopedRun_dom hr)
    hstrlen_row hc_alloc hSt0 hSt01
    (subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun)
    hhops

theorem b2MainSpecTightNeedLocksFineAt_of_pqScopedRunSem_placed
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (WP : PEParams) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlen_row : ext W "strlen" = some strlenHook)
    (hc_alloc : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp St1 St2 St3 St4 St5 RunEnv
      (pqScopedRun WP (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (pqScopedRun WP (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_pqScopedRunSem_lsmpl WP S
    hlibc hfs_eq hstrlen_row hc_alloc hSt0 hSt01 hrun hhops

/-! ## PQXDH and `NoMatch` clause agreement -/

/-- Establish the 5 `CliSpecPqxdh` clauses and `MainOkNoMatchClausePlaced` on
`pqScopedRun ⟨W.C, W.Q⟩ (runRel S)`. -/
theorem pqScopedRunSem_pqxdh_and_noMatch_clauses_placed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (S : RunSem)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hS_init : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hS_decPk : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (hS_pksm : S.pksmParse = pksmParse)
    (hS_files : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hS_encOk : S.encOk = encOk₀ scopeIn)
    (hS_initOk : S.initOk = InitOk₀ ⟨W.C, W.Q⟩)
    (hS_decPkOk : S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let Run := pqScopedRun WP (runRel S)
    ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
      (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
        st.session = none →
        ∃ a, Run (pqInitInputs WP st b t) a ∧
          observe (pqInitInputs WP st b t).files a =
            pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
          CommitOk (pqInitInputs WP st b t) (MainResult.ofAnswer a)) ∧
      (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
        ∃ a, Run (pqSendInputs WP st m r) a ∧
          observe (pqSendInputs WP st m r).files a =
            pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
          CommitOk (pqSendInputs WP st m r) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
          observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
              (pqRecvWhisperModel WP st c rc) ∧
          CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
      (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
          observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (pqRecvPrekeyModel X WP st m rc) ∧
          CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
        ∃ a, Run (pqRecvInputs WP st c rc) a ∧
          observe (pqRecvInputs WP st c rc).files a =
            .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
          CommitOk (pqRecvInputs WP st c rc) (MainResult.ofAnswer a)) ∧
      MainOkNoMatchClausePlaced WP X Run st := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hcovPq := ratchetScopeCoversPq_scopeIn_placed WP
  have hagInit : PqInitiateAgrees S X WP := pqInitiateAgrees_initDef_proof S X WP hS_init
  have hagEnc : PqEncryptAgrees S WP :=
    pqEncryptAgrees_encDef S WP scopeIn hS_enc encodeInjOn_scopeIn_placed hcovPq
  have hagDec : PqDecryptSignalAgrees S WP :=
    pqDecryptSignalAgrees_decSigDef S WP scopeIn hS_dec encodeInjOn_scopeIn_placed hcovPq
  have hagPksm : PksmParseAgrees S := pksmParseAgrees_S0 hS_pksm
  have hpksmT : PksmTyped S := pksmTyped_S0 hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X WP :=
    pqDecryptPrekeyAgrees_decPkDefD2c S X WP scopeIn hS_decPk hpksmT
      encodeInjOn_scopeIn_placed hcovPq
  intro st hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact ⟨runAns S (pqInitInputs WP st b t),
      ⟨cliPqInputs_init b t hst hnone,
        ⟨domainArgv_pqInit WP st b t, runBounds_pqInit WP st b t,
          runFilesOk_pqInit_cli_placed (S := S) hS_files WP st b t hst,
          runEncOk_pqInit S WP st b t,
          runHsOk_pqInit_cli_placed (S := S) (W := WP) hS_initOk st b t hst hnone, rfl⟩⟩,
      runAns_pqInit S X WP hagInit st b t hst hnone,
      commitOk_pqInit_initDef_placed (S := S) (X := X) (W := WP) hS_init st b t⟩
  · intro m r hm
    exact ⟨runAns S (pqSendInputs WP st m r),
      ⟨cliPqInputs_send m r hst hm,
        ⟨domainArgv_pqSend WP st m r, runBounds_pqSend WP st m r hm,
          runFilesOk_pqSend_cli_placed (S := S) hS_files WP st m r hst,
          runEncOk_pqSend (S := S) hS_encOk WP st m r,
          runHsOk_pqSend_cli_placed S WP st m r, rfl⟩⟩,
      runAns_pqSend S WP hagEnc st m r hst hm,
      commitOk_pqSend_encDef_placed (S := S) (W := WP) hS_enc st m r⟩
  · intro c rc hc
    have hnot3 : (wireWhisper :: c).head? ≠ some wirePrekey := by simp [wireWhisper, wirePrekey]
    exact ⟨runAns S (pqRecvInputs WP st (wireWhisper :: c) rc),
      ⟨cliPqInputs_recvWhisper c rc hst hc,
        ⟨domainArgv_pqRecv WP st (wireWhisper :: c) rc,
          runBounds_pqRecv WP st (wireWhisper :: c) rc (Nat.succ_le_of_lt hc),
          runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wireWhisper :: c) rc hst,
          runEncOk_pqRecv S WP st (wireWhisper :: c) rc,
          runHsOk_pqRecvOther_cli_placed S WP st (wireWhisper :: c) rc hnot3, rfl⟩⟩,
      runAns_pqRecvWhisper S WP hagDec st c rc hst hc,
      commitOk_pqRecvWhisper_decSigDef_placed (S := S) (W := WP) hS_dec st c rc⟩
  · intro m rc hm hmatch
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨cliPqInputs_recvPrekey m rc hst hm,
        ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
          runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
          runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
          runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
          runHsOk_pqRecvPrekey_d2c hS_decPkOk hS_pksm st m rc hst hm, rfl⟩⟩,
      runAns_pqRecvPrekey S X WP hagPksm hagDecPk st m rc hst hm hmatch,
      commitOk_pqRecvPrekey_decPkDefD2c hS_decPk st m.bytes rc⟩
  · intro c rc hc h2 h3
    refine ⟨runAns S (pqRecvInputs WP st c rc),
      ⟨cliPqInputs_recvBad c rc hst hc h2 h3,
        ⟨domainArgv_pqRecv WP st c rc,
          runBounds_pqRecv WP st c rc (Nat.le_of_lt hc),
          runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st c rc hst,
          runEncOk_pqRecv S WP st c rc,
          runHsOk_pqRecvOther_cli_placed S WP st c rc h3, rfl⟩⟩,
      ?_, commitOk_pqRecvBad_placed S WP st c rc h2 h3⟩
    rw [runAns_pqRecvBad S WP st c rc h2 h3]
    rfl
  · intro x₀ g₀ m rc hs hm hnot
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨cliPqInputs_recvPrekey m rc hst hm,
        ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
          runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
          runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
          runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
          runHsOk_pqRecvPrekey_d2c hS_decPkOk hS_pksm st m rc hst hm, rfl⟩⟩,
      runAns_pqRecvPrekey_noMatch_exact S X WP scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn_placed hcovPq st x₀ g₀ m rc hst hs hm hnot,
      runAns_pqRecvPrekey_noMatch_exceptNorm S X WP scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn_placed hcovPq st x₀ g₀ m rc hst hs hm hnot,
      commitOk_pqRecvPrekey_decPkDefD2c hS_decPk st m.bytes rc⟩

theorem runSem_pqxdh_and_noMatch_clauses_placed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (S : RunSem)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hS_init : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hS_decPk : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (hS_pksm : S.pksmParse = pksmParse)
    (hS_files : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hS_encOk : S.encOk = encOk₀ scopeIn)
    (hS_initOk : S.initOk = InitOk₀ ⟨W.C, W.Q⟩)
    (hS_decPkOk : S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let Run := runRel S
    ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
      (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
        st.session = none →
        ∃ a, Run (pqInitInputs WP st b t) a ∧
          observe (pqInitInputs WP st b t).files a =
            pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
          CommitOk (pqInitInputs WP st b t) (MainResult.ofAnswer a)) ∧
      (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
        ∃ a, Run (pqSendInputs WP st m r) a ∧
          observe (pqSendInputs WP st m r).files a =
            pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
          CommitOk (pqSendInputs WP st m r) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
          observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
              (pqRecvWhisperModel WP st c rc) ∧
          CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
      (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
          observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (pqRecvPrekeyModel X WP st m rc) ∧
          CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
        ∃ a, Run (pqRecvInputs WP st c rc) a ∧
          observe (pqRecvInputs WP st c rc).files a =
            .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
          CommitOk (pqRecvInputs WP st c rc) (MainResult.ofAnswer a)) ∧
      MainOkNoMatchClausePlaced WP X Run st := by
  dsimp only
  have hsc := pqScopedRunSem_pqxdh_and_noMatch_clauses_placed X W S
    hS_enc hS_dec hS_init hS_decPk hS_pksm hS_files hS_encOk hS_initOk hS_decPkOk
  intro st hst
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hsc st hst
  exact ⟨fun b t hn => let ⟨a, hr, ho, hc⟩ := c1 b t hn; ⟨a, hr.2, ho, hc⟩,
    fun m r hm => let ⟨a, hr, ho, hc⟩ := c2 m r hm; ⟨a, hr.2, ho, hc⟩,
    fun c rc hc => let ⟨a, hr, ho, hc⟩ := c3 c rc hc; ⟨a, hr.2, ho, hc⟩,
    fun m rc hm hmat => let ⟨a, hr, ho, hc⟩ := c4 m rc hm hmat; ⟨a, hr.2, ho, hc⟩,
    fun c rc hc h2 h3 => let ⟨a, hr, ho, hc⟩ := c5 c rc hc h2 h3; ⟨a, hr.2, ho, hc⟩,
    fun x₀ g₀ m rc hs hm hnot =>
      let ⟨a, hr, hd2c, hex, hc⟩ := c6 x₀ g₀ m rc hs hm hnot
      ⟨a, hr.2, hd2c, hex, hc⟩⟩

theorem pqScopedCliRunSemD2c_pqxdh_and_noMatch_clauses_placed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let Run := pqScopedRun WP (runRel (cliRunSemD2c_placed X W))
    ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
      (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
        st.session = none →
        ∃ a, Run (pqInitInputs WP st b t) a ∧
          observe (pqInitInputs WP st b t).files a =
            pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
          CommitOk (pqInitInputs WP st b t) (MainResult.ofAnswer a)) ∧
      (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
        ∃ a, Run (pqSendInputs WP st m r) a ∧
          observe (pqSendInputs WP st m r).files a =
            pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
          CommitOk (pqSendInputs WP st m r) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
          observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
              (pqRecvWhisperModel WP st c rc) ∧
          CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
      (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
          observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (pqRecvPrekeyModel X WP st m rc) ∧
          CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
        ∃ a, Run (pqRecvInputs WP st c rc) a ∧
          observe (pqRecvInputs WP st c rc).files a =
            .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
          CommitOk (pqRecvInputs WP st c rc) (MainResult.ofAnswer a)) ∧
      MainOkNoMatchClausePlaced WP X Run st :=
  pqScopedRunSem_pqxdh_and_noMatch_clauses_placed X W (cliRunSemD2c_placed X W)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem cliRunSemD2c_pqxdh_and_noMatch_clauses_placed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let Run := runRel (cliRunSemD2c_placed X W)
    ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
      (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
        st.session = none →
        ∃ a, Run (pqInitInputs WP st b t) a ∧
          observe (pqInitInputs WP st b t).files a =
            pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
          CommitOk (pqInitInputs WP st b t) (MainResult.ofAnswer a)) ∧
      (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
        ∃ a, Run (pqSendInputs WP st m r) a ∧
          observe (pqSendInputs WP st m r).files a =
            pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
          CommitOk (pqSendInputs WP st m r) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
          observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
              (pqRecvWhisperModel WP st c rc) ∧
          CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
      (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
          observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
            pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (pqRecvPrekeyModel X WP st m rc) ∧
          CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
        ∃ a, Run (pqRecvInputs WP st c rc) a ∧
          observe (pqRecvInputs WP st c rc).files a =
            .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
          CommitOk (pqRecvInputs WP st c rc) (MainResult.ofAnswer a)) ∧
      MainOkNoMatchClausePlaced WP X Run st :=
  runSem_pqxdh_and_noMatch_clauses_placed X W (cliRunSemD2c_placed X W)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## `MainOkCliExt*B2NeedLocksPlacedAt` constructors -/

theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_pqScopedMainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))
            inputsOf)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W
  have hcl := pqScopedCliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W
  exact ⟨pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)),
    hmain_sub h547 X W,
    fun p hp =>
      let ⟨c1, c2, c3, c4, c5, _⟩ := hcl p hp
      ⟨c1, c2, c3, c4, c5⟩⟩

theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_pqScopedMainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))
            inputsOf)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W
  have hcl := pqScopedCliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W
  refine ⟨pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)),
    hmain_sub h547 X W,
    fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_mainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (runRel (cliRunSemD2c_placed X W))
            inputsOf)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W
  have hcl := cliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W
  exact ⟨runRel (cliRunSemD2c_placed X W),
    hmain_sub h547 X W,
    fun p hp =>
      let ⟨c1, c2, c3, c4, c5, _⟩ := hcl p hp
      ⟨c1, c2, c3, c4, c5⟩⟩

theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_mainSubroutine
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat} {lim : BudgetLimits}
    (hmain_sub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (runRel (cliRunSemD2c_placed X W))
            inputsOf)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr brkStart stk lim := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W
  have hcl := cliRunSemD2c_pqxdh_and_noMatch_clauses_placed X W
  refine ⟨runRel (cliRunSemD2c_placed X W),
    hmain_sub h547 X W,
    fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

/-- Assemble `MainOkCliExtPqB2NeedLocksPlacedAt` at Block `617` from `runSpecTightPlaced` and
`B2MainRemainingHops`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_hops
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    (St0 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St1 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St2 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St3 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St4 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → FineBudget → Prop)
    (St5 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → Bool →
      FineBudget → Prop)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hstrlen_row : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hc_alloc : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
      CliInputsOk i → St0 X W i fineCostModel.init)
    (hSt01 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) {i : Inputs},
      CliInputsOk i → St0 X W i fineCostModel.init → i.argv ≠ [] →
        FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
          St1 X W i
            (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hhops : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
          CodeOk mmpl ext W brkStart lim γ tp
          (St1 X W) (St2 X W) (St3 X W) (St4 X W) (St5 X W) (RunEnv X W)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_pqScopedRunSem_placed hblk hext_nodup hCI
        ⟨W.C, W.Q⟩ (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq (hstrlen_row W) (hc_alloc W γ tp)
        (hSt0 X W) (hSt01 X W) (hrun h547 X W γ tp) (hhops h547 X W γ tp)

/-- Assemble `MainOkCliExtOverB2NeedLocksPlacedAt` at Block `617` from `runSpecTightPlaced` and
`B2MainRemainingHops`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_hops
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    (St0 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St1 : UnreachedPqxdhPrimitives → CliHooks → Inputs → FineBudget → Prop)
    (St2 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St3 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → FineBudget → Prop)
    (St4 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → FineBudget → Prop)
    (St5 : UnreachedPqxdhPrimitives → CliHooks → Inputs → CallV → StoresGhost → Bool →
      FineBudget → Prop)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hstrlen_row : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hc_alloc : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
      CliInputsOk i → St0 X W i fineCostModel.init)
    (hSt01 : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) {i : Inputs},
      CliInputsOk i → St0 X W i fineCostModel.init → i.argv ≠ [] →
        FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
          St1 X W i
            (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (hhops : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
          CodeOk mmpl ext W brkStart lim γ tp
          (St1 X W) (St2 X W) (St3 X W) (St4 X W) (St5 X W) (RunEnv X W)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W)))) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_pqScopedRunSem_placed hblk hext_nodup hCI
        ⟨W.C, W.Q⟩ (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq (hstrlen_row W) (hc_alloc W γ tp)
        (hSt0 X W) (hSt01 X W) (hrun h547 X W γ tp) (hhops h547 X W γ tp)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
