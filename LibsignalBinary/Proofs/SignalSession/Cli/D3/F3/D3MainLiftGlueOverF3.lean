/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Two-Placement `579 → 617` Lift & `MainOkOverD3F3` Glue

Connects `pqD3ScopedRun` over `cliRunSemOverV4 X W` and `[LibsignalPlacement]`-free
two-placement `(mpl, mmpl)` Block-`579 → 617` harness lifts to `MainOkOverD3F3` and
`MainOkCliF3OverB2NeedLocksPlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3

open Arm64 (GhostName Memory State subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ProcessInputs bytesOfString initFsState)
open CryptoVerification (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib pqRecvInputs strlenHook)
open CryptoVerification.SignalSession.Cli (CliInputsOk RunAnswer StoresGhost cliInputs)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallV DomainArgv LsCodeInv RunCall cliIo cliMainStk cliResStack cliWrOk hparse_of_domains
   mProgPlaced mainFrameSize parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runAns runRel runRel_dom)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap (AllocEvent BudgetLimits FitsEvents rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineBudget fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv (mainSt4 mainSt5)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (CliPqOrD3RecvDom mainSt01Dom_of_st0 mainSt0Dom mainSt1Dom mainSt2Dom mainSt3Dom)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
  (cliRunSemOverV4 pqD3ScopedRun runRel_pqRecv_canonicalNoMatch runRel_pqRecv_validOver)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (MainOkCanonNoMatchD3F3 MainOkOverD3F3 MainOkValidOverBodyD3F3 mainOkCliF3Over_of_mainOkOverD3F3
   mainOkOverD3F3_of_clauses)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliF3OverB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
  (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (MainEntryBudgetFitsCap
   b2MainSpecTightNeedLocksFineAt_cliExterns_of_runTight_and_budgetFitsCap_lsmpl
   b2MainSpecTightNeedLocksFineAt_cliGhostExterns_of_runTight_and_budgetFitsCap_lsmpl
   cliGhostExterns_strlen)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (B2MainRemainingHops b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
   initFsState_cliProcessInputs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks allocContractsFsPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. Pure `pqD3ScopedRun` & `cliRunSemOverV4` Clauses -/

theorem pqD3ScopedRun_dom {WP : PEParams} {S : RunSem} {i : Inputs} {a : RunAnswer}
    (hr : pqD3ScopedRun WP (runRel S) i a) : DomainArgv i :=
  runRel_dom hr.2

theorem pqD3ScopedRun_parse_isSome {WP : PEParams} {S : RunSem}
    (i : Inputs) (a : RunAnswer) (hr : pqD3ScopedRun WP (runRel S) i a) :
    (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome :=
  hparse_of_domains (fun _ _ h => pqD3ScopedRun_dom h) i a hr

/-- Canonical-`m.bytes` non-matching clause (`MainOkCanonNoMatchD3F3`) at
`RunOf X W := pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem mainOkCanonNoMatchD3F3_overV4 (mpl : MultiPlacement) :
    MainOkCanonNoMatchD3F3 mpl
      (fun X W => pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) := by
  unfold MainOkCanonNoMatchD3F3
  intro _hDropNz X W _WP _Run st hst x g hsess m rc hm hnomatch
  exact ⟨runAns (cliRunSemOverV4 X W) (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc),
    runRel_pqRecv_canonicalNoMatch X W st x g m rc hst hsess hm hnomatch⟩

/-- Establishes `MainOkValidOverBodyD3F3` from a Block-`617` `subroutine_ok` over
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem mainOkValidOverBodyD3F3_of_mainSubroutine
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hmain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) cliProcessInputs)) :
    MainOkValidOverBodyD3F3 mpl mmpl CodeOk libcAddr brkStart stk
      (fun X W => pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) := by
  unfold MainOkValidOverBodyD3F3
  intro hDropNz X W _WP _Run
  refine ⟨hmain hDropNz X W, fun st hst x g hsess body pm m rc hbody hparse hpk hm hnomatch => ?_⟩
  exact ⟨runAns (cliRunSemOverV4 X W) (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
    runRel_pqRecv_validOver X W st x g body pm m rc hst hsess hbody hparse hpk hm hnomatch⟩

/-- Establishes `MainOkOverD3F3` from a Block-`617` `subroutine_ok` over
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem mainOkOverD3F3_of_mainSubroutine
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hmain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) cliProcessInputs)) :
    MainOkOverD3F3 mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkOverD3F3_of_clauses
    (mainOkValidOverBodyD3F3_of_mainSubroutine hmain)
    (mainOkCanonNoMatchD3F3_overV4 mpl)

theorem mainOkCliF3Over_of_mainSubroutine
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hmain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) cliProcessInputs)) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr brkStart stk :=
  mainOkCliF3Over_of_mainOkOverD3F3 (mainOkOverD3F3_of_mainSubroutine hmain)

/-! ## 2. Shared `[LibsignalPlacement]`-Free `(mpl, mmpl)` `579 → 617` Lifts into `F3.L4B` -/

/-- Block-`617` ghost-to-linked `cliExternsPlaced mmpl` transfer predicate. -/
abbrev Block617GhostToLinkedAt
    (mpl mmpl : MultiPlacement) (ghOf : CliHooks → CliGhostHooks)
    (CodeOk : Memory → Prop) (libcAddr brkStart : BitVec 64)
    (lim : BudgetLimits) (stk : Nat) (W : CliHooks)
    (γ : GhostName) (tp : BitVec 64)
    (Run : Inputs → RunAnswer → Prop) (inputsOf : Inputs → ProcessInputs) : Prop :=
  subroutine_ok
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) 617 W)
      (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf) →
    subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)

/-- Generic `[LibsignalPlacement]`-free `(mpl, mmpl)` `579 → 617` lift into
`b2MainSpecTightNeedLocksFineAt`. -/
theorem b2MainSpecTightNeedLocksFineAt_f3_of_runTight_placed
    {mpl mmpl : MultiPlacement}
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
    {Run : Inputs → RunAnswer → Prop} {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
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
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp St1 St2 St3 St4 St5 RunEnv Run) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff mpl ext 617 W (mpl.base 617)
    libcAddr CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim fineCostModel.init
    cliMainStk (cliStaticsPlacedAt mpl) Run inputsOf).mp
    (b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
      hlibc hfs_eq hparse hstrlen_row hc_alloc hSt0 hSt01 hrun hhops)

/-- Specializes `b2MainSpecTightNeedLocksFineAt_f3_of_runTight_placed` to
`mainSt0Dom..mainSt3Dom Dom E lim` and `mainSt4`/`mainSt5`. -/
theorem b2MainSpecTightNeedLocksFineAt_f3_of_d3MainSt0Dom_placed
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs)
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstrlen_row : ext W "strlen" = some strlenHook)
    (hc_alloc : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → mainSt0Dom Dom E lim i fineCostModel.init)
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp
      (mainSt1Dom Dom E lim) (mainSt2Dom Dom E lim) (mainSt3Dom Dom E lim)
      (mainSt4 lim) (mainSt5 lim) RunEnv Run) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs) :=
  b2MainSpecTightNeedLocksFineAt_f3_of_runTight_placed hblk hext_nodup hCI
    hlibc initFsState_cliProcessInputs_eq hparse hstrlen_row hc_alloc hSt0
    (fun hok hst0 hne => mainSt01Dom_of_st0 hok hst0 hne) hrun hhops

/-- Specializes `b2MainSpecTightNeedLocksFineAt_f3_of_d3MainSt0Dom_placed` to
`cliGhostExterns`, discharging `strlen` and allocator contracts from `CliGhostAllocHooks`. -/
theorem b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_d3MainSt0Dom_placed
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs)
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hG : @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → mainSt0Dom Dom E lim i fineCostModel.init)
    (hrun : @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) W
      brkStart lim γ tp
      (mainSt1Dom Dom E lim) (mainSt2Dom Dom E lim) (mainSt3Dom Dom E lim)
      (mainSt4 lim) (mainSt5 lim) RunEnv Run) :
    subroutine_ok
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) 617 W)
      (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact b2MainSpecTightNeedLocksFineAt_f3_of_d3MainSt0Dom_placed hblk hext_nodup hCI
    Dom E hlibc hparse
    (cliGhostExterns_strlen mmpl (ghOf W) W)
    (allocContractsFsPlaced_of_hooks mmpl (ghOf W) W hG)
    hSt0 hrun hhops

theorem b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_d3MainSt0Dom_linked_placed
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs)
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hG : @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hSt0 : ∀ i : Inputs, CliInputsOk i → mainSt0Dom Dom E lim i fineCostModel.init)
    (hrun : @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) W
      brkStart lim γ tp
      (mainSt1Dom Dom E lim) (mainSt2Dom Dom E lim) (mainSt3Dom Dom E lim)
      (mainSt4 lim) (mainSt5 lim) RunEnv Run)
    (hTransfer617 : Block617GhostToLinkedAt mpl mmpl ghOf CodeOk libcAddr brkStart lim
      cliMainStk W γ tp Run cliProcessInputs) :
    subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs) :=
  hTransfer617
    (b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_d3MainSt0Dom_placed hblk hext_nodup hCI
      ghOf Dom E hlibc hparse hG hSt0 hrun hhops)

/-- Lifts a Block-`579` `runSpecTightPlaced` contract and `MainEntryBudgetFitsCap` on
`cliGhostExterns` to `b2MainSpecTightNeedLocksFineAt`. -/
theorem b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_budgetFitsCap_placed
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hG : @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hio : @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack)) :
    subroutine_ok
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) 617 W)
      (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff mpl
    (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) 617 W (mpl.base 617)
    libcAddr CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim fineCostModel.init
    cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs).mp
    (b2MainSpecTightNeedLocksFineAt_cliGhostExterns_of_runTight_and_budgetFitsCap_lsmpl
      mmpl ghOf W hlibc initFsState_cliProcessInputs_eq hparse hG hio hioBounded hstk hfitCap hrun)

theorem b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_budgetFitsCap_linked_placed
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hG : @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hio : @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack))
    (hTransfer617 : Block617GhostToLinkedAt mpl mmpl ghOf CodeOk libcAddr brkStart lim
      cliMainStk W γ tp Run cliProcessInputs) :
    subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs) :=
  hTransfer617
    (b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_budgetFitsCap_placed hblk hext_nodup hCI
      ghOf hlibc hparse hG hio hioBounded hstk hfitCap hrun)

theorem b2MainSpecTightNeedLocksFineAt_f3_cliExterns_of_budgetFitsCap_placed
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hFs : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W))
    (hio : @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W) cliIo hookStack)
    (hioBounded : @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W) cliIo hookStack
      ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (cliExternsPlaced mmpl W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse Run
        cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact (subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff mpl (cliExternsPlaced mmpl) 617 W
    (mpl.base 617) libcAddr CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
    fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run cliProcessInputs).mp
    (b2MainSpecTightNeedLocksFineAt_cliExterns_of_runTight_and_budgetFitsCap_lsmpl
      mmpl W hlibc initFsState_cliProcessInputs_eq hparse hFs hio hioBounded hstk hfitCap hrun)

/-! ## 3. Concrete `MainOkOverD3F3` & `MainOkCliF3OverB2NeedLocksPlacedAt` Assemblers -/

/-- `CodeOk`-generic `MainOkOverD3F3` assembler from Block-`579` `hrun` and `mainSt0Dom`. -/
theorem mainOkOverD3F3_of_hrun_and_d3MainSt0Dom
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64}
    (E : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → CliRunCalleeEnvs)
    (RunEnvOf : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits (ghOf W))
    (hSt0 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (i : Inputs),
        CliInputsOk i →
        mainSt0Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits i
          fineCostModel.init)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnvOf X W γ tp) uuidTryParse
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
            cliWrOk cliResStack))
    (hhops : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
          CodeOk mmpl (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) W
          brkStart cliBudgetLimits γ tp
          (mainSt1Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits)
          (mainSt2Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits)
          (mainSt3Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits)
          (mainSt4 cliBudgetLimits) (mainSt5 cliBudgetLimits)
          (RunEnvOf X W γ tp)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))
    (hTransfer617 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        Block617GhostToLinkedAt mpl mmpl ghOf CodeOk libcAddr brkStart cliBudgetLimits
          cliMainStk W γ tp (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
          cliProcessInputs) :
    MainOkOverD3F3 mpl mmpl CodeOk libcAddr brkStart cliMainStk :=
  mainOkOverD3F3_of_mainSubroutine fun h547 X W γ tp =>
    b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_d3MainSt0Dom_linked_placed
      hblk hext_nodup hCI ghOf (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp)
      hlibc pqD3ScopedRun_parse_isSome (hG W γ tp)
      (hSt0 h547 X W γ tp) (hrun h547 X W γ tp) (hhops h547 X W γ tp)
      (hTransfer617 h547 X W γ tp)

theorem mainOkCliF3Over_of_hrun_and_d3MainSt0Dom
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64}
    (E : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → CliRunCalleeEnvs)
    (RunEnvOf : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits (ghOf W))
    (hSt0 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (i : Inputs),
        CliInputsOk i →
        mainSt0Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits i
          fineCostModel.init)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnvOf X W γ tp) uuidTryParse
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
            cliWrOk cliResStack))
    (hhops : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
          CodeOk mmpl (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) W
          brkStart cliBudgetLimits γ tp
          (mainSt1Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits)
          (mainSt2Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits)
          (mainSt3Dom (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (E X W γ tp) cliBudgetLimits)
          (mainSt4 cliBudgetLimits) (mainSt5 cliBudgetLimits)
          (RunEnvOf X W γ tp)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))
    (hTransfer617 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        Block617GhostToLinkedAt mpl mmpl ghOf CodeOk libcAddr brkStart cliBudgetLimits
          cliMainStk W γ tp (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
          cliProcessInputs) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr brkStart cliMainStk :=
  mainOkCliF3Over_of_mainOkOverD3F3
    (mainOkOverD3F3_of_hrun_and_d3MainSt0Dom hblk hext_nodup hCI ghOf E RunEnvOf
      hlibc hG hSt0 hrun hhops hTransfer617)

/-- `CodeOk`-generic `MainOkOverD3F3` assembler from Block-`579` `hrun` and
`MainEntryBudgetFitsCap`. -/
theorem mainOkOverD3F3_of_hrun_and_budgetFitsCap
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (RunEnvOf : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits (ghOf W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel cliBudgetLimits fineCostModel.init cliIo uuidTryParse
          (RunEnvOf X W γ tp)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnvOf X W γ tp) uuidTryParse
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
            cliWrOk cliResStack))
    (hTransfer617 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        Block617GhostToLinkedAt mpl mmpl ghOf CodeOk libcAddr brkStart cliBudgetLimits
          cliMainStk W γ tp (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
          cliProcessInputs) :
    MainOkOverD3F3 mpl mmpl CodeOk libcAddr brkStart cliMainStk :=
  mainOkOverD3F3_of_mainSubroutine fun h547 X W γ tp =>
    b2MainSpecTightNeedLocksFineAt_f3_cliGhostExterns_of_budgetFitsCap_linked_placed
      hblk hext_nodup hCI ghOf hlibc pqD3ScopedRun_parse_isSome
      (hG W γ tp) (hio W γ tp) (hioBounded W γ tp) hstk
      (hfitCap h547 X W γ tp) (hrun h547 X W γ tp) (hTransfer617 h547 X W γ tp)

theorem mainOkCliF3Over_of_hrun_and_budgetFitsCap
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (RunEnvOf : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits (ghOf W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel cliBudgetLimits fineCostModel.init cliIo uuidTryParse
          (RunEnvOf X W γ tp)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnvOf X W γ tp) uuidTryParse
            (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
            cliWrOk cliResStack))
    (hTransfer617 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        Block617GhostToLinkedAt mpl mmpl ghOf CodeOk libcAddr brkStart cliBudgetLimits
          cliMainStk W γ tp (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
          cliProcessInputs) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr brkStart cliMainStk :=
  mainOkCliF3Over_of_mainOkOverD3F3
    (mainOkOverD3F3_of_hrun_and_budgetFitsCap hblk hext_nodup hCI ghOf RunEnvOf
      hlibc hG hio hioBounded hstk hfitCap hrun hTransfer617)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3
