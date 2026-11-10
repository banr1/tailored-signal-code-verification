/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Heap.Fine.Inv
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine

/-!
# Stdin-Capped Entry Budget Fit (`MainEntryBudgetFitsCap`) and `main` Lifts

Defines `MainEntryBudgetFitsCap` and its `ReadEnv`-parametric generalization
`MainEntryBudgetFitsCapOf`, guarding the `M4` (`Run i a`) budget continuation with the
`(inputOf i c).length ≤ stdinCapBytes` bound established at `M3` (`read_stdin`), and lifts
Block-`579` `runSpecTightPlaced` contracts to `MainOkCliExtPqB2NeedLocksPlacedAt` and
`MainOkCliExtOverB2NeedLocksPlacedAt` on Block `617`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   ls_externAt?_of_mem ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack finishGrowStackX)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliExternsPlaced cliProcessInputs fromUtf8Hook
   libsignalSessionLib lsFromUtf8Sym lsMemrchrSym lsReadFileSym lsReadStdinSym lsWriteFileSym
   lsWriteStdoutSym memrchrHook stdinCapBytes strlenHook writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk RunAnswer StoresGhost cliInputs)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_588)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallV DomainArgv IoModel LsCodeInv RunCall cliExternsPlaced_fromUtf8 cliExternsPlaced_memrchr
   cliExternsPlaced_strlen cliExternsPlaced_writeFile cliExternsPlaced_writeStdout cliIo
   cliMainStk cliResStack cliWrOk cli_hstk64 cli_resStack_callees
   fromUtf8Hook_ok hparse_of_domains inputOf lsHandleErrorSymMain mProgPlaced mainFrameSize
   namedWrites parseArgs strlenHook_ok)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel runRel_dom)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.Slots
  (cliExternsPlaced_panic_all cliGhostExterns_fromUtf8_eq cliGhostExterns_memrchr_eq
   cliGhostExterns_panic_all)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineBudget FineScale FineStepBound_mono_meta Guaranteed63Threshold MmapThresholdReq
   fineCostModel fineFootprint fineHookRustCliAllocBudget fineMaxDynIvs fineMaxGroups
   fineMaxMetaAreas finePeak63Bytes finePeak63Count fineStepReserve fromUtf8Hook_vmPreserved
   strlenHook_vmPreserved toFineEvent)
open LibsignalBinary.Heap.SpecBudget
  (hookSat_withVmPreserved vmPreserved_writeFileHook vmPreserved_writeStdoutHook writeFileEnv_nil
   writeStdoutEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (M2CollectEnv M2CollectStepEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (IterSeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
  (argvAtROP libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt
   b2MainSpecTightNeedLocksFineAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced MainIoOfPlaced ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (B2MainRemainingHops b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl cliRunSemD2c_placed
   initFsState_cliProcessInputs_eq mainOkCliExtOverB2NeedLocksPlacedAt_of_pqScopedMainSubroutine
   mainOkCliExtPqB2NeedLocksPlacedAt_of_pqScopedMainSubroutine pqScopedRun
   subroutine_ok_runSpecTightPlaced_mono_run)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (MainCalleesBlk617 runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudget
  (address_placed_ok_a1_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget
  (allocContractsFsPlaced_toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.shim2_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
  (M2CollectLoopEnv m2GrowEventsAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget (m2DispatchEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget
  (M2PreDeallocEnv b2_step2_pool_placed_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget
  (M3Env M3EnvReadOf main_m3_bounded_pool_placed_proof main_m3_bounded_readOf_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudget
  (main_m4_pool_placed_proof main_m4_sendOverCap_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget
  (M5Env main_m5_of_proof_placed main_m5_proof_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6PlacedBudget
  (main_m6_m6Env_pool_proof_placed main_m6_of_m6Env_pool_proof_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
  (allocNoOomExtern_fs_rocl reserve16_placed_ok reserve1_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
  (tryAllocateIn3_placed_okFs_of_hooks_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks allocContractsFsPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced ReadFileRuleEnv readFileLitSpecPlaced readStdinSpecPlaced
   writeFileSpecPlaced writeStdoutSpecPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## Stdin-capped entry budget-fit predicates -/

/-- Entry cost-model budget-fit predicate across `M1`..`M6`, guarding the `M4` continuation with
`(inputOf i c).length ≤ stdinCapBytes`. -/
def MainEntryBudgetFitsCap (M : AllocCostModel) (lim : BudgetLimits) (st0 : M.σ)
    (io : IoModel) (uuidParse : UuidParser)
    (RunEnv : RunCall → List AllocEvent → Prop)
    (Run : Inputs → RunAnswer → Prop) : Prop :=
  ∀ (i : Inputs), CliInputsOk i →
    (i.argv ≠ [] → FitsEvents M lim st0 (rustAllocEvents (16 * i.argv.length) 8)) ∧
    (i.argv ≠ [] →
      let st1 := M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0
      FitsEnv M lim st1 (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)) ∧
      ∀ (vcap : BitVec 64) (evs_c : List AllocEvent) (c : CallV),
        M2CollectEnv i.argv.length evs_c →
        vcap ≠ 0#64 →
        parseArgs uuidParse (i.argv.map bytesOfString) = some c →
        let st2 :=
          M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
            (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
              (M.stepEvents evs_c st1))
        FitsEnv M lim st2 (M3Env io i c) ∧
        ∀ evs_m3 : List AllocEvent, M3Env io i c evs_m3 →
          let st3 := M.stepEvents evs_m3 st2
          (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f → FitsEvents M lim st3 evs_f) ∧
          ((inputOf i c).length ≤ stdinCapBytes →
            ∀ (a : RunAnswer) (resP callP storesP inpP coinsP : BitVec 64),
              Run i a →
              let g : RunCall :=
                { i := i, c := c, a := a,
                  res := resP, call := callP, stores := storesP, inp := inpP, coins := coinsP }
              FitsEnv M lim st3 (RunEnv g) ∧
              ∀ evs_r : List AllocEvent, RunEnv g evs_r →
                let st4 := M.stepEvents evs_r st3
                (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f → FitsEvents M lim st4 evs_f) ∧
                ∀ (sg : StoresGhost) (out : List (BitVec 8)),
                  a = some (some (namedWrites sg.writes, out)) →
                  (∀ pw ∈ sg.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
                  ∀ (ok : Bool),
                    FitsEnv M lim st4 (SeqEnv (M5Env sg) (M6Env ok))))

theorem mainEntryBudgetFitsCap_mono_run
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run₁ Run₂ : Inputs → RunAnswer → Prop}
    (himp : ∀ i a, Run₁ i a → Run₂ i a)
    (h : MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv Run₂) :
    MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv Run₁ :=
  fun i hok =>
    ⟨(h i hok).1, fun hne =>
      ⟨((h i hok).2 hne).1, fun vcap evs_c c hc hv hp =>
        let hm2 := ((h i hok).2 hne).2 vcap evs_c c hc hv hp
        ⟨hm2.1, fun evs_m3 hm3 =>
          let hm3' := hm2.2 evs_m3 hm3
          ⟨hm3'.1, fun hin a resP callP storesP inpP coinsP hrun =>
            hm3'.2 hin a resP callP storesP inpP coinsP (himp i a hrun)⟩⟩⟩⟩

def domScopedRun (Dom : Inputs → Prop) (Run₀ : Inputs → RunAnswer → Prop)
    (i : Inputs) (a : RunAnswer) : Prop :=
  Dom i ∧ Run₀ i a

theorem domScopedRun_eq_pqScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop) :
    domScopedRun (CliPqxdhInputs WP) Run₀ = pqScopedRun WP Run₀ :=
  rfl

theorem domScopedRun_dom {Dom : Inputs → Prop} {S : RunSem} {i : Inputs} {a : RunAnswer}
    (hr : domScopedRun Dom (runRel S) i a) : DomainArgv i :=
  runRel_dom hr.2

theorem mainEntryBudgetFitsCap_domScopedRun
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Dom : Inputs → Prop} {Run₀ : Inputs → RunAnswer → Prop}
    (h : MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv Run₀) :
    MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv (domScopedRun Dom Run₀) :=
  mainEntryBudgetFitsCap_mono_run (fun _ _ hr => hr.2) h

theorem mainEntryBudgetFitsCap_pqScopedRun
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {WP : PEParams} {Run₀ : Inputs → RunAnswer → Prop}
    (h : MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv Run₀) :
    MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv (pqScopedRun WP Run₀) :=
  mainEntryBudgetFitsCap_mono_run (fun _ _ hr => hr.2) h

/-- `ReadEnv`-parametric generalization of `MainEntryBudgetFitsCap` over `M3EnvReadOf`. -/
def MainEntryBudgetFitsCapOf (M : AllocCostModel) (lim : BudgetLimits) (st0 : M.σ)
    (io : IoModel) (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (uuidParse : UuidParser)
    (RunEnv : RunCall → List AllocEvent → Prop)
    (Run : Inputs → RunAnswer → Prop) : Prop :=
  ∀ (i : Inputs), CliInputsOk i →
    (i.argv ≠ [] → FitsEvents M lim st0 (rustAllocEvents (16 * i.argv.length) 8)) ∧
    (i.argv ≠ [] →
      let st1 := M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0
      FitsEnv M lim st1 (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)) ∧
      ∀ (vcap : BitVec 64) (evs_c : List AllocEvent) (c : CallV),
        M2CollectEnv i.argv.length evs_c →
        vcap ≠ 0#64 →
        parseArgs uuidParse (i.argv.map bytesOfString) = some c →
        let st2 :=
          M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
            (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
              (M.stepEvents evs_c st1))
        FitsEnv M lim st2 (M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c) ∧
        ∀ evs_m3 : List AllocEvent, M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c evs_m3 →
          let st3 := M.stepEvents evs_m3 st2
          (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f → FitsEvents M lim st3 evs_f) ∧
          ((inputOf i c).length ≤ stdinCapBytes →
            ∀ (a : RunAnswer) (resP callP storesP inpP coinsP : BitVec 64),
              Run i a →
              let g : RunCall :=
                { i := i, c := c, a := a,
                  res := resP, call := callP, stores := storesP, inp := inpP, coins := coinsP }
              FitsEnv M lim st3 (RunEnv g) ∧
              ∀ evs_r : List AllocEvent, RunEnv g evs_r →
                let st4 := M.stepEvents evs_r st3
                (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f → FitsEvents M lim st4 evs_f) ∧
                ∀ (sg : StoresGhost) (out : List (BitVec 8)),
                  a = some (some (namedWrites sg.writes, out)) →
                  (∀ pw ∈ sg.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
                  ∀ (ok : Bool),
                    FitsEnv M lim st4 (SeqEnv (M5Env sg) (M6Env ok))))

theorem mainEntryBudgetFitsCapOf_eq_mainEntryBudgetFitsCap
    (M : AllocCostModel) (lim : BudgetLimits) (st0 : M.σ) (io : IoModel) (uuidParse : UuidParser)
    (RunEnv : RunCall → List AllocEvent → Prop) (Run : Inputs → RunAnswer → Prop) :
    MainEntryBudgetFitsCapOf M lim st0 io (ReadFileRuleEnv io.rd) uuidParse RunEnv Run =
      MainEntryBudgetFitsCap M lim st0 io uuidParse RunEnv Run :=
  rfl

theorem mainEntryBudgetFitsCapOf_mono_run
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run₁ Run₂ : Inputs → RunAnswer → Prop}
    (himp : ∀ i a, Run₁ i a → Run₂ i a)
    (h : MainEntryBudgetFitsCapOf M lim st0 io ReadEnv uuidParse RunEnv Run₂) :
    MainEntryBudgetFitsCapOf M lim st0 io ReadEnv uuidParse RunEnv Run₁ :=
  fun i hok =>
    ⟨(h i hok).1, fun hne =>
      ⟨((h i hok).2 hne).1, fun vcap evs_c c hc hv hp =>
        let hm2 := ((h i hok).2 hne).2 vcap evs_c c hc hv hp
        ⟨hm2.1, fun evs_m3 hm3 =>
          let hm3' := hm2.2 evs_m3 hm3
          ⟨hm3'.1, fun hin a resP callP storesP inpP coinsP hrun =>
            hm3'.2 hin a resP callP storesP inpP coinsP (himp i a hrun)⟩⟩⟩⟩

theorem mainEntryBudgetFitsCapOf_domScopedRun
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Dom : Inputs → Prop} {Run₀ : Inputs → RunAnswer → Prop}
    (h : MainEntryBudgetFitsCapOf M lim st0 io ReadEnv uuidParse RunEnv Run₀) :
    MainEntryBudgetFitsCapOf M lim st0 io ReadEnv uuidParse RunEnv (domScopedRun Dom Run₀) :=
  mainEntryBudgetFitsCapOf_mono_run (fun _ _ hr => hr.2) h

theorem mainEntryBudgetFitsCapOf_pqScopedRun
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {WP : PEParams} {Run₀ : Inputs → RunAnswer → Prop}
    (h : MainEntryBudgetFitsCapOf M lim st0 io ReadEnv uuidParse RunEnv Run₀) :
    MainEntryBudgetFitsCapOf M lim st0 io ReadEnv uuidParse RunEnv (pqScopedRun WP Run₀) :=
  mainEntryBudgetFitsCapOf_mono_run (fun _ _ hr => hr.2) h

/-! ## `MainCalleesBlk617` discharge -/

private theorem ls_hook_placed_rocl_ok_local [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat hmem

/-- Unconditional discharge of `MainCalleesBlk617` for any `H : LibsignalHooks` from
`AllocContractsFsPlaced A lim H` and the four non-allocator hook equations. -/
theorem mainCalleesBlk617_of_allocFs_and_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack resStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : H lsMemrchrSym = some memrchrHook)
    (hpan : H lsHandleErrorSymMain = some Rust.panicked)
    (hfg : finishGrowStackX ≤ resStack)
    (hdr : doReserveStackX ≤ resStack)
    (haddr : 0xB0 + extHookStack ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    MainCalleesBlk617 A lim H uuidTryParse hookStack resStack where
  alloc := allocContractsFsPlaced_toAllocContractsX hFs
  allocFs := hFs
  strlen := ls_hook_placed_rocl_ok_local <|
    hookSat_withVmPreserved ⟨strlenHook, hstrlen, strlenHook_ok hookStack⟩
      (fun f hf s => by
        cases hstrlen.symm.trans hf
        exact strlenHook_vmPreserved s)
  fromUtf8 := ls_hook_placed_rocl_ok_local <|
    hookSat_withVmPreserved ⟨fromUtf8Hook err, hutf8, fromUtf8Hook_ok hookStack err⟩
      (fun f hf s => by
        cases hutf8.symm.trans hf
        exact fromUtf8Hook_vmPreserved err s)
  address := address_placed_ok_a1_of_hooks hFs hmemrchr haddr hres64
  reserve16 := reserve16_placed_ok hFs hdr hpan
  reserve1 := reserve1_placed_ok hFs hdr hpan
  tryAllocateIn3 :=
    tryAllocateIn3_placed_okFs_of_hooks_at
      (prog := lsProg_617 H) (i := 617)
      (AllocContractsFsPlaced.shim2_rocl (prog := lsProg_588 H) (i := 588) hFs)
      (allocNoOomExtern_fs_rocl (prog := lsProg_588 H) (i := 588) hFs)
      hfg hres64
  handleErrorPanic :=
    (ls_externAt?_of_mem (prog := lsProg_617 H) (i := 617) (by decide)).trans hpan

theorem mainCalleesBlk617_of_allocFs_and_hooks_cliResStack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : H lsMemrchrSym = some memrchrHook)
    (hpan : H lsHandleErrorSymMain = some Rust.panicked) :
    MainCalleesBlk617 A lim H uuidTryParse hookStack cliResStack :=
  mainCalleesBlk617_of_allocFs_and_hooks hFs hstrlen hutf8 hmemrchr hpan
    cli_resStack_callees.1 cli_resStack_callees.2.1
    cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2

/-! ## Continuation state invariants and `B2MainRemainingHops` -/

def B2St5Cap (M : AllocCostModel) (lim : BudgetLimits) (_i : Inputs) (_c : CallV)
    (_sg : StoresGhost) (ok : Bool) (st5 : M.σ) : Prop :=
  FitsEnv M lim st5 (M6Env ok)

def B2St4Cap (M : AllocCostModel) (lim : BudgetLimits) (_i : Inputs) (_c : CallV)
    (sg : StoresGhost) (st4 : M.σ) : Prop :=
  ∀ (ok : Bool), FitsEnv M lim st4 (SeqEnv (M5Env sg) (M6Env ok))

def B2St3Cap (M : AllocCostModel) (lim : BudgetLimits) (io : IoModel)
    (RunEnv : RunCall → List AllocEvent → Prop) (Run : Inputs → RunAnswer → Prop)
    (i : Inputs) (c : CallV) (st3 : M.σ) : Prop :=
  (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f → FitsEvents M lim st3 evs_f) ∧
  ∀ (a : RunAnswer) (resP callP storesP inpP coinsP : BitVec 64),
    Run i a →
    let g : RunCall :=
      { i := i, c := c, a := a,
        res := resP, call := callP, stores := storesP, inp := inpP, coins := coinsP }
    FitsEnv M lim st3 (RunEnv g) ∧
    ∀ evs_r : List AllocEvent, RunEnv g evs_r →
      let st4 := M.stepEvents evs_r st3
      (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f → FitsEvents M lim st4 evs_f) ∧
      ∀ (sg : StoresGhost) (out : List (BitVec 8)),
        a = some (some (namedWrites sg.writes, out)) →
        (∀ pw ∈ sg.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
        B2St4Cap M lim i c sg st4

def B2St2Cap (M : AllocCostModel) (lim : BudgetLimits) (io : IoModel)
    (RunEnv : RunCall → List AllocEvent → Prop) (Run : Inputs → RunAnswer → Prop)
    (i : Inputs) (c : CallV) (st2 : M.σ) : Prop :=
  FitsEnv M lim st2 (M3Env io i c) ∧
  ∀ evs_m3 : List AllocEvent, M3Env io i c evs_m3 →
    (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
      FitsEvents M lim (M.stepEvents evs_m3 st2) evs_f) ∧
    ((inputOf i c).length ≤ stdinCapBytes →
      B2St3Cap M lim io RunEnv Run i c (M.stepEvents evs_m3 st2))

/-- Coordinatewise dominance on `FineBudget` across all 6 watermark and live-63 fields. -/
def FineBudgetDom (b₁ b₂ : FineBudget) : Prop :=
  b₁.cumSmallBytes ≤ b₂.cumSmallBytes ∧
  b₁.cumSmallGroupsS ≤ b₂.cumSmallGroupsS ∧
  b₁.live63Bytes ≤ b₂.live63Bytes ∧
  finePeak63Bytes b₁ ≤ finePeak63Bytes b₂ ∧
  b₁.live63Count ≤ b₂.live63Count ∧
  finePeak63Count b₁ ≤ finePeak63Count b₂

private theorem fineBudgetDom_stepAligned (align req : Nat) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (FineBudget.stepAligned align req b₁) (FineBudget.stepAligned align req b₂) := by
  rcases h with ⟨hSB, hGS, hLB, hPB, hLC, hPC⟩
  unfold FineBudgetDom FineBudget.stepAligned
  dsimp only
  split
  · unfold finePeak63Bytes finePeak63Count at *
    dsimp only
    exact ⟨hSB, hGS, by omega, by omega, by omega, by omega⟩
  · split
    · unfold finePeak63Bytes finePeak63Count at *
      dsimp only
      exact ⟨by omega, by omega, hLB, by omega, hLC, by omega⟩
    · unfold finePeak63Bytes finePeak63Count at *
      dsimp only
      exact ⟨by omega, by omega, hLB, by omega, hLC, by omega⟩

private theorem fineBudgetDom_stepFree (align req : Nat) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (FineBudget.stepFree align req b₁) (FineBudget.stepFree align req b₂) := by
  rcases h with ⟨hSB, hGS, hLB, hPB, hLC, hPC⟩
  unfold FineBudgetDom FineBudget.stepFree
  dsimp only
  split
  · unfold finePeak63Bytes finePeak63Count at *
    dsimp only
    exact ⟨hSB, hGS, by omega, by omega, by omega, by omega⟩
  · unfold finePeak63Bytes finePeak63Count at *
    dsimp only
    exact ⟨hSB, hGS, hLB, by omega, hLC, by omega⟩

private theorem fineBudgetDom_stepReallocAdd (align newSz : Nat) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (FineBudget.stepReallocAdd align newSz b₁)
      (FineBudget.stepReallocAdd align newSz b₂) := by
  unfold FineBudget.stepReallocAdd
  dsimp only
  split
  · exact fineBudgetDom_stepAligned align newSz h
  · rcases h with ⟨hSB, hGS, hLB, hPB, hLC, hPC⟩
    unfold FineBudgetDom finePeak63Bytes finePeak63Count at *
    dsimp only
    exact ⟨by omega, by omega, hLB, by omega, hLC, by omega⟩

private theorem fineBudgetDom_step (ev : AllocEvent) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (fineCostModel.step ev b₁) (fineCostModel.step ev b₂) := by
  change FineBudgetDom (FineBudget.step (toFineEvent ev) b₁) (FineBudget.step (toFineEvent ev) b₂)
  cases ev with
  | alloc req => exact fineBudgetDom_stepAligned 16 req h
  | aligned align req => exact fineBudgetDom_stepAligned align req h
  | free align req => exact fineBudgetDom_stepFree align req h
  | realloc align oldSz newSz =>
    exact fineBudgetDom_stepFree align oldSz (fineBudgetDom_stepReallocAdd align newSz h)

private theorem fineBudgetDom_stepEvents :
    ∀ (evs : List AllocEvent) {b₁ b₂ : FineBudget},
      FineBudgetDom b₁ b₂ →
      FineBudgetDom (fineCostModel.stepEvents evs b₁) (fineCostModel.stepEvents evs b₂)
  | [], _, _, h => h
  | ev :: evs, _, _, h => fineBudgetDom_stepEvents evs (fineBudgetDom_step ev h)

private theorem fineMaxGroups_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineMaxGroups b₁ ≤ fineMaxGroups b₂ := by
  rcases h with ⟨_, hGS, _, _, _, hPC⟩
  unfold fineMaxGroups
  have hDiv :
      (b₁.cumSmallGroupsS + FineScale - 1) / FineScale ≤
        (b₂.cumSmallGroupsS + FineScale - 1) / FineScale :=
    Nat.div_le_div_right (by omega)
  omega

private theorem fineMaxMetaAreas_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineMaxMetaAreas b₁ ≤ fineMaxMetaAreas b₂ := by
  have hG := fineMaxGroups_mono_dom h
  unfold fineMaxMetaAreas
  have hDiv := Nat.div_le_div_right (c := 101) (a := 7 + fineMaxGroups b₁)
    (b := 7 + fineMaxGroups b₂) (by omega)
  omega

private theorem fineMaxDynIvs_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineMaxDynIvs b₁ ≤ fineMaxDynIvs b₂ := by
  have hG := fineMaxGroups_mono_dom h
  have hM := fineMaxMetaAreas_mono_dom h
  unfold fineMaxDynIvs
  omega

private theorem fineFootprint_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineFootprint b₁ ≤ fineFootprint b₂ := by
  have hM := fineMaxMetaAreas_mono_dom h
  rcases h with ⟨hSB, _, _, hPB, _, _⟩
  unfold fineFootprint
  omega

private theorem fineStepReserve_mono_dom (ev : AllocEvent) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    fineCostModel.stepReserve ev b₁ ≤ fineCostModel.stepReserve ev b₂ := by
  have hM := fineMaxMetaAreas_mono_dom h
  change fineStepReserve (toFineEvent ev) b₁ ≤ fineStepReserve (toFineEvent ev) b₂
  cases ev <;> exact FineStepBound_mono_meta hM

private theorem fitsEvents_of_fineBudgetDom {lim : BudgetLimits} :
    ∀ (evs : List AllocEvent) {b₁ b₂ : FineBudget},
      FineBudgetDom b₁ b₂ →
      FitsEvents fineCostModel lim b₂ evs →
      FitsEvents fineCostModel lim b₁ evs
  | [], _, _, _, _ => trivial
  | ev :: evs, _, _, hdom, ⟨⟨hw, hstep⟩, hrest⟩ =>
    ⟨⟨hw, hstep.mono (fineStepReserve_mono_dom ev hdom)
      (fineMaxDynIvs_mono_dom hdom) (fineFootprint_mono_dom hdom)⟩,
     fitsEvents_of_fineBudgetDom evs (fineBudgetDom_step ev hdom) hrest⟩

private theorem fitsEnv_of_fineBudgetDom {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {b₁ b₂ : FineBudget} (hdom : FineBudgetDom b₁ b₂)
    (h : FitsEnv fineCostModel lim b₂ Env) :
    FitsEnv fineCostModel lim b₁ Env :=
  fun evs hevs => fitsEvents_of_fineBudgetDom evs hdom (h evs hevs)

private theorem b2St4Cap_of_fineBudgetDom {lim : BudgetLimits} {i : Inputs} {c : CallV}
    {sg : StoresGhost} {b₁ b₂ : FineBudget} (hdom : FineBudgetDom b₁ b₂)
    (h : B2St4Cap fineCostModel lim i c sg b₂) :
    B2St4Cap fineCostModel lim i c sg b₁ :=
  fun ok => fitsEnv_of_fineBudgetDom hdom (h ok)

private theorem b2St3Cap_of_fineBudgetDom {lim : BudgetLimits} {io : IoModel}
    {RunEnv : RunCall → List AllocEvent → Prop} {Run : Inputs → RunAnswer → Prop}
    {i : Inputs} {c : CallV} {b₁ b₂ : FineBudget} (hdom : FineBudgetDom b₁ b₂)
    (h : B2St3Cap fineCostModel lim io RunEnv Run i c b₂) :
    B2St3Cap fineCostModel lim io RunEnv Run i c b₁ :=
  ⟨fun evs_f hf => fitsEvents_of_fineBudgetDom evs_f hdom (h.1 evs_f hf),
   fun a resP callP storesP inpP coinsP hrun =>
     let hr := h.2 a resP callP storesP inpP coinsP hrun
     ⟨fitsEnv_of_fineBudgetDom hdom hr.1,
      fun evs_r hevs_r =>
        let hr' := hr.2 evs_r hevs_r
        let hdom4 := fineBudgetDom_stepEvents evs_r hdom
        ⟨fun evs_f hf => fitsEvents_of_fineBudgetDom evs_f hdom4 (hr'.1 evs_f hf),
         fun sg out ha hpw => b2St4Cap_of_fineBudgetDom hdom4 (hr'.2 sg out ha hpw)⟩⟩⟩

private theorem b2St2Cap_of_fineBudgetDom {lim : BudgetLimits} {io : IoModel}
    {RunEnv : RunCall → List AllocEvent → Prop} {Run : Inputs → RunAnswer → Prop}
    {i : Inputs} {c : CallV} {b₁ b₂ : FineBudget} (hdom : FineBudgetDom b₁ b₂)
    (h : B2St2Cap fineCostModel lim io RunEnv Run i c b₂) :
    B2St2Cap fineCostModel lim io RunEnv Run i c b₁ :=
  ⟨fitsEnv_of_fineBudgetDom hdom h.1,
   fun evs_m3 hm3 =>
     let hdom3 := fineBudgetDom_stepEvents evs_m3 hdom
     ⟨fun evs_f hf => fitsEvents_of_fineBudgetDom evs_f hdom3 ((h.2 evs_m3 hm3).1 evs_f hf),
      fun hin => b2St3Cap_of_fineBudgetDom hdom3 ((h.2 evs_m3 hm3).2 hin)⟩⟩

private theorem fineBudgetDom_alloc64_realloc0_64 (b : FineBudget) :
    FineBudgetDom
      (fineCostModel.stepEvents (rustAllocEvents 64 8) b)
      (fineCostModel.stepEvents (rustReallocEvents (16 * 0) (16 * reserveCapStride 16 0 0 1) 8) b) := by
  have halloc : rustAllocEvents 64 8 = [.alloc 64] := by decide
  have hcap : reserveCapStride 16 0 0 1 = 4 := by decide
  have hrealloc :
      rustReallocEvents (16 * 0) (16 * reserveCapStride 16 0 0 1) 8 = [.realloc 8 0 64] := by
    rw [hcap]
    decide
  rw [halloc, hrealloc]
  have hg64 : ¬ Guaranteed63Threshold ≤ 64 := by decide
  have hm64 : 64 + (max 16 16 - 16) ≤ MmapThresholdReq := by decide
  have hm64' : 64 ≤ MmapThresholdReq := by decide
  have hg0 : ¬ Guaranteed63Threshold ≤ 0 := by decide
  have hcls1 : (64 + (max 16 16 - 16) + 3) / 16 = 4 := by decide
  have hcls2 : (64 + 3) / 16 = 4 := by decide
  simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil, fineCostModel,
    toFineEvent, FineBudget.step, FineBudget.stepAlloc, FineBudget.stepRealloc,
    FineBudget.stepAligned, FineBudget.stepReallocAdd, FineBudget.stepFree,
    hg64, hm64, hm64', hg0, hcls1, hcls2, ↓reduceIte]
  unfold FineBudgetDom finePeak63Bytes finePeak63Count
  dsimp only
  exact ⟨by omega, by omega, Nat.le_refl _, by omega, Nat.le_refl _, by omega⟩

private def rangeFrom : Nat → Nat → List Nat
  | _, 0 => []
  | k, rem + 1 => k :: rangeFrom (k + 1) rem

private theorem rangeFrom_succ_right (k rem : Nat) :
    rangeFrom k (rem + 1) = rangeFrom k rem ++ [k + rem] := by
  induction rem generalizing k with
  | zero => rfl
  | succ rem ih =>
    show k :: rangeFrom (k + 1) (rem + 1) = k :: (rangeFrom (k + 1) rem ++ [k + (rem + 1)])
    rw [ih (k + 1)]
    have hk : k + 1 + rem = k + (rem + 1) := by omega
    rw [hk]

private theorem list_range_eq_rangeFrom : ∀ (n : Nat), List.range n = rangeFrom 0 n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, list_range_eq_rangeFrom n, rangeFrom_succ_right 0 n, Nat.zero_add]

private theorem iterSeqEnv_m2CollectStepEnv_nil :
    ∀ (xs : List Nat), IterSeqEnv M2CollectStepEnv xs []
  | [] => rfl
  | _ :: _ => Or.inl (Or.inl rfl)

private theorem m2CollectLoopEnv_to_iterSeqEnv {n k : Nat} {evs : List AllocEvent}
    (h : M2CollectLoopEnv n k evs) :
    IterSeqEnv M2CollectStepEnv (rangeFrom k (n - k)) evs := by
  induction h with
  | done =>
    exact iterSeqEnv_m2CollectStepEnv_nil _
  | @skip k evs hk_lt _ ih =>
    have hrem : n - k = (n - (k + 1)) + 1 := by omega
    rw [hrem]
    exact Or.inr ⟨[], evs, rfl, Or.inl rfl, ih⟩
  | @grow k evs _ hk_lt _ ih =>
    have hrem : n - k = (n - (k + 1)) + 1 := by omega
    rw [hrem]
    exact Or.inr ⟨m2GrowEventsAt k, evs, rfl, Or.inr rfl, ih⟩

private theorem entryM2CollectEnv_fineBudgetDom_peak {n : Nat} (hn : 1 ≤ n)
    {evs_c : List AllocEvent} (st1 : FineBudget)
    (hevs_c :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget.M2CollectEnv
        n evs_c) :
    ∃ evs_c' : List AllocEvent,
      M2CollectEnv n evs_c' ∧
      FineBudgetDom (fineCostModel.stepEvents evs_c st1) (fineCostModel.stepEvents evs_c' st1) := by
  have hn_eq : List.range n = 0 :: rangeFrom 1 (n - 1) := by
    have h1 : n = (n - 1) + 1 := by omega
    rw [list_range_eq_rangeFrom n]
    conv => lhs; rw [h1]
    rfl
  rcases hevs_c with rfl | ⟨_, evs₂, rfl, rfl, hloop⟩
  · refine ⟨rustReallocEvents (16 * 0) (16 * reserveCapStride 16 0 0 1) 8, ?_,
      fineBudgetDom_alloc64_realloc0_64 st1⟩
    unfold M2CollectEnv
    rw [hn_eq]
    exact Or.inl (Or.inr rfl)
  · refine ⟨rustReallocEvents (16 * 0) (16 * reserveCapStride 16 0 0 1) 8 ++ evs₂, ?_, ?_⟩
    · unfold M2CollectEnv
      rw [hn_eq]
      exact Or.inr ⟨_, evs₂, rfl, Or.inr rfl, m2CollectLoopEnv_to_iterSeqEnv hloop⟩
    · have hL :
          fineCostModel.stepEvents (rustAllocEvents 64 8 ++ evs₂) st1 =
            fineCostModel.stepEvents evs₂ (fineCostModel.stepEvents (rustAllocEvents 64 8) st1) :=
        fineCostModel.stepEvents_append _ _ st1
      have hR :
          fineCostModel.stepEvents
              (rustReallocEvents (16 * 0) (16 * reserveCapStride 16 0 0 1) 8 ++ evs₂) st1 =
            fineCostModel.stepEvents evs₂
              (fineCostModel.stepEvents
                (rustReallocEvents (16 * 0) (16 * reserveCapStride 16 0 0 1) 8) st1) :=
        fineCostModel.stepEvents_append _ _ st1
      rw [hL, hR]
      exact fineBudgetDom_stepEvents evs₂ (fineBudgetDom_alloc64_realloc0_64 st1)

def B2St1Cap (M : AllocCostModel) (lim : BudgetLimits) (io : IoModel) (uuidParse : UuidParser)
    (RunEnv : RunCall → List AllocEvent → Prop) (Run : Inputs → RunAnswer → Prop)
    (i : Inputs) (st1 : M.σ) : Prop :=
  FitsEnv M lim st1 (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)) ∧
  ∀ (vcap : BitVec 64) (evs_c : List AllocEvent) (c : CallV),
    LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget.M2CollectEnv
      i.argv.length evs_c →
    vcap ≠ 0#64 →
    parseArgs uuidParse (i.argv.map bytesOfString) = some c →
    B2St2Cap M lim io RunEnv Run i c
      (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
        (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
          (M.stepEvents evs_c st1)))

def B2St0Cap (M : AllocCostModel) (st0 : M.σ) (i : Inputs) (st : M.σ) : Prop :=
  CliInputsOk i ∧ st = st0

theorem b2St0Cap_init (M : AllocCostModel) (st0 : M.σ) (i : Inputs) (hok : CliInputsOk i) :
    B2St0Cap M st0 i st0 :=
  ⟨hok, rfl⟩

theorem b2St01_of_mainEntryBudgetFitsCap {lim : BudgetLimits} {st0 : FineBudget}
    {io : IoModel} {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim st0 io uuidParse RunEnv Run)
    {i : Inputs} (hok : CliInputsOk i) (_hst0 : B2St0Cap fineCostModel st0 i st0)
    (hne : i.argv ≠ []) :
    FitsEvents fineCostModel lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
      B2St1Cap fineCostModel lim io uuidParse RunEnv Run i
        (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0) := by
  refine ⟨(hfitCap i hok).1 hne, ((hfitCap i hok).2 hne).1,
    fun vcap evs_c c hevs_c hvcap hp => ?_⟩
  have hn : 1 ≤ i.argv.length := Nat.succ_le_of_lt (List.length_pos_iff.mpr hne)
  let st1 := fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0
  obtain ⟨evs_c', hevs_c', hdom_c⟩ := entryM2CollectEnv_fineBudgetDom_peak hn st1 hevs_c
  have hdom2 :=
    fineBudgetDom_stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
      (fineBudgetDom_stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString)) hdom_c)
  have hm2 := ((hfitCap i hok).2 hne).2 vcap evs_c' c hevs_c' hvcap hp
  exact b2St2Cap_of_fineBudgetDom hdom2
    ⟨hm2.1, fun evs_m3 hm3 => ⟨(hm2.2 evs_m3 hm3).1, fun hin =>
      ⟨(hm2.2 evs_m3 hm3).1, (hm2.2 evs_m3 hm3).2 hin⟩⟩⟩

/-- Discharge `B2MainRemainingHops` over `B2St1Cap..B2St5Cap` from `AllocContractsFsPlaced`,
`MainIoPlaced`, and `MainIoBoundedPlaced`. -/
theorem b2MainRemainingHopsCap_of_allocFs_and_io [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      (B2St1Cap fineCostModel lim cliIo uuidTryParse RunEnv Run)
      (B2St2Cap fineCostModel lim cliIo RunEnv Run)
      (B2St3Cap fineCostModel lim cliIo RunEnv Run)
      (B2St4Cap fineCostModel lim)
      (B2St5Cap fineCostModel lim)
      RunEnv Run :=
  let hc := mainCalleesBlk617_of_allocFs_and_hooks_cliResStack hFs hstrlen hutf8 hmemrchr hpan
  { step2 :=
      b2_step2_pool_placed_of_hooks hc hstrlen hutf8 hmemrchr
        cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2 hstk cli_hstk64
        (fun hst1 _ _ => hst1.1)
        (fun hst1 _ _ hevs_c hvcap hp => hst1.2 _ _ _ hevs_c hvcap hp)
    step3 := fun hst2 hs0fs hs0tr hstdin hcoinsOk hcoins hpc hs _hpan hexit hnext =>
      main_m3_bounded_pool_placed_proof hc hioBounded hstk cli_hstk64 hs0fs hs0tr hstdin
        hcoinsOk hcoins hpc hst2.1 hs hexit
        fun s' cc cp ic ip evs hevs hin hat4 =>
          hnext s' cc cp ic ip _ ((hst2.2 evs hevs).2 hin) hin hat4
    step4_overCap := fun _hst3 hsp hs0tr hpc hover hs hpan hexit =>
      main_m4_sendOverCap_pool_placed_proof hc hstk cli_hstk64 hsp hs0tr hpc hover hs hpan hexit
    step4_call := fun hrun {_i _a _c _w s0 _s _buf _p0 coinsCap coinsPtr _inCap inPtr _ps _st3 _Q _Qp}
        hst3 hsp hs0tr hRun hnover hpc hs hpan hexit hnext =>
      let _ := coinsCap
      main_m4_pool_placed_proof hc hrun hstk cli_hstk64 hsp hs0tr hRun
        (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hpc⟩, hgt⟩)
        hpc
        (hst3.2 _
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
          inPtr coinsPtr hRun).1
        hs hpan hexit
        fun s' sg out evs hevs hans hwr htr hat4e =>
          hnext s' sg out _
            (((hst3.2 _
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
              inPtr coinsPtr hRun).2 evs hevs).2 sg out hans hwr)
            hans hwr htr hat4e
    step5 := fun hst4 _hs0tr hpaths hs _hpan hnext =>
      main_m5_proof_placed hc hio (hst4 false).seq_left hstk cli_hstk64 hpaths hs
        fun s' _evs ok outCap outPtr hevs hcom htr hstdout hat6 =>
          hnext s' ok outCap outPtr _ ((hst4 ok).seq_right hevs) hcom htr hstdout hat6
    step6 := fun hst5 hs hexit =>
      main_m6_m6Env_pool_proof_placed hc hio hst5 hstk cli_hstk64 hs hexit }

def B2St2CapOf (M : AllocCostModel) (lim : BudgetLimits) (io : IoModel)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (RunEnv : RunCall → List AllocEvent → Prop) (Run : Inputs → RunAnswer → Prop)
    (i : Inputs) (c : CallV) (st2 : M.σ) : Prop :=
  FitsEnv M lim st2 (M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c) ∧
  ∀ evs_m3 : List AllocEvent, M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c evs_m3 →
    (∀ evs_f : List AllocEvent, FreeOnlyEvs evs_f →
      FitsEvents M lim (M.stepEvents evs_m3 st2) evs_f) ∧
    ((inputOf i c).length ≤ stdinCapBytes →
      B2St3Cap M lim io RunEnv Run i c (M.stepEvents evs_m3 st2))

private theorem b2St2CapOf_of_fineBudgetDom {lim : BudgetLimits} {io : IoModel}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop} {Run : Inputs → RunAnswer → Prop}
    {i : Inputs} {c : CallV} {b₁ b₂ : FineBudget} (hdom : FineBudgetDom b₁ b₂)
    (h : B2St2CapOf fineCostModel lim io ReadEnv RunEnv Run i c b₂) :
    B2St2CapOf fineCostModel lim io ReadEnv RunEnv Run i c b₁ :=
  ⟨fitsEnv_of_fineBudgetDom hdom h.1,
   fun evs_m3 hm3 =>
     let hdom3 := fineBudgetDom_stepEvents evs_m3 hdom
     ⟨fun evs_f hf => fitsEvents_of_fineBudgetDom evs_f hdom3 ((h.2 evs_m3 hm3).1 evs_f hf),
      fun hin => b2St3Cap_of_fineBudgetDom hdom3 ((h.2 evs_m3 hm3).2 hin)⟩⟩

def B2St1CapOf (M : AllocCostModel) (lim : BudgetLimits) (io : IoModel)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (uuidParse : UuidParser)
    (RunEnv : RunCall → List AllocEvent → Prop) (Run : Inputs → RunAnswer → Prop)
    (i : Inputs) (st1 : M.σ) : Prop :=
  FitsEnv M lim st1 (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)) ∧
  ∀ (vcap : BitVec 64) (evs_c : List AllocEvent) (c : CallV),
    LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget.M2CollectEnv
      i.argv.length evs_c →
    vcap ≠ 0#64 →
    parseArgs uuidParse (i.argv.map bytesOfString) = some c →
    B2St2CapOf M lim io ReadEnv RunEnv Run i c
      (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
        (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
          (M.stepEvents evs_c st1)))

theorem b2St01_of_mainEntryBudgetFitsCapOf {lim : BudgetLimits} {st0 : FineBudget}
    {io : IoModel} {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {uuidParse : UuidParser}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim st0 io ReadEnv uuidParse RunEnv Run)
    {i : Inputs} (hok : CliInputsOk i) (_hst0 : B2St0Cap fineCostModel st0 i st0)
    (hne : i.argv ≠ []) :
    FitsEvents fineCostModel lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
      B2St1CapOf fineCostModel lim io ReadEnv uuidParse RunEnv Run i
        (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0) := by
  refine ⟨(hfitCap i hok).1 hne, ((hfitCap i hok).2 hne).1,
    fun vcap evs_c c hevs_c hvcap hp => ?_⟩
  have hn : 1 ≤ i.argv.length := Nat.succ_le_of_lt (List.length_pos_iff.mpr hne)
  let st1 := fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0
  obtain ⟨evs_c', hevs_c', hdom_c⟩ := entryM2CollectEnv_fineBudgetDom_peak hn st1 hevs_c
  have hdom2 :=
    fineBudgetDom_stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
      (fineBudgetDom_stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString)) hdom_c)
  have hm2 := ((hfitCap i hok).2 hne).2 vcap evs_c' c hevs_c' hvcap hp
  exact b2St2CapOf_of_fineBudgetDom hdom2
    ⟨hm2.1, fun evs_m3 hm3 => ⟨(hm2.2 evs_m3 hm3).1, fun hin =>
      ⟨(hm2.2 evs_m3 hm3).1, (hm2.2 evs_m3 hm3).2 hin⟩⟩⟩

/-- `ReadEnv`-parametric `B2MainRemainingHops` discharge from a single `MainIoOfPlaced` bundle. -/
theorem b2MainRemainingHopsCapOf_of_allocFs_and_io [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      (B2St1CapOf fineCostModel lim cliIo ReadEnv uuidTryParse RunEnv Run)
      (B2St2CapOf fineCostModel lim cliIo ReadEnv RunEnv Run)
      (B2St3Cap fineCostModel lim cliIo RunEnv Run)
      (B2St4Cap fineCostModel lim)
      (B2St5Cap fineCostModel lim)
      RunEnv Run :=
  let hc := mainCalleesBlk617_of_allocFs_and_hooks_cliResStack hFs hstrlen hutf8 hmemrchr hpan
  { step2 :=
      b2_step2_pool_placed_of_hooks hc hstrlen hutf8 hmemrchr
        cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2 hstk cli_hstk64
        (fun hst1 _ _ => hst1.1)
        (fun hst1 _ _ hevs_c hvcap hp => hst1.2 _ _ _ hevs_c hvcap hp)
    step3 := fun hst2 hs0fs hs0tr hstdin hcoinsOk hcoins hpc hs _hpan hexit hnext =>
      main_m3_bounded_readOf_pool_placed_proof hc hioOf hstk cli_hstk64 hs0fs hs0tr hstdin
        hcoinsOk hcoins hpc hst2.1 hs hexit
        fun s' cc cp ic ip evs hevs hin hat4 =>
          hnext s' cc cp ic ip _ ((hst2.2 evs hevs).2 hin) hin hat4
    step4_overCap := fun _hst3 hsp hs0tr hpc hover hs hpan hexit =>
      main_m4_sendOverCap_pool_placed_proof hc hstk cli_hstk64 hsp hs0tr hpc hover hs hpan hexit
    step4_call := fun hrun {_i _a _c _w s0 _s _buf _p0 coinsCap coinsPtr _inCap inPtr _ps _st3 _Q _Qp}
        hst3 hsp hs0tr hRun hnover hpc hs hpan hexit hnext =>
      let _ := coinsCap
      main_m4_pool_placed_proof hc hrun hstk cli_hstk64 hsp hs0tr hRun
        (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hpc⟩, hgt⟩)
        hpc
        (hst3.2 _
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
          inPtr coinsPtr hRun).1
        hs hpan hexit
        fun s' sg out evs hevs hans hwr htr hat4e =>
          hnext s' sg out _
            (((hst3.2 _
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
              inPtr coinsPtr hRun).2 evs hevs).2 sg out hans hwr)
            hans hwr htr hat4e
    step5 := fun hst4 _hs0tr hpaths hs _hpan hnext =>
      main_m5_of_proof_placed hc hioOf (hst4 false).seq_left hstk cli_hstk64 hpaths hs
        fun s' _evs ok outCap outPtr hevs hcom htr hstdout hat6 =>
          hnext s' ok outCap outPtr _ ((hst4 ok).seq_right hevs) hcom htr hstdout hat6
    step6 := fun hst5 hs hexit =>
      main_m6_of_m6Env_pool_proof_placed hc hioOf hst5 hstk cli_hstk64 hs hexit }

/-! ## Block `579 → 617` and `MainOkCliExt*B2NeedLocksPlacedAt` lifts -/

theorem b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCap_lsmpl [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
    hlibc hfs_eq hparse hstrlen hFs
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCap hfitCap)
    hrun
    (b2MainRemainingHopsCap_of_allocFs_and_io hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk)

theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_lsmpl [LibsignalPlacement]
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
    (Dom : Inputs → Prop) (S : RunSem)
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
      St1 St2 St3 St4 St5 RunEnv (domScopedRun Dom (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
    hlibc hfs_eq (hparse_of_domains fun _ _ hr => domScopedRun_dom hr)
    hstrlen_row hc_alloc hSt0 hSt01
    (subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun)
    hhops

theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_lsmpl
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv (domScopedRun Dom (runRel S)))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_lsmpl Dom S
    hlibc hfs_eq hstrlen hFs
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCap hfitCap)
    hrun
    (b2MainRemainingHopsCap_of_allocFs_and_io hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk)

theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
      ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv (domScopedRun Dom (runRel S)))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (domScopedRun Dom (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_lsmpl Dom S
    hlibc hfs_eq hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk hfitCap hrun

/-- Assemble `MainOkCliExtPqB2NeedLocksPlacedAt` from Block-`579` `runSpecTightPlaced` and
`MainEntryBudgetFitsCap`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (errOf : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (errOf W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hio W γ tp) (hioBounded W γ tp)
        (hstrlen W) (hutf8 W) (hmemrchr W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-- Assemble `MainOkCliExtOverB2NeedLocksPlacedAt` from Block-`579` `runSpecTightPlaced` and
`MainEntryBudgetFitsCap`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (errOf : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (errOf W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hio W γ tp) (hioBounded W γ tp)
        (hstrlen W) (hutf8 W) (hmemrchr W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-! ## `cliGhostExterns` and `cliExternsPlaced` specializations -/

theorem cliExternsPlaced_handleErrorMain (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsHandleErrorSymMain = some Rust.panicked :=
  cliExternsPlaced_panic_all mmpl W lsHandleErrorSymMain (by decide)

theorem cliGhostExterns_strlen (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) "strlen" = some strlenHook :=
  (cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans (cliExternsPlaced_strlen mmpl W)

theorem cliGhostExterns_writeFile (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsWriteFileSym = some writeFileHook :=
  (cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans (cliExternsPlaced_writeFile mmpl W)

theorem cliGhostExterns_writeStdout (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsWriteStdoutSym = some writeStdoutHook :=
  (cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans (cliExternsPlaced_writeStdout mmpl W)

theorem cliGhostExterns_handleErrorMain (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsHandleErrorSymMain = some Rust.panicked :=
  cliGhostExterns_panic_all mmpl gh W lsHandleErrorSymMain (by decide)

theorem writeStdoutHook_budget_ok_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutSpecPlaced A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [writeStdoutSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases CryptoVerification.SignalSession.Cli.MainHops.writeStdoutHook_ok_placed stk x
      (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [writeStdoutSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (writeStdoutHook s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (writeStdoutHook s0) (vmPreserved_writeStdoutHook s0)
    have hrest' : (writeStdoutHook s0).mem ⊨
        ((x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨writeStdoutEnv_nil, hres⟩ (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem writeFileHook_budget_ok_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeFileHook (writeFileSpecPlaced cliIo A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [writeFileSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases CryptoVerification.SignalSession.Cli.MainHops.writeFileHook_ok_placed stk x
      (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [writeFileSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (writeFileHook s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (writeFileHook s0) (vmPreserved_writeFileHook s0)
    have hrest' : (writeFileHook s0).mem ⊨
        ((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono
      (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨writeFileEnv_nil x.path.length, hres⟩ (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem writeFile_budget_rocl_ok_of_lookup [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} (stk : Nat)
    (hLookup : H lsWriteFileSym = some writeFileHook) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlaced cliIo A lim stk)) :=
  ls_hook_placed_rocl_ok_local ⟨writeFileHook, hLookup, writeFileHook_budget_ok_placed A lim stk⟩

theorem writeStdout_budget_rocl_ok_of_lookup [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} (stk : Nat)
    (hLookup : H lsWriteStdoutSym = some writeStdoutHook) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced A lim stk)) :=
  ls_hook_placed_rocl_ok_local ⟨writeStdoutHook, hLookup, writeStdoutHook_budget_ok_placed A lim stk⟩

theorem mainIoPlaced_cliExterns_of_readSubroutines [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A lim stk)))
    (hReadFile : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk))) :
    MainIoPlaced A lim (cliExternsPlaced mmpl W) cliIo stk where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_budget_rocl_ok_of_lookup stk (cliExternsPlaced_writeFile mmpl W)
  writeStdout := writeStdout_budget_rocl_ok_of_lookup stk (cliExternsPlaced_writeStdout mmpl W)

theorem mainIoBoundedPlaced_cliExterns_of_readSubroutines [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced cliIo A lim stk StdinEnv)))
    (hReadFile : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk))) :
    MainIoBoundedPlaced A lim (cliExternsPlaced mmpl W) cliIo stk StdinEnv where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_budget_rocl_ok_of_lookup stk (cliExternsPlaced_writeFile mmpl W)
  writeStdout := writeStdout_budget_rocl_ok_of_lookup stk (cliExternsPlaced_writeStdout mmpl W)

theorem mainIoPlaced_cliGhostExterns_of_readSubroutines [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin :
      subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadStdinSym) (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A lim stk)))
    (hReadFile :
      subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk))) :
    MainIoPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliIo stk where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_budget_rocl_ok_of_lookup stk (cliGhostExterns_writeFile mmpl gh W)
  writeStdout := writeStdout_budget_rocl_ok_of_lookup stk (cliGhostExterns_writeStdout mmpl gh W)

theorem mainIoBoundedPlaced_cliGhostExterns_of_readSubroutines [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin :
      subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadStdinSym)
        (withLsRoCl lsmpl (readStdinSpecOfPlaced cliIo A lim stk StdinEnv)))
    (hReadFile :
      subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk))) :
    MainIoBoundedPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliIo stk StdinEnv where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_budget_rocl_ok_of_lookup stk (cliGhostExterns_writeFile mmpl gh W)
  writeStdout := writeStdout_budget_rocl_ok_of_lookup stk (cliGhostExterns_writeStdout mmpl gh W)

theorem mainCalleesBlk617_cliGhostExterns_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    MainCalleesBlk617 A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
      uuidTryParse hookStack cliResStack :=
  mainCalleesBlk617_of_allocFs_and_hooks_cliResStack
    (allocContractsFsPlaced_of_hooks mmpl gh W hG)
    (cliGhostExterns_strlen mmpl gh W)
    (cliGhostExterns_fromUtf8_eq mmpl gh W)
    (cliGhostExterns_memrchr_eq mmpl gh W)
    (cliGhostExterns_handleErrorMain mmpl gh W)

theorem mainCalleesBlk617_cliExterns_of_allocFs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack : Nat}
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hFs : AllocContractsFsPlaced A lim (cliExternsPlaced mmpl W)) :
    MainCalleesBlk617 A lim (cliExternsPlaced mmpl W) uuidTryParse hookStack cliResStack :=
  mainCalleesBlk617_of_allocFs_and_hooks_cliResStack hFs
    (cliExternsPlaced_strlen mmpl W)
    (cliExternsPlaced_fromUtf8 mmpl W)
    (cliExternsPlaced_memrchr mmpl W)
    (cliExternsPlaced_handleErrorMain mmpl W)

theorem b2MainRemainingHopsCap_cliGhostExterns_of_hooks [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (ghOf : CliHooks → CliGhostHooks) (W : CliHooks)
    {brkStart : BitVec 64} {lim : BudgetLimits} {γ : GhostName} {tp : BitVec 64}
    {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl
      (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) W brkStart lim γ tp
      (B2St1Cap fineCostModel lim cliIo uuidTryParse RunEnv Run)
      (B2St2Cap fineCostModel lim cliIo RunEnv Run)
      (B2St3Cap fineCostModel lim cliIo RunEnv Run)
      (B2St4Cap fineCostModel lim)
      (B2St5Cap fineCostModel lim)
      RunEnv Run :=
  b2MainRemainingHopsCap_of_allocFs_and_io
    (allocContractsFsPlaced_of_hooks mmpl (ghOf W) W hG)
    hio hioBounded
    (cliGhostExterns_strlen mmpl (ghOf W) W)
    (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk

theorem b2MainRemainingHopsCap_cliExterns_of_allocFs_and_io [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {brkStart : BitVec 64} {lim : BudgetLimits} {γ : GhostName} {tp : BitVec 64}
    {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliExternsPlaced mmpl W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliExternsPlaced mmpl W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliExternsPlaced mmpl W) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl (cliExternsPlaced mmpl) W brkStart lim γ tp
      (B2St1Cap fineCostModel lim cliIo uuidTryParse RunEnv Run)
      (B2St2Cap fineCostModel lim cliIo RunEnv Run)
      (B2St3Cap fineCostModel lim cliIo RunEnv Run)
      (B2St4Cap fineCostModel lim)
      (B2St5Cap fineCostModel lim)
      RunEnv Run :=
  b2MainRemainingHopsCap_of_allocFs_and_io hFs hio hioBounded
    (cliExternsPlaced_strlen mmpl W)
    (cliExternsPlaced_fromUtf8 mmpl W)
    (cliExternsPlaced_memrchr mmpl W)
    (cliExternsPlaced_handleErrorMain mmpl W)
    hstk

theorem b2MainSpecTightNeedLocksFineAt_cliGhostExterns_of_runTight_and_budgetFitsCap_lsmpl
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (ghOf : CliHooks → CliGhostHooks) (W : CliHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : subroutine_ok
      (mProgPlaced (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok
      (cliProgExtPlacedAt lsmpl
        (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) 617 W)
      (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCap_lsmpl
    hlibc hfs_eq hparse
    (allocContractsFsPlaced_of_hooks mmpl (ghOf W) W hG)
    hio hioBounded
    (cliGhostExterns_strlen mmpl (ghOf W) W)
    (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

theorem b2MainSpecTightNeedLocksFineAt_cliExterns_of_runTight_and_budgetFitsCap_lsmpl
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliExternsPlaced mmpl W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliExternsPlaced mmpl W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliExternsPlaced mmpl W) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : subroutine_ok (mProgPlaced (cliExternsPlaced mmpl W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCap_lsmpl
    hlibc hfs_eq hparse hFs hio hioBounded
    (cliExternsPlaced_strlen mmpl W)
    (cliExternsPlaced_fromUtf8 mmpl W)
    (cliExternsPlaced_memrchr mmpl W)
    (cliExternsPlaced_handleErrorMain mmpl W)
    hstk hfitCap hrun

theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim (ghOf W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    (fun W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl (ghOf W) W (hG W γ tp))
    hio hioBounded
    (fun W => cliGhostExterns_strlen mmpl (ghOf W) W)
    (fun W => cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim (ghOf W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    (fun W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl (ghOf W) W (hG W γ tp))
    hio hioBounded
    (fun W => cliGhostExterns_strlen mmpl (ghOf W) W)
    (fun W => cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCap
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    hFs hio hioBounded
    (cliExternsPlaced_strlen mmpl)
    (cliExternsPlaced_fromUtf8 mmpl)
    (cliExternsPlaced_memrchr mmpl)
    (cliExternsPlaced_handleErrorMain mmpl)
    hstk hfitCap hrun

theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCap
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    hFs hio hioBounded
    (cliExternsPlaced_strlen mmpl)
    (cliExternsPlaced_fromUtf8 mmpl)
    (cliExternsPlaced_memrchr mmpl)
    (cliExternsPlaced_handleErrorMain mmpl)
    hstk hfitCap hrun

/-! ## `MainIoOfPlaced` and `MainEntryBudgetFitsCapOf` specializations -/

theorem mainIoOfPlaced_cliExterns_of_readSubroutines [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecOfPlaced cliIo A lim stk StdinEnv)))
    (hReadFile : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk ReadEnv))) :
    MainIoOfPlaced A lim (cliExternsPlaced mmpl W) cliIo stk StdinEnv ReadEnv where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_budget_rocl_ok_of_lookup stk (cliExternsPlaced_writeFile mmpl W)
  writeStdout := writeStdout_budget_rocl_ok_of_lookup stk (cliExternsPlaced_writeStdout mmpl W)

theorem mainIoOfPlaced_cliGhostExterns_of_readSubroutines [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StdinEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat)
    (hReadStdin :
      subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadStdinSym)
        (withLsRoCl lsmpl (readStdinSpecOfPlaced cliIo A lim stk StdinEnv)))
    (hReadFile :
      subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A lim stk ReadEnv))) :
    MainIoOfPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliIo stk StdinEnv ReadEnv where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_budget_rocl_ok_of_lookup stk (cliGhostExterns_writeFile mmpl gh W)
  writeStdout := writeStdout_budget_rocl_ok_of_lookup stk (cliGhostExterns_writeStdout mmpl gh W)

theorem b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCapOf_lsmpl [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv Run)
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl
    hlibc hfs_eq hparse hstrlen hFs
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCapOf hfitCap)
    hrun
    (b2MainRemainingHopsCapOf_of_allocFs_and_io hFs hioOf hstrlen hutf8 hmemrchr hpan hstk)

theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv (domScopedRun Dom (runRel S)))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_lsmpl Dom S
    hlibc hfs_eq hstrlen hFs
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCapOf hfitCap)
    hrun
    (b2MainRemainingHopsCapOf_of_allocFs_and_io hFs hioOf hstrlen hutf8 hmemrchr hpan hstk)

theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
      ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : ext W lsMemrchrSym = some memrchrHook)
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv (domScopedRun Dom (runRel S)))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (domScopedRun Dom (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl Dom S
    hlibc hfs_eq hFs hioOf hstrlen hutf8 hmemrchr hpan hstk hfitCap hrun

/-- Assemble `MainOkCliExtPqB2NeedLocksPlacedAt` from `MainEntryBudgetFitsCapOf` and
`MainIoOfPlaced`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (errOf : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (errOf W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hioOf W γ tp)
        (hstrlen W) (hutf8 W) (hmemrchr W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (errOf : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (errOf W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hioOf W γ tp)
        (hstrlen W) (hutf8 W) (hmemrchr W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

theorem b2MainRemainingHopsCapOf_cliGhostExterns_of_hooks [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (ghOf : CliHooks → CliGhostHooks) (W : CliHooks)
    {brkStart : BitVec 64} {lim : BudgetLimits} {γ : GhostName} {tp : BitVec 64}
    {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
      ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl
      (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) W brkStart lim γ tp
      (B2St1CapOf fineCostModel lim cliIo ReadEnv uuidTryParse RunEnv Run)
      (B2St2CapOf fineCostModel lim cliIo ReadEnv RunEnv Run)
      (B2St3Cap fineCostModel lim cliIo RunEnv Run)
      (B2St4Cap fineCostModel lim)
      (B2St5Cap fineCostModel lim)
      RunEnv Run :=
  b2MainRemainingHopsCapOf_of_allocFs_and_io
    (allocContractsFsPlaced_of_hooks mmpl (ghOf W) W hG)
    hioOf
    (cliGhostExterns_strlen mmpl (ghOf W) W)
    (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk

theorem b2MainSpecTightNeedLocksFineAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_lsmpl
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (ghOf : CliHooks → CliGhostHooks) (W : CliHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hG : CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      lim (ghOf W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
      ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv Run)
    (hrun : subroutine_ok
      (mProgPlaced (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok
      (cliProgExtPlacedAt lsmpl
        (fun W' => cliGhostExterns (ghOf W') (cliExternsPlaced mmpl W')) 617 W)
      (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCapOf_lsmpl
    hlibc hfs_eq hparse
    (allocContractsFsPlaced_of_hooks mmpl (ghOf W) W hG)
    hioOf
    (cliGhostExterns_strlen mmpl (ghOf W) W)
    (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    (fun W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl (ghOf W) W (hG W γ tp))
    hioOf
    (fun W => cliGhostExterns_strlen mmpl (ghOf W) W)
    (fun W => cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    (fun W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl (ghOf W) W (hG W γ tp))
    hioOf
    (fun W => cliGhostExterns_strlen mmpl (ghOf W) W)
    (fun W => cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_memrchr_eq mmpl (ghOf W) W)
    (fun W => cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCapOf
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    hFs hioOf
    (cliExternsPlaced_strlen mmpl)
    (cliExternsPlaced_fromUtf8 mmpl)
    (cliExternsPlaced_memrchr mmpl)
    (cliExternsPlaced_handleErrorMain mmpl)
    hstk hfitCap hrun

theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCapOf
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI CliHooks.utf8Err RunEnv hlibc
    hFs hioOf
    (cliExternsPlaced_strlen mmpl)
    (cliExternsPlaced_fromUtf8 mmpl)
    (cliExternsPlaced_memrchr mmpl)
    (cliExternsPlaced_handleErrorMain mmpl)
    hstk hfitCap hrun

end LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
