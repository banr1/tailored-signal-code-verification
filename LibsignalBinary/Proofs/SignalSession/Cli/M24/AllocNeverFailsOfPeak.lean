/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Heap.Fine.SpecBudgetFine
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Peak-Bound `CliPqxdhAllocNeverFailsPlaced` and Strict Recovery

Derives `CliPqxdhAllocNeverFailsPlaced` and strict (`0`-excused-abort) placed ELF/binary
correctness from a whole-CLI `PhaseCreditSpec` or `FitsEnv` peak allocation bound under
`fineCostModel`, initializes the `NoOom` global-allocator thunk contracts across startup, and
defines the concrete `1 GiB` budget limits `cliM24DefaultLimits`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AllocNeverFailsOfPeak

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhBinaryCorrectPlaced CliPqxdhBinaryCorrectPlacedAt CliPqxdhElfCorrectPlaced
   CliPqxdhInputs CliReachesOOMPlaced Inputs cliProcessInputs libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced cliProgPlacedSig)
open LibsignalBinary.Heap
  (AllocEvent BudgetLimits FitsEnv RustAllocAddrs RustCliAllocBudget RustCliAllocNoOomEntriesBase
   rustCliAllocNoOomSpecBase subroutine_ok_allocNoOom_of_budgetBase)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout FineBudget FineStepBound StartupVmPreserved allocMemsetVmSpec
   cliElf_fineBudgetPool_of_init fineCostModel fineHookBudgetPool_of_codeLoaded
   fineHookRustCliAllocBudget fineHookRustCliAllocBudgetEntries_thunks
   fineHookRustCliAllocZeroedBudget_thunk_ok rdlAllocZeroedInstrs stringCloneHookMallocng)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineDynIvsOfCum fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineStepReserveOfCum)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (NonVacTwoPhaseEnv fitsEnv_fineCostModel_of_phaseCredit nonVacTwoPhase_phaseCreditSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
  (PreservesNoAllocFailed cliM2ProgPlacedSig cliM2_allocNeverFailsPlaced
   preservesNoAllocFailed_stepRustAlloc1)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
  (CliPqxdhAllocNeverFailsPlaced CliPqxdhBinaryCorrectStrictPlaced
   CliPqxdhBinaryCorrectStrictPlacedAt CliPqxdhElfCorrectStrictPlaced CliRunAllocFailsPlaced
   cliPqxdhBinaryCorrectStrictPlaced_of_upToAllocFailure
   cliPqxdhBinaryCorrectStrictPlacedAt_of_upToAllocFailure
   cliPqxdhElfCorrectStrictPlaced_of_upToAllocFailure)
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries.Mallocng
  (MallocngAuxvAt MallocngRuntime mallocngAddrsOfPlacement)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng)
open VerifiedLibraries.RustStd
  (RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs)

/-! ## Peak allocation bound predicates -/

/-- Top-level `PhaseCreditSpec` bound across all inputs in `CliPqxdhInputs W`. -/
def M23bPhaseCreditHyp
    (EnvOf : PEParams → Inputs → List AllocEvent → Prop)
    (W : PEParams) (cumB liveB peakB maxReq : Nat) : Prop :=
  ∀ i : Inputs, CliPqxdhInputs W i →
    PhaseCreditSpec fineCostModel (EnvOf W i) cumB liveB peakB maxReq

/-- Top-level `FitsEnv fineCostModel lim fineCostModel.init` bound across `CliPqxdhInputs W`. -/
def M23bFitsEnvHyp
    (lim : BudgetLimits)
    (EnvOf : PEParams → Inputs → List AllocEvent → Prop)
    (W : PEParams) : Prop :=
  ∀ i : Inputs, CliPqxdhInputs W i →
    FitsEnv fineCostModel lim fineCostModel.init (EnvOf W i)

/-- Derive `M23bFitsEnvHyp` from `M23bPhaseCreditHyp` and physical/virtual capacity bounds. -/
theorem m23bFitsEnvHyp_of_phaseCredit
    {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    {W : PEParams} {cumB liveB peakB maxReq : Nat}
    (hSpec : M23bPhaseCreditHyp EnvOf W cumB liveB peakB maxReq)
    (hlp : liveB ≤ peakB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    M23bFitsEnvHyp lim EnvOf W :=
  fun i hi => fitsEnv_fineCostModel_of_phaseCredit (hSpec i hi) hlp henf hram hva

/-! ## Startup `physMemAvail` preservation and `NoOom` allocator thunks -/

/-- `stringCloneHookMallocng mpl` preserves `allocFailedEvent ∉ s.trace`. -/
theorem preservesNoAllocFailed_stringCloneHookMallocng (mpl : Obj.MultiPlacement) :
    PreservesNoAllocFailed (stringCloneHookMallocng mpl) := by
  intro s0 hs0
  unfold stringCloneHookMallocng
  dsimp only
  split
  · exact hs0
  · refine preservesNoAllocFailed_stepRustAlloc1 mpl false _ _ (fun s1 _ hs1 => ?_) s0 hs0
    exact hs1

/-- Initialize `fineHookRustCliAllocBudget` at `main` entry together with `NoOom` contracts for
`__rust_{alloc,dealloc,realloc,alloc_zeroed}`. -/
theorem cliElf_fineHookNoOomInit_of_startup
    {P : Program} {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {thunkAddrs rdlAddrs : RustAllocAddrs}
    {allocZeroedThunkAddr allocZeroedRdlAddr memcpyAddr memsetAddr : BitVec 64}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hP : ProgContainsMallocng P mpl)
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem)
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hZeroThunk : hasInstrs P allocZeroedThunkAddr [.b (allocZeroedRdlAddr - allocZeroedThunkAddr)])
    (hZeroCode : hasInstrs P allocZeroedRdlAddr
      (rdlAllocZeroedInstrs allocZeroedRdlAddr (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc")
        (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineHookRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocNoOomEntriesBase fineCostModel A lim P thunkAddrs ∧
      subroutine_ok P allocZeroedThunkAddr (rustCliAllocNoOomSpecBase fineCostModel A lim true) := by
  obtain ⟨γ, hPool⟩ := cliElf_fineBudgetPool_of_init hLayout hLoad hVm htpLo htpHi hmem
  exact ⟨γ,
    fineHookBudgetPool_of_codeLoaded hCL hPool,
    (fineHookRustCliAllocBudgetEntries_thunks hP γ s0.tpidrEl0 s0.brkStart
      hThunks hShims hMemcpy).toNoOom lim,
    subroutine_ok_allocNoOom_of_budgetBase
      (fineHookRustCliAllocZeroedBudget_thunk_ok hP γ s0.tpidrEl0 s0.brkStart
        allocZeroedThunkAddr allocZeroedRdlAddr memsetAddr lim hZeroThunk hZeroCode hMemset)⟩

/-! ## `CliPqxdhAllocNeverFailsPlaced` and strict recovery -/

/-- Derive `CliPqxdhAllocNeverFailsPlaced` from `M23bFitsEnvHyp`. -/
theorem cliPqxdhAllocNeverFailsPlaced_of_peak
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    (hPeak : M23bFitsEnvHyp lim EnvOf ⟨W.C, W.Q⟩)
    (hLayout : CliElfMallocngLayout elf lim)
    (hRunEnv : CliElfMallocngLayout elf lim →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliRunAllocFailsPlaced mpl mmpl elf W i →
        ¬ FitsEnv fineCostModel lim fineCostModel.init (EnvOf ⟨W.C, W.Q⟩ i)) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W := by
  intro i hi s0 s hload hsteps hmem
  exact hRunEnv hLayout i hi ⟨s0, s, hload, hsteps, hmem⟩ (hPeak i hi)

theorem cliPqxdhAllocNeverFailsPlaced_of_phaseCredit
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    {cumB liveB peakB maxReq : Nat}
    (hSpec : M23bPhaseCreditHyp EnvOf ⟨W.C, W.Q⟩ cumB liveB peakB maxReq)
    (hlp : liveB ≤ peakB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48)
    (hLayout : CliElfMallocngLayout elf lim)
    (hRunEnv : CliElfMallocngLayout elf lim →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliRunAllocFailsPlaced mpl mmpl elf W i →
        ¬ FitsEnv fineCostModel lim fineCostModel.init (EnvOf ⟨W.C, W.Q⟩ i)) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W :=
  cliPqxdhAllocNeverFailsPlaced_of_peak
    (m23bFitsEnvHyp_of_phaseCredit hSpec hlp henf hram hva)
    hLayout hRunEnv

/-- Derive `CliPqxdhAllocNeverFailsPlaced` from `cliProgPlacedSig = cliM2ProgPlacedSig`. -/
theorem cliPqxdhAllocNeverFailsPlaced_of_m2ProgEq
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (hProg : cliProgPlacedSig mpl mmpl W = cliM2ProgPlacedSig mpl mmpl W) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W := by
  intro i _ s0 s hload hsteps
  rw [hProg] at hsteps
  exact cliM2_allocNeverFailsPlaced mpl mmpl elf W i s0 s hload hsteps

theorem cliPqxdhNoOomPlaced_of_peak
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    (hPeak : M23bFitsEnvHyp lim EnvOf ⟨W.C, W.Q⟩)
    (hLayout : CliElfMallocngLayout elf lim)
    (hRunEnv : CliElfMallocngLayout elf lim →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesOOMPlaced mpl mmpl elf W i →
        ¬ FitsEnv fineCostModel lim fineCostModel.init (EnvOf ⟨W.C, W.Q⟩ i)) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  fun i hi hOom => hRunEnv hLayout i hi hOom (hPeak i hi)

theorem cliPqxdhElfCorrectStrictPlaced_of_peak
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    (hElf : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hLayout : CliElfMallocngLayout elf lim)
    (hPeak : ∀ W : PEParams, M23bFitsEnvHyp lim EnvOf W)
    (hRunEnv : ∀ W : CliHooks, CliElfMallocngLayout elf lim →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesOOMPlaced mpl mmpl elf W i →
        ¬ FitsEnv fineCostModel lim fineCostModel.init (EnvOf ⟨W.C, W.Q⟩ i)) :
    CliPqxdhElfCorrectStrictPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced_of_upToAllocFailure hElf fun W =>
    cliPqxdhNoOomPlaced_of_peak (hPeak ⟨W.C, W.Q⟩) hLayout (hRunEnv W)

theorem cliPqxdhBinaryCorrectStrictPlacedAt_of_peak
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)} {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    (hBin : CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes)
    (hLayout : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf → CliElfMallocngLayout elf lim)
    (hPeak : ∀ W : PEParams, M23bFitsEnvHyp lim EnvOf W)
    (hRunEnv : ∀ (elf : ElfImage) (W : CliHooks),
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      CliElfMallocngLayout elf lim →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesOOMPlaced mpl mmpl elf W i →
        ¬ FitsEnv fineCostModel lim fineCostModel.init (EnvOf ⟨W.C, W.Q⟩ i)) :
    CliPqxdhBinaryCorrectStrictPlacedAt mpl mmpl bytes :=
  cliPqxdhBinaryCorrectStrictPlacedAt_of_upToAllocFailure hBin fun elf W hparse hCode =>
    cliPqxdhNoOomPlaced_of_peak (hPeak ⟨W.C, W.Q⟩) (hLayout elf hparse)
      (hRunEnv elf W hparse hCode)

theorem cliPqxdhBinaryCorrectStrictPlaced_of_peak
    {bytes : List (BitVec 8)} {lim : BudgetLimits}
    {EnvOf : PEParams → Inputs → List AllocEvent → Prop}
    (hBin : CliPqxdhBinaryCorrectPlaced bytes)
    (hLayout : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf → CliElfMallocngLayout elf lim)
    (hPeak : ∀ W : PEParams, M23bFitsEnvHyp lim EnvOf W)
    (hRunEnv : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks),
      libsignalSessionLib.LinkedAt bytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      CliElfMallocngLayout elf lim →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesOOMPlaced mpl mmpl elf W i →
        ¬ FitsEnv fineCostModel lim fineCostModel.init (EnvOf ⟨W.C, W.Q⟩ i)) :
    CliPqxdhBinaryCorrectStrictPlaced bytes :=
  cliPqxdhBinaryCorrectStrictPlaced_of_upToAllocFailure hBin
    fun mpl mmpl elf W hLink hMLink hparse hCode =>
      cliPqxdhNoOomPlaced_of_peak (hPeak ⟨W.C, W.Q⟩) (hLayout elf hparse)
        (hRunEnv mpl mmpl elf W hLink hMLink hparse hCode)

/-! ## Concrete `1 GiB` `BudgetLimits` -/

/-- Concrete `1 GiB` (`2 ^ 30` B) `BudgetLimits` (`staticCount = 64`, `staticBytes = 16 MiB`). -/
def cliM24DefaultLimits : BudgetLimits where
  staticCount := 64
  staticBytes := 16 * 1024 * 1024
  physCap := 2 ^ 30
  enforced := true

/-- Non-vacuity witness: `cliM24DefaultLimits` satisfies `FitsEnv` on `NonVacTwoPhaseEnv`. -/
theorem cliM24DefaultLimits_nonVac_fitsEnv :
    FitsEnv fineCostModel cliM24DefaultLimits fineCostModel.init NonVacTwoPhaseEnv := by
  have hstep : fineStepReserveOfCum 200000 16 3628 = 21704704 := by
    unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum Arm64.pageAlignUp PAGE_SIZE
    omega
  have hdyn : fineDynIvsOfCum 3628 = 316 := by
    unfold fineDynIvsOfCum fineMaxMetaAreasOfCum fineMaxGroupsOfCum
    omega
  have hsc : cliM24DefaultLimits.staticCount = 64 := rfl
  have hsb : cliM24DefaultLimits.staticBytes = 16 * 1024 * 1024 := rfl
  have hcap : cliM24DefaultLimits.physCap = 2 ^ 30 := rfl
  refine fitsEnv_fineCostModel_of_phaseCredit nonVacTwoPhase_phaseCreditSpec
    (by omega) rfl ?_ ?_
  · rw [hsb, hcap, hstep]
    omega
  · rw [hsc, hsb, hdyn, hstep]
    unfold MMAP_MIN_ADDR PAGE_SIZE
    omega

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AllocNeverFailsOfPeak
