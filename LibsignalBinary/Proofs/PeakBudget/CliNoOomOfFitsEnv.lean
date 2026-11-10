/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1Placed
public import ProofLib.SepLogic.WPp

/-!
# Whole-Program `FitsEnv` to Never-OOM and Strict Placed CLI Composition

Connects whole-`main` `FitsEnv fineCostModel` bounds to placed ELF execution correctness and
absence of `.OutOfMemory` (`¬ CliReachesOOMExtPlacedAt` and `CliPqxdhAllocNeverFailsPlaced`) across
all PQXDH/SPQR CLI subcommands, both for parametric `CliRunCalleeEnvs` families and for
`mkExistentialRealCalleeEnvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv

open Arm64 (GhostName Memory State Steps subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (ElfImage ProcessInputs ProcessTerminatedOutcome bytesOfString)
open CryptoVerification (libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives wirePrekey wireWhisper)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhElfCorrectPlaced CliPqxdhInputs CliReachesOOMPlaced CliRun
   CliSpecPqxdh CliSpecPqxdhNoMatch Inputs Outcome PqSessionMatches cliExternsPlaced
   cliInputs_eq_cliProcessInputs cliProcessInputs fromUtf8Hook libsignalSessionLib
   lsFromUtf8Sym lsMemrchrSym memrchrHook stdinCapBytes strlenHook)
open CryptoVerification.SignalSession.Cli (cliInputs loadState_fs_trace)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliExternsPlaced_strlen cliIo cliMainStk cliResStack cliWrOk
   inputOf lsHandleErrorSymMain mProgPlaced mainFrameSize parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig cliTokenPatchPlaced)
open LibsignalBinary.Heap (AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal (cliRealNinetyPctOneGiB)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits
   mainEntryBudgetFitsCapOf_of_fitsEnv
   mainEntryBudgetFitsCap_cliBudgetLimits_of_kitEnvFits
   mainEntryBudgetFitsCap_of_fitsEnv
   mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB
   mainEntryBudgetFitsCap_of_realMainEnvFits_90pct
   mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (BoundedReadFileEnv CliMainBoundedSetupEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
  (CliRunsToExtOnInputsAt cliProgExtPlacedSigAt cliRunExtOnInputsSigAt
   cliRunsToExtOnInputsAt_of_eq_some)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (CliElfExtB2NeedLocksAssumptions CliPqxdhExtElfCorrectStrictPlacedAt
   CliPqxdhExtOnInputsElfCorrectStrictPlacedAt MainOkCliExtOverB2NeedLocksPlacedAt
   MainOkCliExtPqB2NeedLocksPlacedAt cliPqxdhElfCorrectPlaced_of_extProgEq
   cliPqxdhElfCorrectStrictPlaced_of_extProgEq
   cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksAssumptions)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_cliExternsPlaced
   externPreservesNoAllocFailed_none externPreserves_map_abortOnPanic steps_preserves_no_allocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (mainOkCliExtOverB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCap
   mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
   mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
   mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
   mainOkCliExtPqB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCap
   mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
   mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
   mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (cliRunSemD2c_placed pqScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
  (CliPqxdhAllocNeverFailsPlaced CliPqxdhElfCorrectStrictPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## `UnreachedPqxdhPrimitives` Witness and Placed OOM Reachability -/

/-- Default witness for `UnreachedPqxdhPrimitives` (used when extracting execution outcomes that do
not depend on model-only unreached primitives). -/
def defaultUnreachedPqxdhPrimitives : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

/-- Execution of `cliProgExtPlacedSigAt mpl ext idx W` from `elf.loadState (inputsOf i)` with
`cliTokenPatchPlaced mpl` reaches a state with `sf.status = .OutOfMemory`. -/
def CliReachesOOMExtOnInputsAt (mpl : MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (inputsOf : Inputs → ProcessInputs) (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 sf : State,
    elf.loadState (inputsOf i) = .ok s0 ∧
    Steps (cliProgExtPlacedSigAt mpl ext idx W) (cliTokenPatchPlaced mpl s0) sf ∧
    sf.status = .OutOfMemory

/-- Specialization of `CliReachesOOMExtOnInputsAt` to `cliProcessInputs`. -/
abbrev CliReachesOOMExtPlacedAt (mpl : MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  CliReachesOOMExtOnInputsAt mpl ext idx cliProcessInputs elf W i

theorem cliProgPlacedSig_eq_cliProgExtPlacedSigAt_f3
    (mpl mmpl : MultiPlacement) (W : CliHooks) :
    cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl (cliExternsPlaced mmpl) 617 W :=
  rfl

theorem cliReachesOOMPlaced_eq_extPlacedAt_f3
    (mpl mmpl : MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs) :
    CliReachesOOMPlaced mpl mmpl elf W i =
      CliReachesOOMExtPlacedAt mpl (cliExternsPlaced mmpl) 617 elf W i :=
  rfl

/-- Any input with a `CliRunsToExtOnInputsAt` outcome (`oom := fun _ => False` inside
`ProcessRunsTo`) never reaches `.OutOfMemory`. -/
theorem not_cliReachesOOMExtOnInputsAt_of_cliRunsToExt
    {mpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {idx : Nat} {inputsOf : Inputs → ProcessInputs}
    {elf : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (hRuns : CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i o) :
    ¬ CliReachesOOMExtOnInputsAt mpl ext idx inputsOf elf W i := by
  rintro ⟨s0', sf, hLoad₂, hSteps, hStat⟩
  rcases hRuns with ⟨s0, hLoad₁, _, hSafe⟩
  rw [hLoad₁] at hLoad₂
  injection hLoad₂ with hs0
  subst hs0
  rcases hSafe sf hSteps with ⟨out, hTerm, _⟩ | ⟨_, hFalse⟩ | ⟨hRun, _⟩
  · rcases hTerm with ⟨_, hEx, _⟩ | ⟨_, hSig, _⟩
    · rw [hStat] at hEx; cases hEx
    · rw [hStat] at hSig; cases hSig
  · exact hFalse
  · rw [hStat] at hRun; cases hRun

/-- Every `CliPqxdhInputs WP i` input across all 5 arms (`init`, `send`, `recv` whisper, `recv`
prekey with `session = none`, matching session, or non-matching session, and `recv` bad tag) has a
defined `some o` outcome whenever `CliSpecPqxdh` and `CliSpecPqxdhNoMatch` hold. -/
theorem exists_outcome_of_cliSpecPqxdh_and_noMatch
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    (hPq : CliSpecPqxdh run X WP)
    (hNoMatch : CliSpecPqxdhNoMatch run X WP)
    {i : Inputs} (hi : CliPqxdhInputs WP i) :
    ∃ o : Outcome, run i = some o := by
  rcases hi with ⟨st, hst, h1 | h2 | h3 | h4 | h5⟩
  · obtain ⟨c1, _, _, _, _⟩ := hPq st hst
    rcases h1 with ⟨hsess, b, t, rfl⟩
    exact ⟨_, c1 b t hsess⟩
  · obtain ⟨_, c2, _, _, _⟩ := hPq st hst
    rcases h2 with ⟨m, r, hm, rfl⟩
    have hc := c2 m r hm
    split at hc
    · exact ⟨_, hc⟩
    · split at hc <;> exact ⟨_, hc⟩
  · obtain ⟨_, _, c3, _, _⟩ := hPq st hst
    rcases h3 with ⟨c, rc, hc, rfl⟩
    have h := c3 c rc hc
    split at h <;> exact ⟨_, h⟩
  · obtain ⟨_, _, _, c4, _⟩ := hPq st hst
    rcases h4 with ⟨m, rc, hm, rfl⟩
    cases hsess : st.session with
    | none =>
      have hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m := by
        intro _ _ h; rw [hsess] at h; cases h
      have h := c4 m rc hm hmatch
      split at h <;> exact ⟨_, h⟩
    | some xg =>
      rcases xg with ⟨x, g⟩
      by_cases hmatch : PqSessionMatches x g m
      · have hmatch' : ∀ x' g', st.session = some (x', g') → PqSessionMatches x' g' m := by
          intro _ _ h; rw [hsess] at h; injection h with hEq; cases hEq; exact hmatch
        have h := c4 m rc hm hmatch'
        split at h <;> exact ⟨_, h⟩
      · have hnm := hNoMatch st hst x g hsess m rc hm hmatch
        split at hnm
        · exact ⟨_, hnm⟩
        · obtain ⟨o, ho, _⟩ := hnm
          exact ⟨o, ho⟩
  · obtain ⟨_, _, _, _, c5⟩ := hPq st hst
    rcases h5 with ⟨c, rc, hc, h2, h3, rfl⟩
    have h := c5 c rc hc h2 h3
    split at h <;> exact ⟨_, h⟩

/-- Strict placed ELF correctness on `inputsOf` implies `¬ CliReachesOOMExtOnInputsAt` for every
`W : CliHooks` and every `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem not_cliReachesOOMExtOnInputsAt_of_strict
    {mpl mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {elf : ElfImage}
    (hStrict : CliPqxdhExtOnInputsElfCorrectStrictPlacedAt mpl mmpl ext mainIdx inputsOf elf)
    (W : CliHooks) {i : Inputs} (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMExtOnInputsAt mpl ext mainIdx inputsOf elf W i := by
  obtain ⟨hPq, hNoMatch⟩ := hStrict.2 W defaultUnreachedPqxdhPrimitives
  obtain ⟨o, ho⟩ := exists_outcome_of_cliSpecPqxdh_and_noMatch hPq hNoMatch hi
  exact not_cliReachesOOMExtOnInputsAt_of_cliRunsToExt (cliRunsToExtOnInputsAt_of_eq_some ho)

/-- Strict placed ELF correctness on `cliProcessInputs` implies `¬ CliReachesOOMExtPlacedAt` for
every `W : CliHooks` and every `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem not_cliReachesOOMExtPlacedAt_of_strict
    {mpl mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage}
    (hStrict : CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext mainIdx elf)
    (W : CliHooks) {i : Inputs} (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMExtPlacedAt mpl ext mainIdx elf W i :=
  not_cliReachesOOMExtOnInputsAt_of_strict hStrict W hi

/-- Generic-`ext` `allocFailedEvent ∉ s.trace` preservation from `loadState` + `cliTokenPatchPlaced`. -/
theorem allocNeverFailsExtPlacedAt_of_externPreserves
    {mpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {idx : Nat} {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W)) :
    ∀ (i : Inputs) (s0 s : State),
      elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgExtPlacedSigAt mpl ext idx W) (cliTokenPatchPlaced mpl s0) s →
      allocFailedEvent ∉ s.trace := by
  intro i s0 s hload hsteps
  have hloadCli : elf.loadState (cliInputs i) = .ok s0 := by
    rwa [cliInputs_eq_cliProcessInputs]
  have hs0 : allocFailedEvent ∉ (cliTokenPatchPlaced mpl s0).trace := by
    unfold cliTokenPatchPlaced
    change allocFailedEvent ∉ s0.trace
    rw [(loadState_fs_trace hloadCli).2]
    simp
  exact steps_preserves_no_allocFailed rfl
    (externPreserves_map_abortOnPanic hext)
    externPreservesNoAllocFailed_none hsteps hs0

/-- Discharges `CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W` from `ExternPreservesNoAllocFailed (ext W)`
once `cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext idx W`. -/
theorem cliPqxdhAllocNeverFailsPlaced_of_extProgEq
    {mpl mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {idx : Nat} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext idx W)
    (hext : ExternPreservesNoAllocFailed (ext W)) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W := by
  intro i _ s0 s hload hsteps
  rw [hprog] at hsteps
  exact allocNeverFailsExtPlacedAt_of_externPreserves hext i s0 s hload hsteps

/-- `allocFailedEvent`-freedom on `cliExternsPlaced mmpl`. -/
theorem cliPqxdhAllocNeverFailsPlaced_f3
    (mpl mmpl : MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W :=
  cliPqxdhAllocNeverFailsPlaced_of_extProgEq rfl (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)

/-! ## Parametric Callee-Envelope `MainOk` Assemblers -/

/-- Chains a parametric whole-`main` `FitsEnv` bound and `runSpecTightPlaced` into
`MainOkCliExtPqB2NeedLocksPlacedAt` via `MainEntryBudgetFitsCapReal.mainEntryBudgetFitsCap_of_fitsEnv`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
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
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
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
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err RunEnv hlibc hFs hio hioBounded
    hstrlen hutf8 hmemrchr hpan hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_of_fitsEnv hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- Chains a parametric whole-`main` `FitsEnv` bound and `runSpecTightPlaced` into
`MainOkCliExtOverB2NeedLocksPlacedAt`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
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
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
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
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err RunEnv hlibc hFs hio hioBounded
    hstrlen hutf8 hmemrchr hpan hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_of_fitsEnv hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliGhostExterns` specialization of `mainOkCliExtPqB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTight
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
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
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
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
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hio hioBounded hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_of_fitsEnv hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliGhostExterns` specialization of `mainOkCliExtOverB2NeedLocksPlacedAt_of_kitEnvFits_and_runTight`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTight
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
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
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
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
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hio hioBounded hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_of_fitsEnv hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliBudgetLimits` specialization of
`mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTight` with setup early-exit
`FitsEnv` discharged. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTight
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
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
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hio hioBounded hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_cliBudgetLimits_of_kitEnvFits
        (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliBudgetLimits` specialization of
`mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTight`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTight
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
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
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hio hioBounded hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCap_cliBudgetLimits_of_kitEnvFits
        (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `ReadEnv`-parametric `MainOkCliExtPqB2NeedLocksPlacedAt` assembler for `MainIoOfPlaced`
and `cliGhostExterns`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTightOf
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
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
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
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
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hioOf hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCapOf_of_fitsEnv hReadSub hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `ReadEnv`-parametric `MainOkCliExtOverB2NeedLocksPlacedAt` assembler for `MainIoOfPlaced`
and `cliGhostExterns`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTightOf
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
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
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
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
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hioOf hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCapOf_of_fitsEnv hReadSub hEarly (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliBudgetLimits` specialization of
`mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTightOf`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hioOf hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits
        hReadSub (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-- `cliBudgetLimits` specialization of
`mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_kitEnvFits_and_runTightOf`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (E : UnreachedPqxdhPrimitives → CliHooks → RunCall → CliRunCalleeEnvs)
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hMain : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (i : Inputs),
        CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
          (RealCliMainBinaryEnvOf (E X W) i))
    (hRunSub : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall),
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        runRel (cliRunSemD2c_placed X W) g.i g.a →
        ∀ evs : List AllocEvent, RunEnv X W γ tp g evs →
          CliRunBinaryEnv cliIo.rd (E X W g) sessionCapBytes g evs)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf
    hblk hext_nodup hCI ghOf RunEnv hlibc hG hioOf hstk
    (fun h547 X W γ tp =>
      mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits
        hReadSub (hMain h547 X W) (hRunSub h547 X W γ tp))
    hrun

/-! ## `mkExistentialRealCalleeEnvs` Whole-Program `FitsEnv` Composition -/

/-- Concrete binary-exact `RunCall → List AllocEvent → Prop` envelope at `(mpl, img, X, W)`. -/
noncomputable def realCliRunBinaryEnvOf
    {mpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (rc : RunCall) : List AllocEvent → Prop :=
  CliRunBinaryEnv cliIo.rd
    (@mkExistentialRealCalleeEnvs (libsignalPlacementOf mpl hblk hext_nodup)
      img (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩ rc)
    sessionCapBytes rc

/-- Concrete `CalleeEnvs` family at `(mpl, img, X, W)`. -/
noncomputable def realCliCalleeEnvsOf
    {mpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    RunCall → CliRunCalleeEnvs :=
  @mkExistentialRealCalleeEnvs (libsignalPlacementOf mpl hblk hext_nodup)
    img (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩

/-- `MainOkCliExtPqB2NeedLocksPlacedAt` from whole-`main` `FitsEnv` at `cliRealNinetyPctOneGiB ≤ lim.physCap`. -/
theorem mainOkCliExtPq_of_realMainEnvFits_90pct
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Image)
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
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_90pct
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap90 img X W)
    hrun

/-- `MainOkCliExtOverB2NeedLocksPlacedAt` from whole-`main` `FitsEnv` at `cliRealNinetyPctOneGiB ≤ lim.physCap`. -/
theorem mainOkCliExtOver_of_realMainEnvFits_90pct
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Image)
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
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_90pct
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap90 img X W)
    hrun

/-- `MainOkCliExtPqB2NeedLocksPlacedAt` from whole-`main` `FitsEnv` at `cliOneGiB ≤ lim.physCap`. -/
theorem mainOkCliExtPq_of_realMainEnvFits_1GiB
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image)
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
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap1G img X W)
    hrun

/-- `MainOkCliExtOverB2NeedLocksPlacedAt` from whole-`main` `FitsEnv` at `cliOneGiB ≤ lim.physCap`. -/
theorem mainOkCliExtOver_of_realMainEnvFits_1GiB
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image)
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
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB
        (libsignalPlacementOf mpl hblk hext_nodup) lim henf hsb hsc hcap1G img X W)
    hrun

/-- `MainOkCliExtPqB2NeedLocksPlacedAt` at `cliBudgetLimits` (`1 GiB`) and `mkExistentialRealCalleeEnvs`. -/
theorem mainOkCliExtPq_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `MainOkCliExtOverB2NeedLocksPlacedAt` at `cliBudgetLimits` (`1 GiB`) and `mkExistentialRealCalleeEnvs`. -/
theorem mainOkCliExtOver_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI utf8Err (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `cliGhostExterns` specialization of `mainOkCliExtPq_of_realMainEnvFits`. -/
theorem mainOkCliExtPq_cliGhostExterns_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
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
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI ghOf (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hG hio hioBounded hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `cliGhostExterns` specialization of `mainOkCliExtOver_of_realMainEnvFits`. -/
theorem mainOkCliExtOver_cliGhostExterns_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
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
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI ghOf (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hG hio hioBounded hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `cliExternsPlaced mmpl` specialization of `mainOkCliExtPq_of_realMainEnvFits`. -/
theorem mainOkCliExtPq_f3_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtPqB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-- `cliExternsPlaced mmpl` specialization of `mainOkCliExtOver_of_realMainEnvFits`. -/
theorem mainOkCliExtOver_f3_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk cliBudgetLimits :=
  mainOkCliExtOverB2NeedLocksPlacedAt_cliExterns_of_runTight_and_budgetFitsCap
    hblk hext_nodup hCI (fun X W _ _ => realCliRunBinaryEnvOf hblk hext_nodup img X W)
    hlibc hFs hio hioBounded hstk
    (fun _ X W _ _ =>
      @mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits
        (libsignalPlacementOf mpl hblk hext_nodup) img X W)
    hrun

/-! ## Strict Placed ELF Correctness and Never-OOM Corollaries -/

/-- Strict placed ELF correctness (`CliPqxdhExtElfCorrectStrictPlacedAt`) from whole-`main` `FitsEnv`. -/
theorem cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext 617 elf :=
  cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksAssumptions hext H
    (mainOkCliExtPq_of_realMainEnvFits hblk hext_nodup hCI utf8Err img hlibc hFs hio hioBounded
      hstrlen hutf8 hmemrchr hpan hstk hrun)
    (mainOkCliExtOver_of_realMainEnvFits hblk hext_nodup hCI utf8Err img hlibc hFs hio hioBounded
      hstrlen hutf8 hmemrchr hpan hstk hrun)

/-- Every `CliPqxdhInputs ⟨W.C, W.Q⟩ i` input across all PQXDH/SPQR CLI subcommands satisfies
`¬ CliReachesOOMExtPlacedAt`. -/
theorem not_cliReachesOOMExtPlacedAt_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) {i : Inputs} (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMExtPlacedAt mpl ext 617 elf W i :=
  not_cliReachesOOMExtPlacedAt_of_strict
    (cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits hblk hext_nodup hCI utf8Err img
      hext H hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk hrun)
    W hi

/-- `cliExternsPlaced mmpl` specialization: `¬ CliReachesOOMPlaced mpl mmpl elf W i` for every
`CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem not_cliReachesOOMPlaced_f3_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack))
    (W : CliHooks) {i : Inputs} (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  rw [cliReachesOOMPlaced_eq_extPlacedAt_f3]
  exact not_cliReachesOOMExtPlacedAt_of_strict
    (cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksAssumptions
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H
      (mainOkCliExtPq_f3_of_realMainEnvFits hblk hext_nodup hCI img hlibc hFs hio hioBounded hstk hrun)
      (mainOkCliExtOver_f3_of_realMainEnvFits hblk hext_nodup hCI img hlibc hFs hio hioBounded hstk hrun))
    W hi

/-- `CliPqxdhElfCorrectStrictPlaced` when
`cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext 617 W`. -/
theorem cliPqxdhElfCorrectStrictPlaced_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hprog : ∀ W : CliHooks, cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext 617 W)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectStrictPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced_of_extProgEq hprog
    (cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits hblk hext_nodup hCI utf8Err img
      hext H hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk hrun)

/-- `cliExternsPlaced mmpl` specialization of `cliPqxdhElfCorrectStrictPlaced_of_realMainEnvFits`. -/
theorem cliPqxdhElfCorrectStrictPlaced_f3_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectStrictPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced_of_extProgEq (fun _ => rfl)
    (cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksAssumptions
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H
      (mainOkCliExtPq_f3_of_realMainEnvFits hblk hext_nodup hCI img hlibc hFs hio hioBounded hstk hrun)
      (mainOkCliExtOver_f3_of_realMainEnvFits hblk hext_nodup hCI img hlibc hFs hio hioBounded hstk hrun))

/-- `CliPqxdhElfCorrectPlaced` when
`cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext 617 W`. -/
theorem cliPqxdhElfCorrectPlaced_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    (utf8Err : CliHooks → List (BitVec 8) → BitVec 64 × BitVec 16)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (hprog : ∀ W : CliHooks, cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext 617 W)
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl ext 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hutf8 : ∀ W : CliHooks, ext W lsFromUtf8Sym = some (fromUtf8Hook (utf8Err W)))
    (hmemrchr : ∀ W : CliHooks, ext W lsMemrchrSym = some memrchrHook)
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Arm64.Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_extProgEq hprog
    (cliPqxdhExtElfCorrectStrictPlacedAt_of_realMainEnvFits hblk hext_nodup hCI utf8Err img
      hext H hlibc hFs hio hioBounded hstrlen hutf8 hmemrchr hpan hstk hrun)

/-- `cliExternsPlaced mmpl` specialization of `cliPqxdhElfCorrectPlaced_of_realMainEnvFits`. -/
theorem cliPqxdhElfCorrectPlaced_f3_of_realMainEnvFits
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {exitStk : Nat} {libcAddr : BitVec 64} {hookStack : Nat} {elf : ElfImage}
    (img : Image)
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
      exitStk libcAddr cliMainStk CodeOk cliBudgetLimits elf)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits (cliExternsPlaced mmpl W)
        cliIo hookStack ReadStdinBoundedEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
          (cliExternsPlaced mmpl W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) cliBudgetLimits
            (realCliRunBinaryEnvOf hblk hext_nodup img X W) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_extProgEq (fun _ => rfl)
    (cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksAssumptions
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H
      (mainOkCliExtPq_f3_of_realMainEnvFits hblk hext_nodup hCI img hlibc hFs hio hioBounded hstk hrun)
      (mainOkCliExtOver_f3_of_realMainEnvFits hblk hext_nodup hCI img hlibc hFs hio hioBounded hstk hrun))

end LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
