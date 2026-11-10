/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgePq
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Strict Placed PQXDH ELF and Binary Correctness

Whole-ELF and whole-binary strict (`0`-excused-abort) PQXDH correctness theorems over
split placements `(mpl, mmpl)`, supporting both `MuslHarnessFinePerInput` and the read-only-`argv`
`NeedLocks` harness `MuslHarnessFineNeedLocksPerInput`, across the 40-row and 41-row
shared-allocator hook tables.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey wireWhisper)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhElfCorrectPlaced CliRun CliSpecPqxdh
   CliSpecPqxdhNoMatch Inputs Outcome OutcomeMatchesModelExceptPath PqParty PqSessionMatches
   PqxdhPartyInSpecDomain cliInputsOk_pqInitInputs cliInputsOk_pqRecvInputs cliInputsOk_pqSendInputs
   cliProcessInputs coinsReadable_pqInitInputs coinsReadable_pqRecvInputs coinsReadable_pqSendInputs
   filesOf inputsLoadable_pqInitInputs inputsLoadable_pqRecvInputs inputsLoadable_pqSendInputs
   isSendOverCap_pqSendInputs isStdinOverCap_pqRecvInputs isStdinOverCap_pqSendInputs
   libsignalSessionLib maxPlaintextBytes not_isSendOverCap_of_stdin_le
   not_isSendOverCap_pqInitInputs not_isSendOverCap_pqRecvInputs not_isStdinOverCap_of_stdin_le
   not_isStdinOverCap_pqInitInputs observe outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited
   partyAddress pqInitInputs pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel
   pqSendInputs pqSendModel pqxdhExpectedOutcome sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk ElfStaticOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainGhost MainPost MainResult RunAnswer cliInputs cliStaticsPlaced fsView_congr
   fsView_writeAll_initFsState loadState_fs_trace signExtend_ofNat_small)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.InitStack (stackBase)
open CryptoVerification.SignalSession.MuslElf (CliElfMusl)
open CryptoVerification.SignalSession.MuslExit (MuslExitFetch)
open CryptoVerification.SignalSession.Placed
  (CliElfCodeMatchesPlaced CliRunsToPlaced cliProgPlacedSig cliRunPlacedSig cliTokenPatchPlaced)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout FineBudget StartupVmPreserved fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
  (CliElfTokenCellsPlacedAt CliRunsToExtOnInputsAt CliStackShape MallocngRoTablesInMem
   MuslHarnessFinePerInput b2FineHookPool_of_needLocks cliElfMallocngLayout_iff_patchElfTokensPlacedAt
   cliM2ExternsWithClonePlaced cliM2ProgWithClonePlacedSig cliM2WithClone_allocNeverFailsPlaced
   cliProgExtPlacedAt cliProgExtPlacedSigAt cliRunExtOnInputsSigAt cliRunExtOnInputsSigAt_eq_some
   cliRunExtPlacedSigAt cliRunExtPlacedSigAt_of_strict_main_call_obs
   cliRunExtPlacedSigAt_of_strict_main_sendOverCap cliRunExtPlacedSigAt_of_strict_main_stdinOverCap
   cliRunsToExtOnInputsAt_of_outcomeOf_observed cliRunsToExtOnInputsAt_of_outcomeOf_usage
   cliRunsToExtOnInputsAt_unique elfStaticOk_patchElfTokensPlacedAt
   externPreservesNoAllocFailed_cliM2ExternsWithClonePlaced loadState_patchElfTokensPlacedAt
   mallocngLib_dataInit_eq_ro_rw mallocngRwBssAt
   muslHarnessFinePerInput_of_muslStartFine_blockProgram patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
  (ExternPreservesNoAllocFailed cliM2ExternsPlaced cliM2ProgPlacedSig cliM2_allocNeverFailsPlaced
   externPreservesNoAllocFailed_cliM2ExternsPlaced externPreservesNoAllocFailed_none
   steps_preserves_no_allocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MuslStartFineResources
  (MuslStartFetchAt mainPcOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
  (CliPqxdhAllocNeverFailsPlaced CliPqxdhElfCorrectStrictPlaced cliPqxdhElfCorrectPlaced_of_strict)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (mainSpecTightPlacedAt)
open VerifiedLibraries.Mallocng
  (MallocngAuxvAt MallocngRoTablesAt mallocngAddrsOfPlacement)

/-! ## Read-only `argv` + `NeedLocks` per-input harness and strict composer -/

/-- Read-only NUL-terminated byte slice `s` at `p`. -/
def cStrAtRO (p : BitVec 64) (s : List (BitVec 8)) : SepProp :=
  p ↦ᵣ (s ++ [0#8])

/-- Read-only C `argv` pointer table at `a`. -/
def argvAtRO : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ᵣ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ᵣ p) ∗ cStrAtRO p s ∗ argvAtRO (a + 8#64) ss

def B2MainEntryFacts (inputsOf : Inputs → ProcessInputs) (i : Inputs) (s : State) : Prop :=
  (s.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    s.fs = initFsState (inputsOf i) ∧ s.trace = []

def b2MainFrameFine {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  argvAtRO (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool lim st s ∗ Statics

def b2MainEntryPreFine (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (stk : Nat)
    (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  ⌜CodeOk s.mem ∧ stk ≤ s.sp.toNat⌝ ∗ b2MainFrameFine A lim st stk Statics i s

/-- Tight `main` specification returning `((libcAddr + 3#64) ↦₈ 0#8)` (`__libc.need_locks = 0`)
and `stackAt s0.sp stk` with `onExit = onOom = ⌜False⌝`. -/
def b2MainSpecTightNeedLocksFineAt (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧
      B2MainEntryFacts inputsOf g.i s ∧ stk ≤ s.sp.toNat⌝ ∗
      b2MainFrameFine A lim st stk Statics g.i s
  post := fun g s0 sf =>
    ⌜MainPost g.r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem exit_frame_needLocks_n {m : Memory} {nl sp : BitVec 64} {n stk : Nat} {Fr : SepProp}
    (hstk : n ≤ stk) (_hstk' : stk ≤ 2 ^ 64)
    (h : m ⊨ ((nl ↦₈ 0#8) ∗ stackAt sp stk ∗ anyHeap) ∗ Fr) :
    m ⊨ (nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗ anyHeap := by
  have hsplit := stackAt_split_bottom sp n (stk - n) (by omega)
  rw [show n + (stk - n) = stk by omega] at hsplit
  rw [hsplit] at h
  refine Satisfies.mono ?_ h
  have e : (((nl ↦₈ 0#8) ∗ (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ stackAt sp n) ∗
        anyHeap) ∗ Fr) =
      (nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗
        (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ anyHeap) := by
    sep_ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

/-- Per-input `∃ (γ : GhostName)` whole-process harness over read-only `argvAtRO` and
`__libc.need_locks = 0`. -/
def MuslHarnessFineNeedLocksPerInput (exitStk : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp) : Prop :=
  ElfStaticOk elf →
    ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
      ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
        let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
        elf.loadState (inputsOf i) = .ok s0 ∧
        Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
        sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
        (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
        (sm.mem ⊨ b2MainEntryPreFine CodeOk A lim st stk Statics i sm ∗ Fr) ∧
        ∀ sr : State, Steps P sm sr → Returned sm sr →
          (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
          ∃ sx : State, Steps P sr sx ∧
            sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
            sx.fs = sr.fs ∧ sx.trace = sr.trace

theorem muslHarnessFineNeedLocksPerInput_of_startup
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    (hsh : ∀ i : Inputs, CliStackShape (inputsOf i))
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hStartup : ElfStaticOk elf →
      ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
        ∃ (s0 sm : State) (Fr : SepProp) (auxvPtr : BitVec 64) (errnoVal : BitVec 32),
          elf.loadState (inputsOf i) = .ok s0 ∧
          Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
          (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
          StartupVmPreserved s0 sm ∧
          0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
          CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem ∧
          stk ≤ sm.sp.toNat ∧
          (sm.mem ⊨
            VerifiedLibraries.mallocngLib.dataInit mmpl ∗
              ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗
              ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
              ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
              MallocngAuxvAt auxvPtr ∗
              (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
                stackAt sm.sp stk ∗ Statics ∗ Fr)) ∧
          ∀ sr : State, Steps P sm sr → Returned sm sr →
            (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
            ∃ sx : State, Steps P sr sx ∧
              sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
              sx.fs = sr.fs ∧ sx.trace = sr.trace) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim fineCostModel.init stk CodeOk Statics := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, auxvPtr, errnoVal, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0,
    hVm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ := hStartup hE i hi
  obtain ⟨γ, hPool⟩ :=
    b2FineHookPool_of_needLocks hCL (hsh i) hLayout hload hVm htpLo htpHi hlibc hmem
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨ b2MainEntryPreFine CodeOk A lim fineCostModel.init stk Statics i sm ∗ Fr := by
    simp only [b2MainEntryPreFine, b2MainFrameFine, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hsp⟩, ?_⟩
    let Argv := argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString)
    let Stk := stackAt sm.sp stk
    have heq :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fr)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fr) := by sep_ac_rfl
    exact heq ▸ hPool
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩

/-- Startup return-address invariant `lr = L.libcStartMainStage2Addr + 56#64` at `main` entry (`blr x21` at `stage2+0x34` in `ProofLib/StdStartup/StdDetect.lean:69-72` `libcStartMainStage2EntryInstrs` returns to `stage2+0x38` = `bl exit` in `ProofLib/StdStartup/CleanupAndExit.lean:391` `muslExitChunks`). -/
def StdMainEntryLr (L : ProofLib.StdStartup.StdBinaryLayout) (sm : State) : Prop :=
  sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64

/-- Guarded counterpart of `MuslHarnessFineNeedLocksPerInput` carrying an entry-state predicate
`EntryGuard sm`. -/
def MuslHarnessFineNeedLocksGuardedPerInput (exitStk : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp)
    (EntryGuard : State → Prop) : Prop :=
  ElfStaticOk elf →
    ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
      ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
        let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
        elf.loadState (inputsOf i) = .ok s0 ∧
        Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
        sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
        EntryGuard sm ∧
        (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
        (sm.mem ⊨ b2MainEntryPreFine CodeOk A lim st stk Statics i sm ∗ Fr) ∧
        ∀ sr : State, Steps P sm sr → Returned sm sr →
          (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
          ∃ sx : State, Steps P sr sx ∧
            sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
            sx.fs = sr.fs ∧ sx.trace = sr.trace

theorem MuslHarnessFineNeedLocksGuardedPerInput.mono_guard
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    {EntryGuard EntryGuard' : State → Prop}
    (hImp : ∀ sm : State, EntryGuard sm → EntryGuard' sm)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard' := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0, hEntry, hexit⟩ :=
    hH hE i hi
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hImp sm hG, hx0, hEntry, hexit⟩

theorem MuslHarnessFineNeedLocksGuardedPerInput.toUnguarded
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    {EntryGuard : State → Prop}
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, _hG, hx0, hEntry, hexit⟩ :=
    hH hE i hi
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩

theorem MuslHarnessFineNeedLocksPerInput.toGuardedTrue
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics (fun _ => True) := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩ :=
    hH hE i hi
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, trivial, hx0, hEntry, hexit⟩

theorem muslHarnessFineNeedLocksGuardedPerInput_true_iff
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics (fun _ => True) ↔
      MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics :=
  ⟨MuslHarnessFineNeedLocksGuardedPerInput.toUnguarded,
   MuslHarnessFineNeedLocksPerInput.toGuardedTrue⟩

theorem muslHarnessFineNeedLocksPerInput_eq_guarded_true
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics =
      MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics (fun _ => True) :=
  propext (muslHarnessFineNeedLocksGuardedPerInput_true_iff exitStk libcAddr elf P mainPc
    inputsOf mmpl lim st stk CodeOk Statics).symm

theorem muslHarnessFineNeedLocksGuardedPerInput_of_startup
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp} {EntryGuard : State → Prop}
    (hsh : ∀ i : Inputs, CliStackShape (inputsOf i))
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hStartup : ElfStaticOk elf →
      ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
        ∃ (s0 sm : State) (Fr : SepProp) (auxvPtr : BitVec 64) (errnoVal : BitVec 32),
          elf.loadState (inputsOf i) = .ok s0 ∧
          Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
          EntryGuard sm ∧
          (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
          StartupVmPreserved s0 sm ∧
          0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
          CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem ∧
          stk ≤ sm.sp.toNat ∧
          (sm.mem ⊨
            VerifiedLibraries.mallocngLib.dataInit mmpl ∗
              ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗
              ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
              ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
              MallocngAuxvAt auxvPtr ∗
              (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
                stackAt sm.sp stk ∗ Statics ∗ Fr)) ∧
          ∀ sr : State, Steps P sm sr → Returned sm sr →
            (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
            ∃ sx : State, Steps P sr sx ∧
              sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
              sx.fs = sr.fs ∧ sx.trace = sr.trace) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim fineCostModel.init stk CodeOk Statics EntryGuard := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, auxvPtr, errnoVal, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0,
    hVm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ := hStartup hE i hi
  obtain ⟨γ, hPool⟩ :=
    b2FineHookPool_of_needLocks hCL (hsh i) hLayout hload hVm htpLo htpHi hlibc hmem
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨ b2MainEntryPreFine CodeOk A lim fineCostModel.init stk Statics i sm ∗ Fr := by
    simp only [b2MainEntryPreFine, b2MainFrameFine, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hsp⟩, ?_⟩
    let Argv := argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString)
    let Stk := stackAt sm.sp stk
    have heq :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fr)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fr) := by sep_ac_rfl
    exact heq ▸ hPool
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0, hEntry, hexit⟩

theorem outcome_of_main_strict_b2_needLocks_guarded_perInput_at
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {EntryGuard : State → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        { (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf) with
          pre := fun x s => ⌜EntryGuard s⌝ ∗
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
              lim st stk Statics Run inputsOf).pre x s })
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (inputsOf i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hG, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  let baseSpec := b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run inputsOf
  have hpre : sm.mem ⊨
      ({ baseSpec with pre := fun x s => ⌜EntryGuard s⌝ ∗ baseSpec.pre x s }).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [baseSpec, b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG, ⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n hstk hstk' hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, hfs_eq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed hsvc hext hovr hsteps01 hs0)
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Strict whole-process outcome theorem from `MuslHarnessFineNeedLocksPerInput` and
`b2MainSpecTightNeedLocksFineAt`. -/
theorem outcome_of_main_strict_b2_needLocks_perInput_at
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (inputsOf i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run inputsOf).pre
        ⟨i, r⟩ sm ∗ Fr := by
    simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n hstk hstk' hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, hfs_eq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed hsvc hext hovr hsteps01 hs0)
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 2 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.stdinOverCap hstin)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 1 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.sendOverCap hover hnstin hcoins)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  rw [hobs] at hruns
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop} {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    ∃ o, cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq hCode hH
      hmain hstk hstk' hi hl hrun hnover hnstin rfl hcoins hcommit, hp⟩

/-! ## Explicit-`mpl` writable statics and `DataDisjoint` lemmas -/

def coinsStaticsPlacedAt (mpl : Obj.MultiPlacement) : SepProp :=
  (∃∗ v : BitVec 64, mpl.ρ CryptoVerification.SignalSession.Coins.coinsNextSym ↦₆₄ v) ∗
  (∃∗ v : BitVec 64, mpl.ρ CryptoVerification.SignalSession.Coins.coinsLeftSym ↦₆₄ v)

def tokenInitPlacedAtMpl (mpl : Obj.MultiPlacement) : SepProp :=
  (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName ↦₈ 0#8) ∗
  ((mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) ↦₃₂ 0#32)

def lsLogOffAt (mpl : Obj.MultiPlacement) : SepProp :=
  mpl.ρ CryptoVerification.lsLogFilterSym ↦₆₄ 0#64

/-- Explicit-`mpl` writable statics bundle
(`coinsStaticsPlacedAt ∗ tokenInitPlacedAtMpl ∗ lsLogOffAt`). -/
def cliStaticsPlacedAt (mpl : Obj.MultiPlacement) : SepProp :=
  coinsStaticsPlacedAt mpl ∗ tokenInitPlacedAtMpl mpl ∗ lsLogOffAt mpl

theorem cliStaticsPlacedAt_eq_cliStaticsPlaced [LibsignalPlacement] :
    cliStaticsPlacedAt lsmpl = cliStaticsPlaced :=
  rfl

theorem satisfies_mallocngDataInit_of_dataDisjoint
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {inputs : ProcessInputs} {s0 : State}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin : VerifiedLibraries.mallocngLib.InElf elf mmpl)
    (hdisj : VerifiedLibraries.mallocngLib.DataDisjoint mmpl)
    (hload : elf.loadState inputs = .ok s0) :
    s0.mem ⊨ VerifiedLibraries.mallocngLib.dataInit mmpl :=
  VerifiedLibraries.mallocngLib.satisfies_dataInit_of_inElf hpl hin hload (by decide) hdisj

theorem satisfies_mallocngRoAndRwBss_of_dataDisjoint
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {inputs : ProcessInputs} {s0 : State}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin : VerifiedLibraries.mallocngLib.InElf elf mmpl)
    (hdisj : VerifiedLibraries.mallocngLib.DataDisjoint mmpl)
    (hload : elf.loadState inputs = .ok s0) :
    s0.mem ⊨ MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ mallocngRwBssAt mmpl := by
  have h := satisfies_mallocngDataInit_of_dataDisjoint hpl hin hdisj hload
  rwa [mallocngLib_dataInit_eq_ro_rw mmpl] at h

/-! ## Uniform `MainOkCliExt*` specifications -/

/-- 5-clause PQXDH tight `main` specification over explicit placements `(mpl, mmpl)` and extern
family `ext`. -/
def MainOkCliExtPqTightCodePlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (CodeOk : Memory → Prop)
    (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (mainSpecTightPlacedAt CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run)) ∧
      ∀ p : PqParty, PqxdhPartyInSpecDomain WP p →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
          p.session = none →
          ∃ a, Run (pqInitInputs WP p b t) a ∧
            observe (pqInitInputs WP p b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP p b t) (pqInitModel X WP p b t) ∧
            CommitOk (pqInitInputs WP p b t) (MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP p m r) a ∧
            observe (pqSendInputs WP p m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP p m r) (pqSendModel WP p m r.toList) ∧
            CommitOk (pqSendInputs WP p m r) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP p (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP p (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP p c rc) ∧
            CommitOk (pqRecvInputs WP p (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, p.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP p (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP p m rc) ∧
            CommitOk (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP p c rc) a ∧
            observe (pqRecvInputs WP p c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP p c rc).files) ∧
            CommitOk (pqRecvInputs WP p c rc) (MainResult.ofAnswer a))

/-- `CliSpecPqxdhNoMatch` tight `main` specification over explicit placements `(mpl, mmpl)` and
extern family `ext`. -/
def MainOkCliExtOverTightCodePlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (CodeOk : Memory → Prop)
    (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (mainSpecTightPlacedAt CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) Run)) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)

abbrev MainOkCliExtPqTightPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  MainOkCliExtPqTightCodePlacedAt mpl mmpl ext mainIdx (LibsignalCodeRoLoaded mpl) brkStart lim

abbrev MainOkCliExtOverTightPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  MainOkCliExtOverTightCodePlacedAt mpl mmpl ext mainIdx (LibsignalCodeRoLoaded mpl) brkStart lim

abbrev MainOkCliM2PqTightPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  MainOkCliExtPqTightPlacedAt mpl mmpl (cliM2ExternsPlaced mmpl) mainIdx brkStart lim

abbrev MainOkCliM2OverTightPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  MainOkCliExtOverTightPlacedAt mpl mmpl (cliM2ExternsPlaced mmpl) mainIdx brkStart lim

abbrev MainOkCliM2WithClonePqTightPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  MainOkCliExtPqTightPlacedAt mpl mmpl (cliM2ExternsWithClonePlaced mmpl) mainIdx brkStart lim

abbrev MainOkCliM2WithCloneOverTightPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (brkStart : BitVec 64) (lim : BudgetLimits) : Prop :=
  MainOkCliExtOverTightPlacedAt mpl mmpl (cliM2ExternsWithClonePlaced mmpl) mainIdx brkStart lim

/-- Read-only-`argv` `NeedLocks` counterpart of `MainOkCliExtPqTightCodePlacedAt`. -/
def MainOkCliExtPqB2NeedLocksPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ p : PqParty, PqxdhPartyInSpecDomain WP p →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
          p.session = none →
          ∃ a, Run (pqInitInputs WP p b t) a ∧
            observe (pqInitInputs WP p b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP p b t) (pqInitModel X WP p b t) ∧
            CommitOk (pqInitInputs WP p b t) (MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP p m r) a ∧
            observe (pqSendInputs WP p m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP p m r) (pqSendModel WP p m r.toList) ∧
            CommitOk (pqSendInputs WP p m r) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP p (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP p (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP p c rc) ∧
            CommitOk (pqRecvInputs WP p (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, p.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP p (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP p m rc) ∧
            CommitOk (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP p c rc) a ∧
            observe (pqRecvInputs WP p c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP p c rc).files) ∧
            CommitOk (pqRecvInputs WP p c rc) (MainResult.ofAnswer a))

/-- Read-only-`argv` `NeedLocks` counterpart of `MainOkCliExtOverTightCodePlacedAt`. -/
def MainOkCliExtOverB2NeedLocksPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)

/-! ## Strict `CliSpecPqxdh` and `CliSpecPqxdhNoMatch` composers -/

theorem cliSpecPqxdh_ext_strict_of_harness
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
      mmpl lim fineCostModel.init cliMainStk CodeOk (cliStaticsPlacedAt mpl))
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmainW
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtPlacedSigAt_of_strict_main_stdinOverCap hext hE htok hCode hH hmainW
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtPlacedSigAt_of_strict_main_sendOverCap hext hE htok hCode hH hmainW
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmainW
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtPlacedSigAt_of_strict_main_stdinOverCap hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtPlacedSigAt_of_strict_main_stdinOverCap hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtPlacedSigAt_of_strict_main_stdinOverCap hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

theorem cliSpecPqxdhNoMatch_ext_strict_of_harness
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
      mmpl lim fineCostModel.init cliMainStk CodeOk (cliStaticsPlacedAt mpl))
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtPlacedSigAt_of_strict_main_stdinOverCap hext hE htok hCode hH hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact ⟨observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a,
      cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmainW
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) rfl
        (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit,
      hobsEx⟩

theorem cliSpecPqxdh_and_noMatch_ext_strict_of_harness
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
      mmpl lim fineCostModel.init cliMainStk CodeOk (cliStaticsPlacedAt mpl))
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim)
    (hover : MainOkCliExtOverTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩ :=
  fun X =>
    ⟨cliSpecPqxdh_ext_strict_of_harness hext hE htok hCode hH hDropNz hmain X,
     cliSpecPqxdhNoMatch_ext_strict_of_harness hext hE htok hCode hH hDropNz hover X⟩

theorem cliSpecPqxdh_ext_strict_of_b2_needLocks
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_sendOverCap hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred hext hE htok hfs_eq hCode hH
        hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

/-! ## Strict placed ELF and binary correctness theorems -/

/-- Strict (`0`-excused-abort) relocatable ELF correctness under `(mpl, mmpl)`, extern family
`ext`, and `main` block `mainIdx`. -/
def CliPqxdhExtElfCorrectStrictPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩

def CliPqxdhExtOnInputsElfCorrectStrictPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩

abbrev CliPqxdhM2ElfCorrectStrictPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (elf : ElfImage) : Prop :=
  CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl (cliM2ExternsPlaced mmpl) mainIdx elf

abbrev CliPqxdhM2ElfCorrectStrictPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliPqxdhM2ElfCorrectStrictPlacedAt mpl mmpl 617 elf

abbrev CliPqxdhM2WithCloneElfCorrectStrictPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (elf : ElfImage) : Prop :=
  CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl (cliM2ExternsWithClonePlaced mmpl) mainIdx elf

abbrev CliPqxdhM2WithCloneElfCorrectStrictPlaced
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliPqxdhM2WithCloneElfCorrectStrictPlacedAt mpl mmpl 617 elf

def CliPqxdhM2BinaryCorrectStrictPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧
    VerifiedLibraries.mallocngLib.Placeable mmpl ∧
    VerifiedLibraries.mallocngLib.InElf elf mmpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl ∧
    CliPqxdhM2ElfCorrectStrictPlacedAt mpl mmpl mainIdx elf

def CliPqxdhM2BinaryCorrectStrictPlaced (mainIdx : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∀ (mpl mmpl : Obj.MultiPlacement),
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhM2BinaryCorrectStrictPlacedAt mpl mmpl mainIdx bytes

def CliPqxdhM2WithCloneBinaryCorrectStrictPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (mainIdx : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧
    VerifiedLibraries.mallocngLib.Placeable mmpl ∧
    VerifiedLibraries.mallocngLib.InElf elf mmpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl ∧
    CliPqxdhM2WithCloneElfCorrectStrictPlacedAt mpl mmpl mainIdx elf

def CliPqxdhM2WithCloneBinaryCorrectStrictPlaced (mainIdx : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∀ (mpl mmpl : Obj.MultiPlacement),
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhM2WithCloneBinaryCorrectStrictPlacedAt mpl mmpl mainIdx bytes

/-- Static ELF and placement `(mpl, mmpl)` assumption bundle for `MuslHarnessFinePerInput`. -/
structure CliElfExtHarnessAssumptions
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop where
  elfStaticOk : ElfStaticOk elf
  codeMatches : CliElfCodeMatchesPlaced mpl mmpl elf
  mallocngPlaceable : VerifiedLibraries.mallocngLib.Placeable mmpl
  mallocngInElf : VerifiedLibraries.mallocngLib.InElf elf mmpl
  mallocngDataDisjoint : VerifiedLibraries.mallocngLib.DataDisjoint mmpl
  tokenCells : CliElfTokenCellsPlacedAt mpl elf
  mallocngLayout : CliElfMallocngLayout elf lim
  base547NeZero : mpl.base 547 ≠ 0#64
  codeLoaded : ∀ (W : CliHooks) (m : Memory),
    CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m
  harness : ∀ W : CliHooks,
    MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
      mmpl lim fineCostModel.init cliMainStk CodeOk (cliStaticsPlacedAt mpl)

/-- Concrete `musl` startup/exit assumption bundle discharging `CliElfExtHarnessAssumptions`. -/
structure CliElfExtMuslStartAssumptions
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop where
  elfStaticOk : ElfStaticOk elf
  codeMatches : CliElfCodeMatchesPlaced mpl mmpl elf
  mallocngPlaceable : VerifiedLibraries.mallocngLib.Placeable mmpl
  mallocngInElf : VerifiedLibraries.mallocngLib.InElf elf mmpl
  mallocngDataDisjoint : VerifiedLibraries.mallocngLib.DataDisjoint mmpl
  tokenCells : CliElfTokenCellsPlacedAt mpl elf
  mallocngLayout : CliElfMallocngLayout elf lim
  base547NeZero : mpl.base 547 ≠ 0#64
  codeLoaded : ∀ (W : CliHooks) (m : Memory),
    CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m
  libcAt : (mallocngAddrsOfPlacement mmpl).libc = elf.entry + 0x21e8#64
  noHookStartup : ∀ (W : CliHooks) (k : BitVec 64), k.toNat < 0xb90 →
    (cliProgExtPlacedAt mpl ext mainIdx W).externAt? (elf.entry + k) = none
  codeOkPatched : ∀ (i : Inputs) (s0 sm : State),
    (patchElfTokensPlacedAt mpl elf).loadState (cliInputs i) = .ok s0 →
    s0.mem.KeepsFrozen sm.mem →
    CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem
  roTablesPatched : ∀ (i : Inputs) (s0 : State),
    (patchElfTokensPlacedAt mpl elf).loadState (cliInputs i) = .ok s0 →
    MallocngRoTablesInMem mmpl s0.mem
  muslStartup :
    ∃ (muslCode : List (BitVec 8)) (dynPageImm pageImm : BitVec 64)
      (addImm : BitVec 12) (supportPred : Nat → Prop),
      CliElfMusl (patchElfTokensPlacedAt mpl elf) muslCode ∧
      MuslStartFetchAt ({ code := muslCode } : Program) 0#64 dynPageImm pageImm addImm ∧
      MuslExitFetch ({ code := muslCode } : Program) 0#64 ∧
      mpl.base mainIdx = mainPcOf elf.entry pageImm addImm ∧
      (∀ (i : Inputs) (s0 : State),
        (patchElfTokensPlacedAt mpl elf).loadState (cliInputs i) = .ok s0 →
        SupportedOn 0#64 supportPred s0.mem (mallocngRwBssAt mmpl ∗ cliStaticsPlacedAt mpl)) ∧
      (∀ k, supportPred k → k < stackBase ∧
        ¬((elf.entry + 0x2000#64).toNat ≤ k ∧ k < (elf.entry + 0x2000#64).toNat + 600))

theorem CliElfExtMuslStartAssumptions.toHarnessAssumptions
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {CodeOk : Memory → Prop} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtMuslStartAssumptions mpl mmpl ext mainIdx CodeOk lim elf) :
    CliElfExtHarnessAssumptions mpl mmpl ext mainIdx CodeOk lim elf where
  elfStaticOk := H.elfStaticOk
  codeMatches := H.codeMatches
  mallocngPlaceable := H.mallocngPlaceable
  mallocngInElf := H.mallocngInElf
  mallocngDataDisjoint := H.mallocngDataDisjoint
  tokenCells := H.tokenCells
  mallocngLayout := H.mallocngLayout
  base547NeZero := H.base547NeZero
  codeLoaded := H.codeLoaded
  harness := fun W => by
    obtain ⟨_, _, _, _, _, hMusl, hStart, hExit, hPc, hSupp, hBounds⟩ := H.muslStartup
    exact muslHarnessFinePerInput_of_muslStartFine_blockProgram
      (elf := patchElfTokensPlacedAt mpl elf)
      (H.noHookStartup W) hMusl H.libcAt hStart hExit
      ((cliElfMallocngLayout_iff_patchElfTokensPlacedAt).mpr H.mallocngLayout)
      hPc H.codeOkPatched H.roTablesPatched hSupp hBounds

/-- Static ELF and placement `(mpl, mmpl)` assumption bundle for
`MuslHarnessFineNeedLocksPerInput`. -/
structure CliElfExtB2NeedLocksAssumptions
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop where
  elfStaticOk : ElfStaticOk elf
  codeMatches : CliElfCodeMatchesPlaced mpl mmpl elf
  mallocngPlaceable : VerifiedLibraries.mallocngLib.Placeable mmpl
  mallocngInElf : VerifiedLibraries.mallocngLib.InElf elf mmpl
  mallocngDataDisjoint : VerifiedLibraries.mallocngLib.DataDisjoint mmpl
  tokenCells : CliElfTokenCellsPlacedAt mpl elf
  mallocngLayout : CliElfMallocngLayout elf lim
  base547NeZero : mpl.base 547 ≠ 0#64
  stkLo : exitStk ≤ stk
  stkHi : stk ≤ 2 ^ 64
  fsEq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i)
  codeLoaded : ∀ (W : CliHooks) (m : Memory),
    CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m
  harness : ∀ W : CliHooks,
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl)

/-- Strict placed ELF correctness from `CliElfExtHarnessAssumptions`, `hmain`, and `hover`. -/
theorem cliPqxdhExtElfCorrectStrictPlacedAt_of_assumptions
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {CodeOk : Memory → Prop} {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtHarnessAssumptions mpl mmpl ext mainIdx CodeOk lim elf)
    (hmain : MainOkCliExtPqTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim)
    (hover : MainOkCliExtOverTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim) :
    CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext mainIdx elf :=
  ⟨H.codeMatches, fun W =>
    cliSpecPqxdh_and_noMatch_ext_strict_of_harness
      (hext W) H.elfStaticOk H.tokenCells (H.codeLoaded W) (H.harness W)
      H.base547NeZero hmain hover⟩

theorem cliPqxdhExtElfCorrectStrictPlacedAt_of_muslStartAssumptions
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {CodeOk : Memory → Prop} {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtMuslStartAssumptions mpl mmpl ext mainIdx CodeOk lim elf)
    (hmain : MainOkCliExtPqTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim)
    (hover : MainOkCliExtOverTightCodePlacedAt mpl mmpl ext mainIdx CodeOk elf.brkStart lim) :
    CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext mainIdx elf :=
  cliPqxdhExtElfCorrectStrictPlacedAt_of_assumptions hext H.toHarnessAssumptions hmain hover

theorem cliPqxdhM2ElfCorrectStrictPlacedAt_of_assumptions
    {mpl mmpl : Obj.MultiPlacement} {mainIdx : Nat} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsPlaced mmpl)
      mainIdx (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2PqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim)
    (hover : MainOkCliM2OverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2ElfCorrectStrictPlacedAt mpl mmpl mainIdx elf :=
  cliPqxdhExtElfCorrectStrictPlacedAt_of_assumptions
    (externPreservesNoAllocFailed_cliM2ExternsPlaced mmpl) H hmain hover

theorem cliPqxdhM2ElfCorrectStrictPlaced_of_assumptions
    {mpl mmpl : Obj.MultiPlacement} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsPlaced mmpl)
      617 (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2PqTightPlacedAt mpl mmpl 617 elf.brkStart lim)
    (hover : MainOkCliM2OverTightPlacedAt mpl mmpl 617 elf.brkStart lim) :
    CliPqxdhM2ElfCorrectStrictPlaced mpl mmpl elf :=
  cliPqxdhM2ElfCorrectStrictPlacedAt_of_assumptions H hmain hover

theorem cliPqxdhM2ElfCorrectStrictPlacedAt_of_muslStartAssumptions
    {mpl mmpl : Obj.MultiPlacement} {mainIdx : Nat} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtMuslStartAssumptions mpl mmpl (cliM2ExternsPlaced mmpl)
      mainIdx (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2PqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim)
    (hover : MainOkCliM2OverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2ElfCorrectStrictPlacedAt mpl mmpl mainIdx elf :=
  cliPqxdhM2ElfCorrectStrictPlacedAt_of_assumptions H.toHarnessAssumptions hmain hover

theorem cliPqxdhM2WithCloneElfCorrectStrictPlacedAt_of_assumptions
    {mpl mmpl : Obj.MultiPlacement} {mainIdx : Nat} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsWithClonePlaced mmpl)
      mainIdx (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2WithClonePqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim)
    (hover : MainOkCliM2WithCloneOverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2WithCloneElfCorrectStrictPlacedAt mpl mmpl mainIdx elf :=
  cliPqxdhExtElfCorrectStrictPlacedAt_of_assumptions
    (externPreservesNoAllocFailed_cliM2ExternsWithClonePlaced mmpl) H hmain hover

theorem cliPqxdhM2WithCloneElfCorrectStrictPlaced_of_assumptions
    {mpl mmpl : Obj.MultiPlacement} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsWithClonePlaced mmpl)
      617 (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2WithClonePqTightPlacedAt mpl mmpl 617 elf.brkStart lim)
    (hover : MainOkCliM2WithCloneOverTightPlacedAt mpl mmpl 617 elf.brkStart lim) :
    CliPqxdhM2WithCloneElfCorrectStrictPlaced mpl mmpl elf :=
  cliPqxdhM2WithCloneElfCorrectStrictPlacedAt_of_assumptions H hmain hover

theorem cliPqxdhM2WithCloneElfCorrectStrictPlacedAt_of_muslStartAssumptions
    {mpl mmpl : Obj.MultiPlacement} {mainIdx : Nat} {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtMuslStartAssumptions mpl mmpl (cliM2ExternsWithClonePlaced mmpl)
      mainIdx (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2WithClonePqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim)
    (hover : MainOkCliM2WithCloneOverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2WithCloneElfCorrectStrictPlacedAt mpl mmpl mainIdx elf :=
  cliPqxdhM2WithCloneElfCorrectStrictPlacedAt_of_assumptions H.toHarnessAssumptions hmain hover

theorem cliPqxdhM2BinaryCorrectStrictPlacedAt_of_assumptions
    {mpl mmpl : Obj.MultiPlacement} {mainIdx : Nat} {lim : BudgetLimits}
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (H : CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsPlaced mmpl)
      mainIdx (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2PqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim)
    (hover : MainOkCliM2OverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2BinaryCorrectStrictPlacedAt mpl mmpl mainIdx bytes :=
  ⟨elf, hparse, H.mallocngPlaceable, H.mallocngInElf, H.mallocngDataDisjoint,
    cliPqxdhM2ElfCorrectStrictPlacedAt_of_assumptions H hmain hover⟩

theorem cliPqxdhM2BinaryCorrectStrictPlaced_of_assumptions
    {mainIdx : Nat} {lim : BudgetLimits} {bytes : List (BitVec 8)}
    (hAt : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage),
      ElfImage.parse bytes = .ok elf →
      libsignalSessionLib.Placeable mpl →
      libsignalSessionLib.InElf elf mpl →
      VerifiedLibraries.mallocngLib.Placeable mmpl →
      VerifiedLibraries.mallocngLib.InElf elf mmpl →
      CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsPlaced mmpl)
        mainIdx (LibsignalCodeRoLoaded mpl) lim elf ∧
      MainOkCliM2PqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim ∧
      MainOkCliM2OverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2BinaryCorrectStrictPlaced mainIdx bytes := by
  intro mpl mmpl ⟨elf, hparse, hpl, hin⟩ ⟨elf', hparse', hmpl, hmin⟩
  rw [hparse] at hparse'
  injection hparse' with helf
  subst helf
  obtain ⟨H, hmain, hover⟩ := hAt mpl mmpl elf hparse hpl hin hmpl hmin
  exact cliPqxdhM2BinaryCorrectStrictPlacedAt_of_assumptions hparse H hmain hover

theorem cliPqxdhM2WithCloneBinaryCorrectStrictPlacedAt_of_assumptions
    {mpl mmpl : Obj.MultiPlacement} {mainIdx : Nat} {lim : BudgetLimits}
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (H : CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsWithClonePlaced mmpl)
      mainIdx (LibsignalCodeRoLoaded mpl) lim elf)
    (hmain : MainOkCliM2WithClonePqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim)
    (hover : MainOkCliM2WithCloneOverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2WithCloneBinaryCorrectStrictPlacedAt mpl mmpl mainIdx bytes :=
  ⟨elf, hparse, H.mallocngPlaceable, H.mallocngInElf, H.mallocngDataDisjoint,
    cliPqxdhM2WithCloneElfCorrectStrictPlacedAt_of_assumptions H hmain hover⟩

theorem cliPqxdhM2WithCloneBinaryCorrectStrictPlaced_of_assumptions
    {mainIdx : Nat} {lim : BudgetLimits} {bytes : List (BitVec 8)}
    (hAt : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage),
      ElfImage.parse bytes = .ok elf →
      libsignalSessionLib.Placeable mpl →
      libsignalSessionLib.InElf elf mpl →
      VerifiedLibraries.mallocngLib.Placeable mmpl →
      VerifiedLibraries.mallocngLib.InElf elf mmpl →
      CliElfExtHarnessAssumptions mpl mmpl (cliM2ExternsWithClonePlaced mmpl)
        mainIdx (LibsignalCodeRoLoaded mpl) lim elf ∧
      MainOkCliM2WithClonePqTightPlacedAt mpl mmpl mainIdx elf.brkStart lim ∧
      MainOkCliM2WithCloneOverTightPlacedAt mpl mmpl mainIdx elf.brkStart lim) :
    CliPqxdhM2WithCloneBinaryCorrectStrictPlaced mainIdx bytes := by
  intro mpl mmpl ⟨elf, hparse, hpl, hin⟩ ⟨elf', hparse', hmpl, hmin⟩
  rw [hparse] at hparse'
  injection hparse' with helf
  subst helf
  obtain ⟨H, hmain, hover⟩ := hAt mpl mmpl elf hparse hpl hin hmpl hmin
  exact cliPqxdhM2WithCloneBinaryCorrectStrictPlacedAt_of_assumptions hparse H hmain hover

theorem cliPqxdhExtOnInputsElfCorrectStrictPlacedAt_of_b2NeedLocksAssumptions
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    CliPqxdhExtOnInputsElfCorrectStrictPlacedAt mpl mmpl ext mainIdx inputsOf elf :=
  ⟨H.codeMatches, fun W X =>
    ⟨cliSpecPqxdh_ext_strict_of_b2_needLocks (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hmain X,
     cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hover X⟩⟩

/-! ## Equality bridges to `CliPqxdhElfCorrectStrictPlaced` -/

theorem cliRunsToPlaced_iff_ext_of_progEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (i : Inputs) (o : Outcome) :
    CliRunsToPlaced mpl mmpl elf W i o ↔
      CliRunsToExtOnInputsAt mpl ext mainIdx cliProcessInputs elf W i o := by
  unfold CliRunsToPlaced CliRunsToExtOnInputsAt
  rw [hprog]

theorem cliRunPlacedSig_eq_cliRunExtPlacedSigAt_of_progEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W) :
    cliRunPlacedSig mpl mmpl elf W = cliRunExtPlacedSigAt mpl ext mainIdx elf W := by
  funext i
  unfold cliRunPlacedSig cliRunExtPlacedSigAt cliRunExtOnInputsSigAt
  have hex : (∃ o, CliRunsToPlaced mpl mmpl elf W i o) ↔
      (∃ o, CliRunsToExtOnInputsAt mpl ext mainIdx cliProcessInputs elf W i o) :=
    exists_congr (cliRunsToPlaced_iff_ext_of_progEq hprog i)
  by_cases h1 : ∃ o, CliRunsToPlaced mpl mmpl elf W i o
  · have h2 : ∃ o, CliRunsToExtOnInputsAt mpl ext mainIdx cliProcessInputs elf W i o :=
      hex.mp h1
    simp only [h1, h2, ↓reduceDIte]
    congr 1
    have hc1 : CliRunsToExtOnInputsAt mpl ext mainIdx cliProcessInputs elf W i
        (Classical.choose h1) :=
      (cliRunsToPlaced_iff_ext_of_progEq hprog i _).mp (Classical.choose_spec h1)
    exact cliRunsToExtOnInputsAt_unique hc1 (Classical.choose_spec h2)
  · have h2 : ¬ ∃ o, CliRunsToExtOnInputsAt mpl ext mainIdx cliProcessInputs elf W i o :=
      fun hc => h1 (hex.mpr hc)
    simp only [h1, h2, ↓reduceDIte]

theorem cliPqxdhElfCorrectStrictPlaced_of_extProgEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hStrict : CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext mainIdx elf) :
    CliPqxdhElfCorrectStrictPlaced mpl mmpl elf := by
  refine ⟨hStrict.1, fun W X => ?_⟩
  rw [cliRunPlacedSig_eq_cliRunExtPlacedSigAt_of_progEq (hprog W)]
  exact hStrict.2 W X

theorem cliPqxdhElfCorrectPlaced_of_extProgEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hStrict : CliPqxdhExtElfCorrectStrictPlacedAt mpl mmpl ext mainIdx elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_strict (cliPqxdhElfCorrectStrictPlaced_of_extProgEq hprog hStrict)

theorem cliPqxdhAllocNeverFailsPlaced_of_m2ProgEq
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliM2ProgPlacedSig mpl mmpl W) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W := by
  intro i _ s0 s hload hsteps
  rw [hprog] at hsteps
  exact cliM2_allocNeverFailsPlaced mpl mmpl elf W i s0 s hload hsteps

theorem cliPqxdhAllocNeverFailsPlaced_of_m2WithCloneProgEq
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliM2ProgWithClonePlacedSig mpl mmpl W) :
    CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W := by
  intro i _ s0 s hload hsteps
  rw [hprog] at hsteps
  exact cliM2WithClone_allocNeverFailsPlaced mpl mmpl elf W i s0 s hload hsteps

end LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
