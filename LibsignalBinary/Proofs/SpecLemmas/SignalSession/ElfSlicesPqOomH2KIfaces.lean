/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime

/-!
# Spine-B (`Block 579`) and Spine-C (`Slots 464/463/521/520`) Interfaces (`ElfSlicesPqOomH2KIfaces`)

**Checked by Lean.**

Defines the pre-only `FdsGe3Closed` contract interfaces separating:
- **Spine A** (`main`, Block `617`),
- **Spine B** (`signal_session::run`, Block `579`), and
- **Spine C** (inner wrapper slots `464` `encrypt`, `463` `decryptSignal`, `521` `initiate`, and
  `520` `decryptPrekey`).

Because neither `main` after `run` (`M5` / `M6` write-only hops) nor `run` after any inner slot
invokes `read_file`, both Spine-B (`runSpecTightPlacedPreFd`) and Spine-C (`slotWithPreFdsGe3Closed`)
carry `⌜FdsGe3Closed s0.fs⌝` on `pre` only, leaving `post`, `onPanic`, and `onOom` unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces

open Arm64
  (GhostName Memory Program SepProp Spec State satisfies_pure_sepConj sepConj_assoc subroutine_ok
   subroutine_ok_mono)
open Arm64.Obj (MultiPlacement)
open CryptoVerification
  (LibsignalFrozen LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfImage cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliResStack cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk mProgPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost InitGhost RunNeeds RunSem mkSlot runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c InitOk₀ cliDecryptPrekeyNeed cliInitiateNeed decPkDefD2c initDef)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (CalleeSlot CalleeSlot.OkPlaced RunBudgets RunSlots runNeed)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
  (canonOrFallbackRunEnvExact')

/-! ## Pre-Only `FdsGe3Closed` Spec and Slot Combinators -/

/-- Strengthen `spec.pre` with `⌜FdsGe3Closed s0.fs⌝`, leaving `post`, `onPanic`, and `onOom`
unchanged. Used at call boundaries after which the caller executes no further `read_file`
(`run` @ Block `579` from `main` `M4`, and inner slots `464`/`463`/`521`/`520` from `run`). -/
def withPreFdsGe3Closed {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => ⌜FdsGe3Closed s0.fs⌝ ∗ spec.pre x s0 }

theorem extract_withPreFdsGe3Closed {α : Type} {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withPreFdsGe3Closed spec).pre x s0 ∗ R) :
    FdsGe3Closed s0.fs ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withPreFdsGe3Closed] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

/-- Any plain `subroutine_ok` contract trivially satisfies `withPreFdsGe3Closed`. -/
theorem subroutine_ok_withPreFdsGe3Closed_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withPreFdsGe3Closed spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hpre => (extract_withPreFdsGe3Closed hpre).2)
    (fun _ _ _ _ hpost => hpost)

/-- Two-sided `withFdsGe3Closed` (`pre` + `post`) weakens in 1 step to `withPreFdsGe3Closed`
(`pre` only). -/
theorem subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withFdsGe3Closed spec)) :
    subroutine_ok prog entry (withPreFdsGe3Closed spec) := by
  refine subroutine_ok_mono h (fun _ _ _ hpre => hpre) ?_
  intro x R s0 sf hpost
  dsimp only [withFdsGe3Closed, withPreFdsGe3Closed] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- Pre-only `FdsGe3Closed` wrapper on a `RunSkeleton.CalleeSlot` (preserves `Ghost` and `need`
definitionally). -/
def slotWithPreFdsGe3Closed (σ : CalleeSlot) : CalleeSlot :=
  { σ with spec := fun stk => withPreFdsGe3Closed (σ.spec stk) }

/-- Two-sided `FdsGe3Closed` wrapper on a `RunSkeleton.CalleeSlot` (preserves `Ghost` and `need`
definitionally). -/
def slotWithFdsGe3Closed (σ : CalleeSlot) : CalleeSlot :=
  { σ with spec := fun stk => withFdsGe3Closed (σ.spec stk) }

theorem okPlaced_slotWithPreFdsGe3Closed_of_plain {callerProg : Program} {target : BitVec 64}
    {σ : CalleeSlot} (h : σ.OkPlaced callerProg target) :
    (slotWithPreFdsGe3Closed σ).OkPlaced callerProg target :=
  fun stk hlo hhi => subroutine_ok_withPreFdsGe3Closed_of_plain (h stk hlo hhi)

theorem okPlaced_slotWithPreFdsGe3Closed_of_withFdsGe3Closed
    {callerProg : Program} {target : BitVec 64} {σ : CalleeSlot}
    (h : (slotWithFdsGe3Closed σ).OkPlaced callerProg target) :
    (slotWithPreFdsGe3Closed σ).OkPlaced callerProg target :=
  fun stk hlo hhi => subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed (h stk hlo hhi)

/-- Lift the 4 inner `RunSlots` (`encrypt` 464, `decryptSignal` 463, `initiate` 521,
`decryptPrekey` 520) with `slotWithPreFdsGe3Closed`, leaving `kemDeserialize` (590, pure codec)
unchanged. Preserves `runNeed B` definitionally. -/
def slotsWithPreFdsGe3Closed (slots : RunSlots) : RunSlots :=
  { encrypt := slotWithPreFdsGe3Closed slots.encrypt
    decryptSignal := slotWithPreFdsGe3Closed slots.decryptSignal
    initiate := slotWithPreFdsGe3Closed slots.initiate
    decryptPrekey := slotWithPreFdsGe3Closed slots.decryptPrekey
    kemDeserialize := slots.kemDeserialize }

theorem runNeed_slotsWithPreFdsGe3Closed (B : RunBudgets) (slots : RunSlots) :
    runNeed B (slotsWithPreFdsGe3Closed slots) = runNeed B slots :=
  rfl

/-! ## Spine-B (`signal_session::run`, Block `579`) Interfaces -/

/-- K-route `run` spec at Block `579`: `runSpecTightPlaced` with `⌜FdsGe3Closed s0.fs⌝` on `pre`
only (`post`, `onPanic`, `onOom` identical to `runSpecTightPlaced`). -/
def runSpecTightPlacedPreFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnvPred : RunCall → List AllocEvent → Prop)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) :
    Spec (RunCall × M.σ) :=
  withPreFdsGe3Closed (runSpecTightPlaced CodeOk A lim RunEnvPred uuidParse Run wrOk resStack)

/-- Generic Spine-B Block-`579` `subroutine_ok` obligation on `mProgPlaced H` at
`runSpecTightPlacedPreFd (LibsignalFrozen mpl)`. -/
def h2ki_RunTightAt579PreFd
    {mpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (H : LibsignalHooks)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnvPred : RunCall → List AllocEvent → Prop)
    (S : RunSem) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  subroutine_ok (mProgPlaced H) (mpl.base 579)
    (runSpecTightPlacedPreFd (LibsignalFrozen mpl) A lim RunEnvPred
      uuidTryParse (runRel S) cliWrOk cliResStack)

/-- Explicit-argument Spine-B `canon'` slice interface at ghost table `ghFixed`. -/
def h2ki_SpineBCanonSliceAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    h2ki_RunTightAt579PreFd hblk hext_nodup
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (canonOrFallbackRunEnvExact' PksmTryFromEnv mpl mmpl cliElfImage.brkStart
        hblk hext_nodup X W γ tp)
      (cliRunSemD2c_placed X W)

/-- Witness-packaged Spine-B `canon'` slice interface for `hmain` and `hinitSem`. -/
abbrev h2ki_SpineBCanonSliceK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2ki_SpineBCanonSliceAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-- Explicit-argument Spine-B interface for D3 `RunSem` slices (`hoverD3`, `huntyped`, `hpathB`,
`hvalidMatch`), matching the `hrun` hypothesis of `D3MainLiftGlueF3.mainSubroutineD3F3_of_domScopedRunTight`
with `runSpecTightPlacedPreFd`. -/
def h2ki_SpineBRunTightOfSemAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (brkStart : BitVec 64)
    (SemOf : CliHooks → RunSem)
    (RunEnvOf : CliHooks → GhostName → BitVec 64 → RunCall → List AllocEvent → Prop) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    h2ki_RunTightAt579PreFd hblk hext_nodup
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (RunEnvOf W γ tp) (SemOf W)

abbrev h2ki_SpineBRunTightOfSemK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (SemOf : CliHooks → RunSem)
    (RunEnvOf : CliHooks → GhostName → BitVec 64 → RunCall → List AllocEvent → Prop) : Prop :=
  h2ki_SpineBRunTightOfSemAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed cliElfImage.brkStart
    SemOf RunEnvOf

/-! ## Spine-C (`Slots 464 / 463 / 521 / 520`) Interfaces -/

/-- Spine-C Slot `464` (`encrypt`) pre-only `FdsGe3Closed` contract on `lsProg_579 H`. -/
def h2ki_EncryptSlot464OkAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  (slotWithPreFdsGe3Closed
    (mkSlot
      (encSlotSpecPlaced A lim (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt)).OkPlaced
    (lsProg_579 H) (lsmpl.base 464)

def h2ki_W1EncryptSlot464OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    h2ki_EncryptSlot464OkAtPreFd
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      X W

/-- Spine-C Slot `463` (`decryptSignal`) pre-only `FdsGe3Closed` contract on `lsProg_579 H`. -/
def h2ki_DecryptSignalSlot463OkAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  (slotWithPreFdsGe3Closed
    (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal)).OkPlaced
    (lsProg_579 H) (lsmpl.base 463)

def h2ki_W2DecryptSignalSlot463OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    h2ki_DecryptSignalSlot463OkAtPreFd
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      X W

/-- Spine-C Slot `521` (`initiate`) pre-only `FdsGe3Closed` contract on `lsProg_579 H`. -/
def CliInitSlotOkPlacedAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
    sEnvs.initiate = InitEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
    needs.initiate = cliInitiateNeed cliRunBudgets →
    (slotWithPreFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).initiate).OkPlaced
      (lsProg_579 H) (lsmpl.base 521)

abbrev CliInitSlotOkPlacedPreFd [LibsignalPlacement] (mmpl : MultiPlacement)
    (gh : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  CliInitSlotOkPlacedAtPreFd (cliGhostExterns gh (cliExternsPlaced mmpl W)) A lim InitEnv X W

def h2ki_W3InitSlot521OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    CliInitSlotOkPlacedPreFd mmpl w.ghFixed
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (realCliInitBinarySlotEnvFixed W) X W

/-- Spine-C Slot `520` (`decryptPrekey`, D2c frozen) pre-only `FdsGe3Closed` contract on
`lsProg_579 H`. -/
def DecPkD2cSlotOkFrozenPlacedAtPreFd [LibsignalPlacement]
    {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced
      (lsProg_579 H) (lsmpl.base 520)

/-- `LibsignalFrozen`-guarded pre-only `FdsGe3Closed` D2c `decryptPrekey` slot contract at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
def DecPkD2cSlotOkFrozenPlacedPreFd [LibsignalPlacement] (mmpl : MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkFrozenPlacedAtPreFd
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

def h2ki_W4DecPkCanonSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    DecPkD2cSlotOkFrozenPlacedAtPreFd
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) X W
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliDecPkCanonSlotEnvExact' X W)

/-- Witness-packaged Spine-C Slot `520` (`decryptPrekey`, D3 untyped) interface at
`w : F3CliElfGhostWitnessK`. -/
def h2ki_UntypedDecPkSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (binaryKitRunSlotEnvsExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf
            (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
            cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
            SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
