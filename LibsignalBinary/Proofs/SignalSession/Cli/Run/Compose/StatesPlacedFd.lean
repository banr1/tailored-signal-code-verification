/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Machine-Level Hop States for `signal_session::run`

Defines cut-point state carriers conjoining `FdsGe3Closed` (`AtRunEntryPlacedFd`,
`AtDispatchPlacedFd`, `AtInit1PlacedFd`, `AtInit2PlacedFd`), pre-guarded `run` specifications
(`runSpecPlacedPreFd`, `runSpecTightPlacedPreFd`, `runSpecAnyPlacedPreFd`), and entry/exit bridge
lemmas on Block `579` (`lsProg_579`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtInit2Placed AtRunEntryPlaced Init1Data Init2Data
   MeAtDispatch RunSem runFiles runPanicProp runRel)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (any_placed_onOom_eq any_placed_onPanic_of_runPanic any_placed_post_of_runPost
   placed_onOom_eq placed_onPanic_of_runPanic placed_post_of_runPost
   runEntryMemPlaced runEntry_of_any_placed_pre runEntry_of_placed_pre
   runPostAnyPlaced runPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (extract_withPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (runSpecAnyPlaced runSpecPlaced)

/-! ## 1. Named Cut-Point State Carriers Conjoining `FdsGe3Closed` -/

def AtRunEntryPlacedFd [LibsignalPlacement] (CodeOk : Memory → Prop) (S : RunSem)
    (g : RunCall) (s0 : State) : Prop :=
  AtRunEntryPlaced CodeOk S g s0 ∧ FdsGe3Closed s0.fs

def AtDispatchPlacedFd [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (me : MeAtDispatch) (s0 s : State) : Prop :=
  AtDispatchPlaced CodeOk g me s0 s ∧ FdsGe3Closed s.fs

def AtInit1PlacedFd [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (d : Init1Data) (s0 s : State) : Prop :=
  AtInit1Placed CodeOk g d s0 s ∧ FdsGe3Closed s.fs

def AtInit2PlacedFd [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (d : Init2Data) (s0 s : State) : Prop :=
  AtInit2Placed CodeOk g d s0 s ∧ FdsGe3Closed s.fs

/-! ## 2. Pre-Only `FdsGe3Closed` `run` Specifications -/

/-- `runSpecPlaced` guarded by `⌜FdsGe3Closed s0.fs⌝` on `pre` only. -/
def runSpecPlacedPreFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnvPred : RunCall → List AllocEvent → Prop)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) :
    Spec (RunCall × M.σ) :=
  withPreFdsGe3Closed (runSpecPlaced CodeOk A lim RunEnvPred uuidParse Run wrOk resStack)

/-- `runSpecTightPlaced` guarded by `⌜FdsGe3Closed s0.fs⌝` on `pre` only
(definitionally equal to both `runSpecPlacedPreFd` and
`ElfSlicesPqOomH2KIfaces.runSpecTightPlacedPreFd`). -/
def runSpecTightPlacedPreFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnvPred : RunCall → List AllocEvent → Prop)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) :
    Spec (RunCall × M.σ) :=
  withPreFdsGe3Closed (runSpecTightPlaced CodeOk A lim RunEnvPred uuidParse Run wrOk resStack)

/-- `runSpecAnyPlaced` guarded by `⌜FdsGe3Closed s0.fs⌝` on `pre` only. -/
def runSpecAnyPlacedPreFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (uuidParse : UuidParser) (Run : Inputs → RunAnswer → Prop)
    (wrOk : List (BitVec 8) → Prop) (resStack : Nat) :
    Spec (RunCall × M.σ) :=
  withPreFdsGe3Closed (runSpecAnyPlaced CodeOk A lim uuidParse Run wrOk resStack)

/-! ## 3. Entry / Exit Bridge Lemmas -/

theorem sp_lr_of_placed_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (runSpecPlacedPreFd CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).pre
        (g, st) s0 ∗ R) :
    resStack ≤ s0.sp.toNat ∧ LsRetAddr624 (s0.readReg64 .x30) := by
  obtain ⟨_, hpre0⟩ := extract_withPreFdsGe3Closed hpre
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨_, _, _, _, _, _, _, _, _, _, hspb, _, hlr_ls⟩, _⟩
  exact ⟨hspb, hlr_ls⟩

theorem runEntryFd_of_placed_pre [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpc : s0.pc = lsmpl.base 579)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (runSpecPlacedPreFd CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).pre
        (g, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    AtRunEntryPlacedFd CodeOk S g s0 ∧ FitsEnv M lim st (RunEnv g) ∧
      (s0.mem ⊨ runEntryMemPlaced A lim st g s0 resStack ∗ R) := by
  obtain ⟨hfds, hpre0⟩ := extract_withPreFdsGe3Closed hpre
  rcases runEntry_of_placed_pre hpc hrun hpre0 hsp with ⟨he, hfits, hmem⟩
  exact ⟨⟨he, hfds⟩, hfits, hmem⟩

theorem runEntryFd_of_tight_placed_pre [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpc : s0.pc = lsmpl.base 579)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (runSpecTightPlacedPreFd CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).pre
        (g, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    AtRunEntryPlacedFd CodeOk S g s0 ∧ FitsEnv M lim st (RunEnv g) ∧
      (s0.mem ⊨ runEntryMemPlaced A lim st g s0 resStack ∗ R) :=
  runEntryFd_of_placed_pre hpc hrun hpre hsp

theorem placed_post_of_runPost_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hfs0 : s0.fs.files = runFiles g.i)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = [])
    (hp : runPostPlaced CodeOk A lim RunEnv g st resStack s0 sf Pf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    (sf.mem ⊨
      (runSpecPlacedPreFd CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).post
        (g, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf :=
  placed_post_of_runPost (S := S) hfs0 hout0 hp hmf

theorem placed_onPanic_of_runPanic_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hpan : runPanicProp g s0 sf) (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      (runSpecPlacedPreFd CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).onPanic
        (g, st) s0 sf ∗ R :=
  placed_onPanic_of_runPanic (CodeOk := CodeOk) (S := S) (A := A) (lim := lim) (RunEnv := RunEnv)
    (st := st) (resStack := resStack) hpan hmf

theorem placed_onOom_eq_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    (g : RunCall) (st : M.σ) (resStack : Nat) (s0 sf : State) :
    (runSpecPlacedPreFd CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).onOom
        (g, st) s0 sf =
      ⌜False⌝ := rfl

theorem runEntryFd_of_any_placed_pre [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpc : s0.pc = lsmpl.base 579)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (runSpecAnyPlacedPreFd CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).pre
        (g, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    AtRunEntryPlacedFd CodeOk S g s0 ∧
      (s0.mem ⊨ runEntryMemPlaced A lim st g s0 resStack ∗ R) := by
  obtain ⟨hfds, hpre0⟩ := extract_withPreFdsGe3Closed hpre
  rcases runEntry_of_any_placed_pre hpc hrun hpre0 hsp with ⟨he, hmem⟩
  exact ⟨⟨he, hfds⟩, hmem⟩

theorem any_placed_post_of_runPost_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hfs0 : s0.fs.files = runFiles g.i)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = [])
    (hp : runPostAnyPlaced CodeOk A lim g resStack s0 sf Pf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    (sf.mem ⊨
      (runSpecAnyPlacedPreFd CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).post
        (g, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf :=
  any_placed_post_of_runPost (S := S) (st := st) hfs0 hout0 hp hmf

theorem any_placed_onPanic_of_runPanic_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hpan : runPanicProp g s0 sf) (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      (runSpecAnyPlacedPreFd CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).onPanic
        (g, st) s0 sf ∗ R :=
  any_placed_onPanic_of_runPanic (CodeOk := CodeOk) (S := S) (A := A) (lim := lim)
    (st := st) (resStack := resStack) hpan hmf

theorem any_placed_onOom_eq_preFd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : RunCall) (st : M.σ) (resStack : Nat) (s0 sf : State) :
    (runSpecAnyPlacedPreFd CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).onOom
        (g, st) s0 sf =
      ⌜False⌝ := rfl

theorem subroutine_ok_runSpecPlacedPreFd_mono_env [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : RunCall → List AllocEvent → Prop}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop}
    {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    {P : Program} {entry : BitVec 64}
    (himp : ∀ g evs, Env₁ g evs → Env₂ g evs)
    (hok : subroutine_ok P entry
      (runSpecPlacedPreFd CodeOk A lim Env₁ uuidParse Run wrOk resStack)) :
    subroutine_ok P entry
      (runSpecPlacedPreFd CodeOk A lim Env₂ uuidParse Run wrOk resStack) := by
  refine subroutine_ok_mono hok (fun (g, st) R s0 hpre => ?_) (fun (g, st) R s0 sf hpost => ?_)
  · obtain ⟨hfds, hpre0⟩ := extract_withPreFdsGe3Closed hpre
    dsimp only [runSpecPlacedPreFd, withPreFdsGe3Closed, runSpecPlaced] at hpre0 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hfits, h12⟩, hmem⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hfits.mono (himp g), h12⟩, hmem⟩
  · dsimp only [runSpecPlacedPreFd, withPreFdsGe3Closed, runSpecPlaced] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hevs⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
    exact ⟨⟨himp g evs hevs.1.1, hevs.1.2⟩, hevs.2⟩

theorem subroutine_ok_runSpecAnyPlacedPreFd_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RunCall → List AllocEvent → Prop}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop}
    {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    {P : Program} {entry : BitVec 64}
    (hfit_triv : ∀ g st, FitsEnv M lim st (Env g))
    (hok : subroutine_ok P entry
      (runSpecPlacedPreFd CodeOk A lim Env uuidParse Run wrOk resStack)) :
    subroutine_ok P entry
      (runSpecAnyPlacedPreFd CodeOk A lim uuidParse Run wrOk resStack) := by
  refine subroutine_ok_mono hok (fun (g, st) R s0 hpre => ?_) (fun (g, st) R s0 sf hpost => ?_)
  · obtain ⟨hfds, hpre0⟩ := extract_withPreFdsGe3Closed hpre
    dsimp only [runSpecAnyPlaced] at hpre0
    dsimp only [runSpecPlacedPreFd, withPreFdsGe3Closed, runSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hmem⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hfit_triv g st, h12⟩, hmem⟩
  · dsimp only [runSpecPlacedPreFd, withPreFdsGe3Closed, runSpecPlaced] at hpost
    dsimp only [runSpecAnyPlacedPreFd, withPreFdsGe3Closed, runSpecAnyPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hevs⟩
    refine ⟨M.stepEvents evs st, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
    exact ⟨hevs.1.2, hevs.2⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
