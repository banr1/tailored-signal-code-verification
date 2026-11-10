/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Arm `J` Specification

Defines the budget-threaded postcondition `runJoinPostPlaced` (over `FreeOnlyEvs`) and hop contract
`RunHopJoinPlaced` on Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliWrOk inputOf runResAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtJoinPlaced AtRejectPlaced RunHistOk RunNeeds RunSem joinMem rejectMem runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (runPostAnyPlaced runPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

/-- Budget-threaded postcondition of Arm `J` (`FreeOnlyEvs`, advancing `A.pool lim st` to `A.pool lim (M.stepEvents evs st)`). -/
def runJoinPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : RunCall) (st : M.σ) (resStack : Nat) (s0 sf : State) (Pf : SepProp) : Prop :=
  CodeOk sf.mem ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    s0.trace <+: sf.trace ∧ RunHistOk g.i s0 sf ∧
    ∃ (evs : List AllocEvent) (a' : RunAnswer),
      FreeOnlyEvs evs ∧ a' ≠ none ∧ a' = g.a ∧
      (Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack ∗
        runResAt A.repAlloc cliWrOk g.res a' ∗ anyHeap)

theorem runPostAnyPlaced_of_joinPost [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {s0 sf : State} {Pf : SepProp}
    (hp : runJoinPostPlaced CodeOk A lim g st resStack s0 sf Pf) :
    runPostAnyPlaced CodeOk A lim g resStack s0 sf Pf := by
  rcases hp with ⟨hc, hsp, hcs, htr, hst, evs, a', _hevs, hne, heq, hent⟩
  exact ⟨hc, hsp, hcs, htr, hst, M.stepEvents evs st, a', hne, heq, hent⟩

/-- Lifts `runJoinPostPlaced` to `runPostPlaced` for any envelope `RunEnv` closed under trailing `FreeOnlyEvs`. -/
theorem runPostPlaced_of_joinPost [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st₀ st : M.σ} {evs₁ : List AllocEvent}
    {resStack : Nat} {s0 sf : State} {Pf : SepProp}
    (hst : st = M.stepEvents evs₁ st₀)
    (hEnv : ∀ evs₂, FreeOnlyEvs evs₂ → RunEnv g (evs₁ ++ evs₂))
    (hp : runJoinPostPlaced CodeOk A lim g st resStack s0 sf Pf) :
    runPostPlaced CodeOk A lim RunEnv g st₀ resStack s0 sf Pf := by
  rcases hp with ⟨hc, hsp, hcs, htr, hstP, evs₂, a', hevs₂, hne, heq, hent⟩
  subst hst
  rw [← M.stepEvents_append evs₁ evs₂ st₀] at hent
  exact ⟨hc, hsp, hcs, htr, hstP, evs₁ ++ evs₂, a', hEnv evs₂ hevs₂, hne, heq, hent⟩

/-- Budget-threaded relocatable Arm `J` contract from `AtJoinPlaced` or `AtRejectPlaced` to `runJoinPostPlaced` with `Qo = ⌜False⌝`. -/
def RunHopJoinPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (sEnvs : RunSlotEnvs) (H : LibsignalHooks) (B : RunBudgets) (S : RunSem)
    (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    LsRetAddr624 (s0.readReg64 .lr) →
    ((∃ g' out, AtJoinPlaced CodeOk g g' out s0 s ∧
        P = joinMem (A.atState lim st s) g g' out s0 resStack) ∨
      (∃ g' rk, AtRejectPlaced CodeOk g g' rk s0 s ∧
        P = rejectMem (A.atState lim st s) g g' rk s0 resStack)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P
      (runJoinPostPlaced CodeOk A lim g st resStack s0)
      Qp
      (fun _ => ⌜False⌝)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
