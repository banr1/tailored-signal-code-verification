/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Process.Core

/-!
# Uniqueness of `Placed.CliRunsToPlaced` and Deterministic `Steps` Bridge

Proves `MultiPlacement`-parametric outcome uniqueness for `Placed.CliRunsToPlaced` and bridges
terminating `Arm64.Steps` traces on `Placed.cliTokenPatchPlaced mpl s0` to
`Placed.cliRunPlacedSig mpl mmpl elf W inp = some out` without unfolding `Placed.cliProgPlacedSig`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.CliRunBridgePlaced

open Arm64 (State Steps StepsUntil)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage ProcessExitsWith ProcessOutcome ProcessRunsTo
  ProcessTerminatedOutcome)
open CryptoVerification.SignalSession (CliHooks Inputs Outcome
  OutcomeMatchesProcess cliProcessInputs)
open CryptoVerification.SignalSession.Placed (CliRunsToPlaced cliProgPlacedSig
  cliRunPlacedSig cliTokenPatchPlaced)

private theorem processTerminatedOutcome_unique {sf : State} {out₁ out₂ : ProcessOutcome}
    (h₁ : ProcessTerminatedOutcome sf out₁) (h₂ : ProcessTerminatedOutcome sf out₂) :
    out₁ = out₂ := by
  rcases h₁ with ⟨code₁, hst₁, rfl⟩ | ⟨sig₁, hst₁, rfl⟩ <;>
    rcases h₂ with ⟨code₂, hst₂, rfl⟩ | ⟨sig₂, hst₂, rfl⟩ <;>
    rw [hst₁] at hst₂ <;> cases hst₂ <;> rfl

private theorem processTerminatedOutcome_not_running {sf : State} {out : ProcessOutcome}
    (h : ProcessTerminatedOutcome sf out) : sf.status ≠ .Running := by
  rcases h with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] <;> intro hr <;> cases hr

private theorem outcomeObserved_unique {o₁ o₂ : Outcome} {out : ProcessOutcome}
    (h₁ : OutcomeMatchesProcess o₁ out) (h₂ : OutcomeMatchesProcess o₂ out) : o₁ = o₂ := by
  cases o₁ <;> cases o₂
  · rcases h₁ with ⟨_, rfl, rfl, rfl⟩; rcases h₂ with ⟨_, rfl, rfl, rfl⟩; rfl
  · rcases h₁ with ⟨hs₁, _⟩; rcases h₂ with ⟨hs₂, _⟩; rw [hs₁] at hs₂; cases hs₂
  · rcases h₁ with ⟨hs₁, _⟩; rcases h₂ with ⟨hs₂, _⟩; rw [hs₁] at hs₂; cases hs₂
  · rfl

/-- `CliRunsToPlaced` uniquely determines the CLI `Outcome` for given `mpl`, `mmpl`, `elf`, `W`,
and `inp`. -/
theorem cliRunsToPlaced_unique {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {inp : Inputs} {o₁ o₂ : Outcome}
    (h₁ : CliRunsToPlaced mpl mmpl elf W inp o₁)
    (h₂ : CliRunsToPlaced mpl mmpl elf W inp o₂) : o₁ = o₂ := by
  rcases h₁ with ⟨s0, hLoad₁, ⟨out₁, ⟨sf, hSteps, hTerm₁⟩, hObs₁⟩ | ⟨_, _, _, hOom₁⟩, _⟩
  · rcases h₂ with ⟨_, hLoad₂, _, hSafe₂⟩
    rw [hLoad₁] at hLoad₂; cases hLoad₂
    rcases hSafe₂ sf hSteps with ⟨out₂, hTerm₂, hObs₂⟩ | ⟨_, hOom⟩ | ⟨hRun, _⟩
    · cases processTerminatedOutcome_unique hTerm₁ hTerm₂
      exact outcomeObserved_unique hObs₁ hObs₂
    · exact False.elim hOom
    · exact absurd hRun (processTerminatedOutcome_not_running hTerm₁)
  · exact False.elim hOom₁

theorem cliRunPlacedSig_eq_some {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {inp : Inputs} {o : Outcome}
    (h : CliRunsToPlaced mpl mmpl elf W inp o) :
    cliRunPlacedSig mpl mmpl elf W inp = some o := by
  unfold cliRunPlacedSig
  split
  · next hex => exact congrArg some (cliRunsToPlaced_unique (Classical.choose_spec hex) h)
  · next hne => exact absurd ⟨o, h⟩ hne

/-- Bridges a terminating `Arm64.Steps` trace on `cliTokenPatchPlaced mpl s0` to
`cliRunPlacedSig mpl mmpl elf W inp = some out`. -/
theorem cliRunPlacedSig_eq_some_of_terminated
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {out : Outcome} {s0 sf : State} {pout : ProcessOutcome}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) sf)
    (hterm : ProcessTerminatedOutcome sf pout)
    (hout : OutcomeMatchesProcess out pout) :
    cliRunPlacedSig mpl mmpl elf W inp = some out := by
  have hexit : ProcessExitsWith (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) pout :=
    ⟨sf, hsteps, hterm⟩
  exact cliRunPlacedSig_eq_some ⟨s0, hload, ProcessRunsTo.of_exitsWith hexit hout⟩

theorem cliRunPlacedSig_eq_some_of_steps
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {out : Outcome} {s0 sf : State} {code : BitVec 64}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) sf)
    (hst : sf.status = .Exited code)
    (hout : OutcomeMatchesProcess out (ProcessOutcome.ofState code sf)) :
    cliRunPlacedSig mpl mmpl elf W inp = some out :=
  cliRunPlacedSig_eq_some_of_terminated hload hsteps (Or.inl ⟨code, hst, rfl⟩) hout

theorem cliRunPlacedSig_eq_some_of_signaled
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {out : Outcome} {s0 sf : State} {sig : BitVec 7}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) sf)
    (hst : sf.status = .Signaled sig)
    (hout : OutcomeMatchesProcess out (ProcessOutcome.ofSignal sig sf)) :
    cliRunPlacedSig mpl mmpl elf W inp = some out :=
  cliRunPlacedSig_eq_some_of_terminated hload hsteps (Or.inr ⟨sig, hst, rfl⟩) hout

theorem cliRunPlacedSig_eq_some_of_stepsUntil
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {out : Outcome} {stop : State → Prop} {s0 sf : State} {pout : ProcessOutcome}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : StepsUntil (cliProgPlacedSig mpl mmpl W) stop (cliTokenPatchPlaced mpl s0) sf)
    (hterm : ProcessTerminatedOutcome sf pout)
    (hout : OutcomeMatchesProcess out pout) :
    cliRunPlacedSig mpl mmpl elf W inp = some out :=
  cliRunPlacedSig_eq_some_of_terminated hload hsteps.toSteps hterm hout

end Symbolic.BugInjection.Proofs.CliExec.CliRunBridgePlaced
