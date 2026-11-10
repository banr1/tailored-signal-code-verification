/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed
public import ProofLib.Process.Core

/-!
# Uniqueness of `CliRunsTo` and Deterministic `Steps` Bridge

Proves outcome uniqueness for `CliRunsTo elf W inp` and bridges terminating `Arm64.Steps` traces on
`cliTokenPatch s0` to `cliRunAbortOnPanic elf W inp = some out`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.CliRunBridge

open Arm64 (State Steps)
open Arm64.Process (ElfImage ProcessExitsWith ProcessOutcome ProcessRunsTo
  ProcessTerminatedOutcome)
open CryptoVerification.SignalSession (CliHooks CliRunsTo Inputs Outcome
  OutcomeMatchesProcess cliProcessInputs cliProgAbortOnPanic cliRunAbortOnPanic
  cliTokenPatch)

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

/-- `CliRunsTo` uniquely determines the CLI `Outcome` for a given `elf`, `W`, and `inp`. -/
theorem cliRunsTo_unique {elf : ElfImage} {W : CliHooks} {inp : Inputs} {o₁ o₂ : Outcome}
    (h₁ : CliRunsTo elf W inp o₁) (h₂ : CliRunsTo elf W inp o₂) : o₁ = o₂ := by
  rcases h₁ with ⟨s0, hLoad₁, ⟨out₁, ⟨sf, hSteps, hTerm₁⟩, hObs₁⟩ | ⟨_, _, _, hOom₁⟩, _⟩
  · rcases h₂ with ⟨_, hLoad₂, _, hSafe₂⟩
    rw [hLoad₁] at hLoad₂; cases hLoad₂
    rcases hSafe₂ sf hSteps with ⟨out₂, hTerm₂, hObs₂⟩ | ⟨_, hOom⟩ | ⟨hRun, _⟩
    · cases processTerminatedOutcome_unique hTerm₁ hTerm₂
      exact outcomeObserved_unique hObs₁ hObs₂
    · exact False.elim hOom
    · exact absurd hRun (processTerminatedOutcome_not_running hTerm₁)
  · exact False.elim hOom₁

private theorem cliRunSig_eq_some {elf : ElfImage} {W : CliHooks} {inp : Inputs} {o : Outcome}
    (h : CliRunsTo elf W inp o) : cliRunAbortOnPanic elf W inp = some o := by
  unfold cliRunAbortOnPanic
  split
  · next hex => exact congrArg some (cliRunsTo_unique (Classical.choose_spec hex) h)
  · next hne => exact absurd ⟨o, h⟩ hne

/-- Bridges a terminating `Arm64.Steps` trace on `cliTokenPatch s0` to
`cliRunAbortOnPanic elf W inp = some out`. -/
theorem cliRunAbortOnPanic_eq_some_of_terminated
    {elf : ElfImage} {W : CliHooks} {inp : Inputs} {out : Outcome}
    {s0 sf : State} {pout : ProcessOutcome}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) sf)
    (hterm : ProcessTerminatedOutcome sf pout)
    (hout : OutcomeMatchesProcess out pout) :
    cliRunAbortOnPanic elf W inp = some out := by
  have hexit : ProcessExitsWith (cliProgAbortOnPanic W) (cliTokenPatch s0) pout :=
    ⟨sf, hsteps, hterm⟩
  exact cliRunSig_eq_some ⟨s0, hload, ProcessRunsTo.of_exitsWith hexit hout⟩

theorem cliRunAbortOnPanic_eq_some_of_steps
    {elf : ElfImage} {W : CliHooks} {inp : Inputs} {out : Outcome}
    {s0 sf : State} {code : BitVec 64}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) sf)
    (hst : sf.status = .Exited code)
    (hout : OutcomeMatchesProcess out (ProcessOutcome.ofState code sf)) :
    cliRunAbortOnPanic elf W inp = some out :=
  cliRunAbortOnPanic_eq_some_of_terminated hload hsteps (Or.inl ⟨code, hst, rfl⟩) hout

theorem cliRunAbortOnPanic_eq_some_of_signaled
    {elf : ElfImage} {W : CliHooks} {inp : Inputs} {out : Outcome}
    {s0 sf : State} {sig : BitVec 7}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hsteps : Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) sf)
    (hst : sf.status = .Signaled sig)
    (hout : OutcomeMatchesProcess out (ProcessOutcome.ofSignal sig sf)) :
    cliRunAbortOnPanic elf W inp = some out :=
  cliRunAbortOnPanic_eq_some_of_terminated hload hsteps (Or.inr ⟨sig, hst, rfl⟩) hout

end Symbolic.BugInjection.Proofs.CliExec.CliRunBridge
