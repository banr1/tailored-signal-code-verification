/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Process-to-`CliRun` Determinism and `CliSpecE` Bridge

**Checked by Lean.** Bridges whole-process `CliRunsTo` (`CliBinaryCorrect`, starting at
`cliTokenPatch s0` per `DEV-CLI10`) to the functional `CliRun` interface (`cliRunAbortOnPanic`,
`CliSpecE`).

- `processTerminatedOutcome_unique` and `outcomeObserved_unique`: a terminated state `sf` uniquely
  determines its `ProcessOutcome` and observed CLI `Outcome`.
- `cliRunsTo_unique`: combines a reachable terminated state `sf` from `cliTokenPatch s0` under `h₁`
  with `h₂`'s `ProcessRunsTo` safety invariant at `sf` without assuming global `Step` determinism.
- `cliRunSig_eq_some` and `cliSpecE_cliRunSig`: evaluate `Classical.choose` in `cliRunAbortOnPanic`
  via `cliRunsTo_unique` to establish `CliSpecE`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process

/-- A single machine state `sf` admits at most one `ProcessTerminatedOutcome`. -/
theorem processTerminatedOutcome_unique {sf : State} {out₁ out₂ : ProcessOutcome}
    (h₁ : ProcessTerminatedOutcome sf out₁) (h₂ : ProcessTerminatedOutcome sf out₂) :
    out₁ = out₂ := by
  rcases h₁ with ⟨code₁, hst₁, rfl⟩ | ⟨sig₁, hst₁, rfl⟩ <;>
    rcases h₂ with ⟨code₂, hst₂, rfl⟩ | ⟨sig₂, hst₂, rfl⟩ <;>
    rw [hst₁] at hst₂ <;> cases hst₂ <;> rfl

private theorem processTerminatedOutcome_not_running {sf : State} {out : ProcessOutcome}
    (h : ProcessTerminatedOutcome sf out) : sf.status ≠ .Running := by
  rcases h with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] <;> intro hr <;> cases hr

/-- A single `ProcessOutcome` observes at most one CLI `Outcome`. -/
theorem outcomeObserved_unique {o₁ o₂ : Outcome} {out : ProcessOutcome}
    (h₁ : OutcomeMatchesProcess o₁ out) (h₂ : OutcomeMatchesProcess o₂ out) : o₁ = o₂ := by
  cases o₁ <;> cases o₂
  · rcases h₁ with ⟨_, rfl, rfl, rfl⟩
    rcases h₂ with ⟨_, rfl, rfl, rfl⟩
    rfl
  · rcases h₁ with ⟨hs₁, _⟩
    rcases h₂ with ⟨hs₂, _⟩
    rw [hs₁] at hs₂
    cases hs₂
  · rcases h₁ with ⟨hs₁, _⟩
    rcases h₂ with ⟨hs₂, _⟩
    rw [hs₁] at hs₂
    cases hs₂
  · rfl

/-- `CliRunsTo` uniquely determines the CLI `Outcome` `o` for a given `elf`, `W`, and `i`. -/
theorem cliRunsTo_unique {elf : Arm64.Process.ElfImage} {W : CliHooks} {i : Inputs}
    {o₁ o₂ : Outcome} (h₁ : CliRunsTo elf W i o₁) (h₂ : CliRunsTo elf W i o₂) :
    o₁ = o₂ := by
  rcases h₁ with ⟨s0, hLoad₁, ⟨out₁, ⟨sf, hSteps, hTerm₁⟩, hObs₁⟩ | ⟨_, _, _, hOom₁⟩, _⟩
  · rcases h₂ with ⟨s0', hLoad₂, _, hSafe₂⟩
    rw [hLoad₁] at hLoad₂
    cases hLoad₂
    rcases hSafe₂ sf hSteps with ⟨out₂, hTerm₂, hObs₂⟩ | ⟨_, hOom⟩ | ⟨hRun, _⟩
    · cases processTerminatedOutcome_unique hTerm₁ hTerm₂
      exact outcomeObserved_unique hObs₁ hObs₂
    · exact False.elim hOom
    · exact absurd hRun (processTerminatedOutcome_not_running hTerm₁)
  · exact False.elim hOom₁

/-- Whenever `CliRunsTo elf W i o` holds, `cliRunAbortOnPanic elf W i` evaluates to `some o`. -/
theorem cliRunSig_eq_some {elf : Arm64.Process.ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (h : CliRunsTo elf W i o) : cliRunAbortOnPanic elf W i = some o := by
  unfold cliRunAbortOnPanic
  split
  · next hex => exact congrArg some (cliRunsTo_unique (Classical.choose_spec hex) h)
  · next hne => exact absurd ⟨o, h⟩ hne

/-- An ELF image satisfying `CliBinaryCorrect` implements `CliSpecE` under `cliRunAbortOnPanic elf W`
whenever `CliAllocNeverFails elf W` holds. -/
theorem cliSpecE_cliRunSig {elf : Arm64.Process.ElfImage} {W : CliHooks}
    (hBin : CliBinaryCorrect elf) (hA : CliAllocNeverFails elf W) :
    CliSpecE (cliRunAbortOnPanic elf W) W.C := by
  obtain ⟨hSend, hRecv⟩ := hBin.2 W hA
  exact ⟨fun g m hg hm =>
      (cliRunSig_eq_some (hSend g m hg hm)).trans (by split_ifs <;> rfl),
    fun g c rc hg hc =>
      (cliRunSig_eq_some (hRecv g c rc hg hc)).trans (by split_ifs <;> rfl)⟩

end CryptoVerification.SignalSession
