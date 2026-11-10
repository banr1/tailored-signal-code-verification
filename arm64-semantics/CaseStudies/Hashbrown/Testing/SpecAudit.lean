/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SpecAudit
public import CaseStudies.Hashbrown.Spec
public import CaseStudies.Hashbrown.SpecExamples

/-!
# Specification Audit & Non-Vacuity for `CaseStudies.Hashbrown.Spec` (`CaseStudies.Hashbrown.Testing.SpecAudit`)

- **Layer / Role**: Per-campaign SpecAudit & non-vacuity module (`Role::Test`, `0 sorry`) for the
  whole-binary CLI specification (`CaseStudies/Hashbrown/Spec/Top.lean`).
- **Purpose & Key Exports**:
  1. Non-vacuity of the input bound `stdin.length ≤ HashbrownCliMaxStdin` (`hashbrownCli_input_nonvacuous`).
  2. Totality and output determinism of `HashbrownCliPost` (`hashbrownCliPost_exists`,
     `hashbrownCliPost_deterministic`, `hashbrownCliPost_no_signal`).
  3. Non-degeneracy across normal execution (`exitCode = 0`), malformed command reporting on
     `stderr` (`exitCode = 0`), and overlong-line whole-run rejection (`exitCode = 1`).
  4. Algebraic finite-map laws for the pure CLI reference model `CliMap`
     (`cliMapLookup_empty`, `cliMapLookup_insert_eq`, `cliMapLookup_insert_ne`,
      `cliMapLookup_erase_eq`, `cliMapLookup_erase_ne`).
-/

@[expose] public section

namespace Testing.HashbrownSpecAudit

open Arm64 Arm64.Process CaseStudies.Hashbrown CaseStudies.Hashbrown.SpecExamples

/-! ## 1. Premise Non-Vacuity & Outcome Totality / Determinism -/

/-- The top-level input-length premise `stdin.length ≤ HashbrownCliMaxStdin` is satisfiable on both
    empty and non-empty `stdin` streams. -/
theorem hashbrownCli_input_nonvacuous :
    ([] : List (BitVec 8)).length ≤ HashbrownCliMaxStdin ∧
    (bytesOfString "insert 3 7\nget 3\n").length ≤ HashbrownCliMaxStdin := by
  decide

/-- Joint non-vacuity witness for the universal `HashbrownCliUniversalStmt` premises. -/
theorem hashbrownCli_premises_nonvacuous : ∃ (inputs : ProcessInputs),
    inputs.Valid ∧ HashbrownStdinBudget inputs :=
  ⟨{ init := { physMemAvail := 8 * 2 ^ 20 } }, by decide +kernel, by decide +kernel⟩

example : ∃ inputs : ProcessInputs, inputs.Valid ∧ HashbrownStdinBudget inputs :=
  hashbrownCli_premises_nonvacuous

/-- For every `stdin`, there exists a `ProcessOutcome` satisfying `HashbrownCliPost stdin`. -/
theorem hashbrownCliPost_exists (stdin : List (BitVec 8)) :
    ∃ out : ProcessOutcome, HashbrownCliPost stdin out := by
  unfold HashbrownCliPost
  by_cases h : (splitLines stdin).any (·.length > MaxLineLen)
  · refine ⟨{ exitCode := 1#64, signal := none, stdout := [],
              stderr := bytesOfString "error: line too long\n", fs := default }, ?_⟩
    simp [h]
  · refine ⟨{ exitCode := 0#64, signal := none, stdout := (evalLines (splitLines stdin)).1,
              stderr := (evalLines (splitLines stdin)).2, fs := default }, ?_⟩
    simp [h]

/-- `HashbrownCliPost stdin` uniquely determines `(exitCode, signal, stdout, stderr)`. -/
theorem hashbrownCliPost_deterministic (stdin : List (BitVec 8))
    (out₁ out₂ : ProcessOutcome)
    (h₁ : HashbrownCliPost stdin out₁) (h₂ : HashbrownCliPost stdin out₂) :
    out₁.exitCode = out₂.exitCode ∧
    out₁.signal = out₂.signal ∧
    out₁.stdout = out₂.stdout ∧
    out₁.stderr = out₂.stderr := by
  unfold HashbrownCliPost at h₁ h₂
  by_cases h : (splitLines stdin).any (·.length > MaxLineLen)
  · simp only [h, ↓reduceIte] at h₁ h₂
    exact ⟨h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm,
           h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.trans h₂.2.2.2.symm⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
    exact ⟨h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm,
           h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.trans h₂.2.2.2.symm⟩

/-- No outcome that terminates by signal (`out.signal = some sig`) can satisfy `HashbrownCliPost`. -/
theorem hashbrownCliPost_no_signal (stdin : List (BitVec 8)) (out : ProcessOutcome) (sig : Nat)
    (hsig : out.signal = some sig) :
    ¬ HashbrownCliPost stdin out := by
  unfold HashbrownCliPost
  by_cases h : (splitLines stdin).any (·.length > MaxLineLen)
  · simp [h, hsig]
  · simp [h, hsig]

/-! ## 2. Algebraic Finite-Map Laws for `CliMap` (`cliMapLookup`, `cliMapInsert`, `cliMapErase`) -/

@[simp] theorem cliMapLookup_empty (k : BitVec 64) :
    cliMapLookup k [] = none := rfl

@[simp] theorem cliMapLookup_insert_eq (m : CliMap) (k v : BitVec 64) :
    cliMapLookup k (cliMapInsert k v m) = some v := by
  simp [cliMapInsert, cliMapLookup]

@[simp] theorem cliMapLookup_erase_eq (m : CliMap) (k : BitVec 64) :
    cliMapLookup k (cliMapErase k m) = none := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k' = k
    · subst h; simp [cliMapErase, ih]
    · simp [cliMapErase, cliMapLookup, h, ih]

@[simp] theorem cliMapLookup_erase_ne (m : CliMap) (k k' : BitVec 64) (hne : k' ≠ k) :
    cliMapLookup k' (cliMapErase k m) = cliMapLookup k' m := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k₀, v₀⟩ := p
    by_cases h : k₀ = k
    · subst h
      have hne' : k₀ ≠ k' := Ne.symm hne
      simp [cliMapErase, cliMapLookup, hne', ih]
    · simp only [cliMapErase, beq_iff_eq, h, ↓reduceIte, cliMapLookup]
      by_cases h0 : k₀ = k'
      · simp [h0]
      · simp [h0, ih]

@[simp] theorem cliMapLookup_insert_ne (m : CliMap) (k k' v : BitVec 64) (hne : k' ≠ k) :
    cliMapLookup k' (cliMapInsert k v m) = cliMapLookup k' m := by
  have hne' : k ≠ k' := Ne.symm hne
  simp [cliMapInsert, cliMapLookup, hne', cliMapLookup_erase_ne m k k' hne]

end Testing.HashbrownSpecAudit
