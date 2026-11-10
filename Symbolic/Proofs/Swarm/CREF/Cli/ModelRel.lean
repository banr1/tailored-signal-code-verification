/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# CLI Model Relation Inversion Lemmas

Inversion and constructor lemmas for `PqModelRel`, `pqxdhExpectedOutcome`, and
`OutcomeMatchesModelExceptPath`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (PqParty pqxdhExpectedOutcome Inputs Outcome filesOf OutcomeMatchesModelExceptPath)

theorem PqModelRel.of_post {interp : ExternInterpretation} {P : PEParams} {i : Inputs}
    {o : Outcome} (h : PqModelPost interp P i o) :
    PqModelRel interp P i (some o) :=
  Or.inr ⟨o, rfl, h⟩

@[simp]
theorem PqModelRel.exited_iff {interp : ExternInterpretation} {P : PEParams} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot} :
    PqModelRel interp P i (some (.exited code out files)) ↔
      PqModelPost interp P i (.exited code out files) := by
  constructor
  · rintro (h | ⟨o', ho, hp⟩)
    · cases h
    · injection ho with ho'; exact ho' ▸ hp
  · exact PqModelRel.of_post

end DY.Libsignal.Composed.Refinement.Cli

namespace Symbolic.Swarm.CREF.Cli

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E
open CryptoVerification.SignalSession

theorem exited_eq_pqObserve_iff {P : PEParams} {i₀ : Inputs}
    {res : Option (Option (PqParty × HwBytes))} {code : Nat} {out : HwBytes} {files : DirectorySnapshot} :
    Outcome.exited code out files = pqxdhExpectedOutcome P i₀ res ↔
      (res = some none ∧ code = 1 ∧ out = [] ∧ files = filesOf i₀.files) ∨
      (∃ st' out', res = some (some (st', out')) ∧
        code = 0 ∧ out = out' ∧ files = filesOf (i₀.files ++ encodeDir P st')) := by
  rcases res with _ | (_ | ⟨st', out'⟩)
  · simp [pqxdhExpectedOutcome, observe]
  · simp only [pqxdhExpectedOutcome, Option.map_some, Option.map_none, observe, Outcome.exited.injEq,
      Option.some.injEq, reduceCtorEq, false_and, exists_false, or_false, true_and]
  · simp only [pqxdhExpectedOutcome, Option.map_some, observe, Outcome.exited.injEq,
      Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, false_or]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨st', out, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    · rintro ⟨st₁, out₁, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩

theorem observedExcept_exited_iff {P : PEParams} {i₀ : Inputs} {path : String}
    {res : Option (Option (PqParty × HwBytes))} {code : Nat} {out : HwBytes} {files : DirectorySnapshot} :
    OutcomeMatchesModelExceptPath P i₀ path res (.exited code out files) ↔
      (res = some none ∧ code = 1 ∧ out = [] ∧ files = filesOf i₀.files) ∨
      (∃ st' out', res = some (some (st', out')) ∧
        code = 0 ∧ out = out' ∧
        ∀ q, Arm64.normalizePath q ≠ Arm64.normalizePath path →
          files q = filesOf (i₀.files ++ encodeDir P st') q) := by
  rcases res with _ | (_ | ⟨st', out'⟩)
  · simp [OutcomeMatchesModelExceptPath, pqxdhExpectedOutcome, observe]
  · simp [OutcomeMatchesModelExceptPath, pqxdhExpectedOutcome, observe]
  · simp only [OutcomeMatchesModelExceptPath, pqxdhExpectedOutcome, Option.map_some, observe, Outcome.AgreeExcept,
      Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, false_or]
    constructor
    · rintro ⟨rfl, rfl, hag⟩; exact ⟨st', out, ⟨rfl, rfl⟩, rfl, rfl, hag⟩
    · rintro ⟨st₁, out₁, ⟨rfl, rfl⟩, rfl, rfl, hag⟩; exact ⟨rfl, rfl, hag⟩

end Symbolic.Swarm.CREF.Cli
