/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Strict Placed Correctness Recovery from Up-to-OOM Specifications

Converts the up-to-allocation-failure (`DEV-CLI15`) placed correctness predicates
(`CliSpecPqxdhOrExcusedAbort`, `CliPqxdhElfCorrectPlaced`, `CliPqxdhBinaryCorrectPlaced`) into
strict (`0`-excused-abort) counterparts (`CliSpecPqxdh`, `CliPqxdhElfCorrectStrictPlaced`,
`CliPqxdhBinaryCorrectStrictPlaced`) once `CliReachesOOMPlaced` is refuted across `CliPqxdhInputs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhBinaryCorrectPlaced
   CliPqxdhBinaryCorrectPlacedAt CliPqxdhElfCorrectPlaced CliPqxdhInputs CliReachesOOMPlaced CliRun
   CliSpecPqxdh CliSpecPqxdhNoMatch CliSpecPqxdhNoMatchOrExcusedAbort
   CliSpecPqxdhOrExcusedAbort Inputs Outcome OutcomeOrExcusedAbort cliProcessInputs
   libsignalSessionLib)
open CryptoVerification.SignalSession.Placed
  (CliElfCodeMatchesPlaced cliProgPlacedSig cliRunPlacedSig cliTokenPatchPlaced)

/-- Predicate asserting that `cliProgPlacedSig mpl mmpl W` logs `allocFailedEvent` on input `i`
from `cliTokenPatchPlaced mpl s0`. -/
def CliRunAllocFailsPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks)
    (i : Inputs) : Prop :=
  ∃ s0 s : State,
    elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) s ∧
    allocFailedEvent ∈ s.trace

/-- Invariant asserting that `cliProgPlacedSig mpl mmpl W` never logs `allocFailedEvent` across
`CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
def CliPqxdhAllocNeverFailsPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : Prop :=
  ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
    ∀ s0 s : State,
      elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) s →
      allocFailedEvent ∉ s.trace

/-! ## Strict placed ELF and binary correctness predicates -/

/-- Strict relocatable `CliPqxdhElfCorrect` under multi-block placements `(mpl, mmpl)` with no
`OrExcusedAbort` relaxation: `elf` matches `libsignalSessionLib` + `mallocngLib` under `(mpl, mmpl)`
and for every `W` and `X`, `cliRunPlacedSig mpl mmpl elf W` satisfies `CliSpecPqxdh` and
`CliSpecPqxdhNoMatch` directly. -/
def CliPqxdhElfCorrectStrictPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Strict relocatable `CliPqxdhBinaryCorrect` at fixed placements `(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectStrictPlacedAt (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectStrictPlaced mpl mmpl elf

/-- Strict relocatable `CliPqxdhBinaryCorrect` universally quantified over every placement pair
`(mpl, mmpl)` linked at `bytes`. -/
def CliPqxdhBinaryCorrectStrictPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectStrictPlacedAt mpl mmpl bytes

/-! ## Eliminating `CliRunAllocFailsPlaced` and `OutcomeOrExcusedAbort` -/

theorem not_cliRunAllocFailsPlaced_of_allocNeverFails
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (hNever : CliPqxdhAllocNeverFailsPlaced mpl mmpl elf W)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliRunAllocFailsPlaced mpl mmpl elf W i := by
  rintro ⟨s0, s, hload, hsteps, hmem⟩
  exact hNever i hi s0 s hload hsteps hmem

theorem outcomeOrExcusedAbort_of_not_exc
    {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {P : Outcome → Prop}
    (h : OutcomeOrExcusedAbort exc run i P) (hne : ¬ exc i) :
    ∃ o, run i = some o ∧ P o := by
  rcases h with ho | ⟨_, hexc⟩
  · exact ho
  · exact (hne hexc).elim

theorem outcomeOrExcusedAbort_eq_of_not_exc
    {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {expected : Outcome}
    (h : OutcomeOrExcusedAbort exc run i (· = expected)) (hne : ¬ exc i) :
    run i = some expected := by
  obtain ⟨o, hrun, rfl⟩ := outcomeOrExcusedAbort_of_not_exc h hne
  exact hrun

theorem outcomeOrExcusedAbort_of_eq
    {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {expected : Outcome}
    (h : run i = some expected) :
    OutcomeOrExcusedAbort exc run i (· = expected) :=
  Or.inl ⟨expected, h, rfl⟩

private theorem some_ite {α : Type} {c : Prop} [Decidable c] {a b : α} :
    some (if c then a else b) = (if c then some a else some b) := by
  by_cases hc : c <;> simp only [hc, ↓reduceIte]

private theorem some_ite2 {α : Type} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    {a b d : α} :
    some (if c₁ then a else if c₂ then b else d) =
      (if c₁ then some a else if c₂ then some b else some d) := by
  by_cases hc₁ : c₁
  · simp only [hc₁, ↓reduceIte]
  · simp only [hc₁, ↓reduceIte]
    exact some_ite

private theorem exists_some_ite_eq {α : Type} {x : Option α} {c : Prop} [Decidable c]
    {a : α} {P : α → Prop}
    (h : ∃ o, x = some o ∧ (if c then o = a else P o)) :
    if c then x = some a else ∃ o, x = some o ∧ P o := by
  obtain ⟨o, hx, hP⟩ := h
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at hP ⊢
    exact hx.trans (congrArg some hP)
  · simp only [hc, ↓reduceIte] at hP ⊢
    exact ⟨o, hx, hP⟩

private theorem exists_some_ite_eq_inv {α : Type} {x : Option α} {c : Prop} [Decidable c]
    {a : α} {P : α → Prop}
    (h : if c then x = some a else ∃ o, x = some o ∧ P o) :
    ∃ o, x = some o ∧ (if c then o = a else P o) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h
    exact ⟨a, h, by simp only [hc, ↓reduceIte]⟩
  · simp only [hc, ↓reduceIte] at h
    obtain ⟨o, hx, hP⟩ := h
    exact ⟨o, hx, by simp only [hc, ↓reduceIte]; exact hP⟩

/-! ## Specification-level recovery -/

theorem cliSpecPqxdh_of_orExcusedAbort
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hOr : CliSpecPqxdhOrExcusedAbort exc run X W)
    (hNoExc : ∀ i : Inputs, CliPqxdhInputs W i → ¬ exc i) :
    CliSpecPqxdh run X W := by
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5⟩ := hOr st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact outcomeOrExcusedAbort_eq_of_not_exc (h1 b t hnone)
      (hNoExc _ ⟨st, hst, Or.inl ⟨hnone, b, t, rfl⟩⟩)
  · intro m r hm
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h2 m r hm)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩)).trans some_ite2
  · intro c rc hc
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h3 c rc hc)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩)).trans some_ite
  · intro m rc hm hmatch
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h4 m rc hm hmatch)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)).trans some_ite
  · intro c rc hc h2ne h3ne
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h5 c rc hc h2ne h3ne)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2ne, h3ne, rfl⟩)))⟩)).trans some_ite

theorem cliSpecPqxdhNoMatch_of_orExcusedAbort
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hOr : CliSpecPqxdhNoMatchOrExcusedAbort exc run X W)
    (hNoExc : ∀ i : Inputs, CliPqxdhInputs W i → ¬ exc i) :
    CliSpecPqxdhNoMatch run X W := by
  intro st hst x g hsess m rc hm hnm
  refine exists_some_ite_eq ?_
  exact outcomeOrExcusedAbort_of_not_exc (hOr st hst x g hsess m rc hm hnm)
    (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)

/-! ## Whole-ELF and binary recovery -/

theorem cliSpecPqxdh_and_noMatch_of_elfCorrectPlaced
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (hElf : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOom : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i)
    (X : UnreachedPqxdhPrimitives) :
    CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ := by
  obtain ⟨hOr5, hOrNm⟩ := hElf.2 W X
  exact ⟨cliSpecPqxdh_of_orExcusedAbort hOr5 hNoOom,
    cliSpecPqxdhNoMatch_of_orExcusedAbort hOrNm hNoOom⟩

/-- Derive `CliPqxdhElfCorrectStrictPlaced` from `CliPqxdhElfCorrectPlaced` and
`¬ CliReachesOOMPlaced`. -/
theorem cliPqxdhElfCorrectStrictPlaced_of_upToAllocFailure
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hElf : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOom : ∀ (W : CliHooks) (i : Inputs),
      CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced mpl mmpl elf :=
  ⟨hElf.1, fun W X => cliSpecPqxdh_and_noMatch_of_elfCorrectPlaced hElf (hNoOom W) X⟩

theorem cliPqxdhBinaryCorrectStrictPlacedAt_of_upToAllocFailure
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (hBin : CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes)
    (hNoOom : ∀ (elf : ElfImage) (W : CliHooks),
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectStrictPlacedAt mpl mmpl bytes := by
  obtain ⟨elf, hparse, hElf⟩ := hBin
  exact ⟨elf, hparse,
    cliPqxdhElfCorrectStrictPlaced_of_upToAllocFailure hElf
      (fun W => hNoOom elf W hparse hElf.1)⟩

/-- Derive `CliPqxdhBinaryCorrectStrictPlaced` from `CliPqxdhBinaryCorrectPlaced` and
`¬ CliReachesOOMPlaced` across all linked placements. -/
theorem cliPqxdhBinaryCorrectStrictPlaced_of_upToAllocFailure
    {bytes : List (BitVec 8)}
    (hBin : CliPqxdhBinaryCorrectPlaced bytes)
    (hNoOom : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks),
      libsignalSessionLib.LinkedAt bytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectStrictPlaced bytes :=
  fun mpl mmpl hLink hMLink =>
    cliPqxdhBinaryCorrectStrictPlacedAt_of_upToAllocFailure (hBin mpl mmpl hLink hMLink)
      (fun elf W hparse hCode => hNoOom mpl mmpl elf W hLink hMLink hparse hCode)

/-! ## Converse weakening -/

theorem cliSpecPqxdhOrExcusedAbort_of_strict
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (h : CliSpecPqxdh run X W) :
    CliSpecPqxdhOrExcusedAbort exc run X W := by
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5⟩ := h st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun b t hnone => outcomeOrExcusedAbort_of_eq (h1 b t hnone)
  · exact fun m r hm => outcomeOrExcusedAbort_of_eq ((h2 m r hm).trans some_ite2.symm)
  · exact fun c rc hc => outcomeOrExcusedAbort_of_eq ((h3 c rc hc).trans some_ite.symm)
  · exact fun m rc hm hmatch => outcomeOrExcusedAbort_of_eq ((h4 m rc hm hmatch).trans some_ite.symm)
  · exact fun c rc hc h2ne h3ne =>
      outcomeOrExcusedAbort_of_eq ((h5 c rc hc h2ne h3ne).trans some_ite.symm)

theorem cliSpecPqxdhNoMatchOrExcusedAbort_of_strict
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (h : CliSpecPqxdhNoMatch run X W) :
    CliSpecPqxdhNoMatchOrExcusedAbort exc run X W :=
  fun st hst x g hsess m rc hm hnm =>
    Or.inl (exists_some_ite_eq_inv (h st hst x g hsess m rc hm hnm))

theorem cliPqxdhElfCorrectPlaced_of_strict
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectStrictPlaced mpl mmpl elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  ⟨h.1, fun W X =>
    ⟨cliSpecPqxdhOrExcusedAbort_of_strict (h.2 W X).1,
     cliSpecPqxdhNoMatchOrExcusedAbort_of_strict (h.2 W X).2⟩⟩

theorem cliPqxdhBinaryCorrectPlacedAt_of_strict
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlacedAt mpl mmpl bytes) :
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes := by
  obtain ⟨elf, hparse, hStrict⟩ := h
  exact ⟨elf, hparse, cliPqxdhElfCorrectPlaced_of_strict hStrict⟩

theorem cliPqxdhBinaryCorrectPlaced_of_strict
    {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlaced bytes) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  fun mpl mmpl hLink hMLink => cliPqxdhBinaryCorrectPlacedAt_of_strict (h mpl mmpl hLink hMLink)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.PlacedOomRecovery
