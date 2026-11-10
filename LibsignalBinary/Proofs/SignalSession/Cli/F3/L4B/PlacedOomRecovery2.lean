/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Two-Placement Shape-H ↔ Strict Recovery Corollaries

Two-placement `(mpl, mmpl)` strict ELF and binary correctness predicates
(`CliPqxdhElfCorrectStrictPlaced2`, `CliPqxdhBinaryCorrectStrictPlacedAt2`,
`CliPqxdhBinaryCorrectStrictPlaced2`) alongside weakening and `¬ CliReachesOOMPlaced` recovery
corollaries for the placed Shape-H ("total except `.OutOfMemory`", `DEV-CLI15`) predicates of
`CliBinaryPq`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhBinaryCorrectPlaced CliPqxdhBinaryCorrectPlacedAt CliPqxdhElfCorrectPlaced
   CliPqxdhInputs CliReachesOOMPlaced CliRun CliSpecPqxdh CliSpecPqxdhNoMatch
   CliSpecPqxdhNoMatchOrExcusedAbort CliSpecPqxdhOrExcusedAbort Inputs Outcome
   OutcomeOrExcusedAbort libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced cliRunPlacedSig)
open VerifiedLibraries (mallocngLib)

/-! ## Strict Two-Placement ELF and Binary Correctness Predicates -/

/-- Strict relocatable `CliPqxdhElfCorrect` under `libsignalSessionLib` placement `mpl` and
`VerifiedLibraries.mallocngLib` placement `mmpl` with no `OrExcusedAbort` relaxation: `elf` matches
`libsignalSessionLib` and `mallocngLib` under `(mpl, mmpl)` (`CliElfCodeMatchesPlaced`) and
for every `W` and `X`, `cliRunPlacedSig mpl mmpl elf W` satisfies `CliSpecPqxdh` and
`CliSpecPqxdhNoMatch` directly. -/
def CliPqxdhElfCorrectStrictPlaced2 (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Strict relocatable `CliPqxdhBinaryCorrect` at fixed placements `(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectStrictPlacedAt2 (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf

/-- Strict relocatable `CliPqxdhBinaryCorrect` universally quantified over every pair of placements
`mpl` linked at `bytes` (`libsignalSessionLib.LinkedAt bytes mpl`) and `mmpl` linked at `bytes`
(`VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl`). -/
def CliPqxdhBinaryCorrectStrictPlaced2 (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectStrictPlacedAt2 mpl mmpl bytes

/-! ## `OutcomeOrExcusedAbort` Elimination and Introduction Helpers -/

/-- Eliminate the excused-abort disjunct of `OutcomeOrExcusedAbort` when `¬ exc i`. -/
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

/-- Lift a concrete outcome witness `run i = some expected` into `OutcomeOrExcusedAbort`. -/
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

/-! ## Strict ⇒ Shape-H (`OrExcusedAbort`) Weakening -/

/-- Strict `CliSpecPqxdh` implies `CliSpecPqxdhOrExcusedAbort` for any `exc`. -/
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

theorem cliPqxdhElfCorrectPlaced_of_strict2
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  ⟨h.1, fun W X =>
    ⟨cliSpecPqxdhOrExcusedAbort_of_strict (h.2 W X).1,
     cliSpecPqxdhNoMatchOrExcusedAbort_of_strict (h.2 W X).2⟩⟩

theorem cliPqxdhBinaryCorrectPlacedAt_of_strict2
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlacedAt2 mpl mmpl bytes) :
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes := by
  obtain ⟨elf, hparse, hStrict⟩ := h
  exact ⟨elf, hparse, cliPqxdhElfCorrectPlaced_of_strict2 hStrict⟩

theorem cliPqxdhBinaryCorrectPlaced_of_strict2
    {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlaced2 bytes) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  fun mpl mmpl hLs hMal => cliPqxdhBinaryCorrectPlacedAt_of_strict2 (h mpl mmpl hLs hMal)

/-! ## Shape-H + `¬ CliReachesOOMPlaced` ⇒ Strict Recovery -/

/-- Recover strict `CliSpecPqxdh` from `CliSpecPqxdhOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)`
and pointwise `¬ CliReachesOOMPlaced mpl mmpl elf W i` across `CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
theorem cliSpecPqxdh_of_orExcusedAbort_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {run : CliRun} {X : UnreachedPqxdhPrimitives}
    (hOr : CliSpecPqxdhOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W) run X ⟨W.C, W.Q⟩)
    (hNoOOM : ∀ i, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdh run X ⟨W.C, W.Q⟩ := by
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5⟩ := hOr st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact outcomeOrExcusedAbort_eq_of_not_exc (h1 b t hnone)
      (hNoOOM _ ⟨st, hst, Or.inl ⟨hnone, b, t, rfl⟩⟩)
  · intro m r hm
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h2 m r hm)
      (hNoOOM _ ⟨st, hst, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩)).trans some_ite2
  · intro c rc hc
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h3 c rc hc)
      (hNoOOM _ ⟨st, hst, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩)).trans some_ite
  · intro m rc hm hmatch
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h4 m rc hm hmatch)
      (hNoOOM _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)).trans some_ite
  · intro c rc hc h2ne h3ne
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h5 c rc hc h2ne h3ne)
      (hNoOOM _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2ne, h3ne, rfl⟩)))⟩)).trans some_ite

/-- Recover strict `CliSpecPqxdhNoMatch` from
`CliSpecPqxdhNoMatchOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` and pointwise
`¬ CliReachesOOMPlaced mpl mmpl elf W i` across `CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
theorem cliSpecPqxdhNoMatch_of_orExcusedAbort_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {run : CliRun} {X : UnreachedPqxdhPrimitives}
    (hOr : CliSpecPqxdhNoMatchOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W) run X ⟨W.C, W.Q⟩)
    (hNoOOM : ∀ i, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdhNoMatch run X ⟨W.C, W.Q⟩ := by
  intro st hst x g hsess m rc hm hnm
  refine exists_some_ite_eq ?_
  exact outcomeOrExcusedAbort_of_not_exc (hOr st hst x g hsess m rc hm hnm)
    (hNoOOM _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)

/-- Shape-H `CliPqxdhElfCorrectPlaced mpl mmpl elf` together with pointwise
`¬ CliReachesOOMPlaced mpl mmpl elf W i` across `CliPqxdhInputs ⟨W.C, W.Q⟩` implies
`CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hElf : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOOM : ∀ (W : CliHooks) (i : Inputs),
      CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  ⟨hElf.1, fun W X =>
    ⟨cliSpecPqxdh_of_orExcusedAbort_noOOM (hElf.2 W X).1 (hNoOOM W),
     cliSpecPqxdhNoMatch_of_orExcusedAbort_noOOM (hElf.2 W X).2 (hNoOOM W)⟩⟩

theorem cliPqxdhBinaryCorrectStrictPlacedAt2_of_noOOM
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (hBin : CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes)
    (hNoOOM : ∀ (elf : ElfImage) (W : CliHooks) (i : Inputs),
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectStrictPlacedAt2 mpl mmpl bytes := by
  obtain ⟨elf, hparse, hElf⟩ := hBin
  exact ⟨elf, hparse,
    cliPqxdhElfCorrectStrictPlaced2_of_noOOM hElf (fun W i hi => hNoOOM elf W i hparse hElf.1 hi)⟩

theorem cliPqxdhBinaryCorrectStrictPlaced2_of_noOOM
    {bytes : List (BitVec 8)}
    (hBin : CliPqxdhBinaryCorrectPlaced bytes)
    (hNoOOM : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs),
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectStrictPlaced2 bytes :=
  fun mpl mmpl hLs hMal =>
    cliPqxdhBinaryCorrectStrictPlacedAt2_of_noOOM (hBin mpl mmpl hLs hMal)
      (fun elf W i hparse hCode hi => hNoOOM mpl mmpl elf W i hLs hMal hparse hCode hi)

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
