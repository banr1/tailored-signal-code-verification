/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Spec/Implementation Split for Refinement Disproofs

Packages the common quantifier shape of the repository's refinement theorems as `RefinementShape`
and splits a witness-based disproof `¬ S.Refines H` into an implementation-independent `SpecHalf`
and a specification-independent `ImplHalf` (`not_refines_of_witness`, `refines_excludes_witness`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection

/-- Parameters and predicates common to the repository's refinement statements. -/
structure RefinementShape where
  /-- Implementation under test (for example, a loaded ELF image). -/
  Setup : Type
  /-- Interpretation of cryptographic externs and hooks. -/
  Interp : Type
  /-- Initial protocol setup records. -/
  Rec : Type
  /-- Existentially chosen ghost semantics for opaque symbols. -/
  Ghost : Type
  /-- Observable trace event type. -/
  Event : Type
  /-- Extern contract assumptions relating `Interp` and `Setup`. -/
  contracts : Interp → Setup → Prop
  /-- Well-formedness predicate on initial records. -/
  wf : Rec → Prop
  /-- Side conditions on the chosen ghost semantics. -/
  ghostOk : Interp → Rec → Ghost → Prop
  /-- Execution trace relation of `Setup`. -/
  traces : Setup → Interp → Rec → List Event → Prop
  /-- Specification predicate stating that a model run (or excused prefix) explains the trace. -/
  explained : Interp → Rec → Ghost → List Event → Prop

namespace RefinementShape

variable (S : RefinementShape)

/-- Refinement statement instantiated at setup `H`. -/
def Refines (H : S.Setup) : Prop :=
  ∀ i, S.contracts i H → ∀ r, S.wf r → ∃ P, S.ghostOk i r P ∧
    ∀ τ, S.traces H i r τ → S.explained i r P τ

/-- Specification half of a witness `(fits, τ)`: every fitting `(i, r)` satisfies `S.wf r` and
admits no valid ghost explaining `τ`. -/
def SpecHalf (fits : S.Interp → S.Rec → Prop) (τ : List S.Event) : Prop :=
  ∀ i r, fits i r → S.wf r ∧ ∀ P, S.ghostOk i r P → ¬ S.explained i r P τ

/-- Implementation half of a witness `(fits, τ)` for `H`: some fitting `(i, r)` satisfies
`S.contracts i H` and produces `τ`. -/
def ImplHalf (fits : S.Interp → S.Rec → Prop) (H : S.Setup) (τ : List S.Event) : Prop :=
  ∃ i r, fits i r ∧ S.contracts i H ∧ S.traces H i r τ

/-- A witness satisfying both `SpecHalf` and `ImplHalf` refutes `S.Refines H`. -/
theorem not_refines_of_witness {fits : S.Interp → S.Rec → Prop} {H : S.Setup}
    {τ : List S.Event} (hs : S.SpecHalf fits τ) (hi : S.ImplHalf fits H τ) : ¬ S.Refines H := by
  intro href
  obtain ⟨i, r, hfit, hc, ht⟩ := hi
  obtain ⟨hwf, hne⟩ := hs i r hfit
  obtain ⟨P, hok, hall⟩ := href i hc r hwf
  exact hne P hok (hall τ ht)

/-- Any setup satisfying `S.Refines H` rules out `S.ImplHalf fits H τ` whenever `S.SpecHalf fits τ`
holds. -/
theorem refines_excludes_witness {fits : S.Interp → S.Rec → Prop} {H : S.Setup}
    {τ : List S.Event} (href : S.Refines H) (hs : S.SpecHalf fits τ) :
    ¬ S.ImplHalf fits H τ :=
  fun hi => S.not_refines_of_witness hs hi href

end RefinementShape

end Symbolic.BugInjection
