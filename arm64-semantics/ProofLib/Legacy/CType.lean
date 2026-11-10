/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.CType
public import ProofLib.ObjectLoad
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# `Obj.LinkedImage` `c_type_spec` Refinement Lemmas

Refinement lemmas bridging base `Obj.LinkedImage.subroutineOk` contracts to typed `c_type_spec`
contracts without adding `ProofLib.ObjectLoad` to `ProofLib.CType`.
-/

namespace Arm64.CType

@[expose] public section

open Arm64 ProofLib

/-- Refine a proved `Obj.LinkedImage.subroutineOk` contract `spec` to `spec'` via a ghost witness
    map `f : β -> State -> α` whose precondition and postcondition entailments hold. -/
theorem LinkedImage.subroutineOk_refine {α β : Type} {li : Obj.LinkedImage} {fn : String}
    {spec : Spec α} {spec' : Spec β}
    (h : li.subroutineOk fn spec) (f : β → State → α)
    (hpre : ∀ y s0, spec'.pre y s0 ⊢ spec.pre (f y s0) s0)
    (hpost : ∀ y s0 sf, spec.post (f y s0) s0 sf ⊢ spec'.post y s0 sf)
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ x code R (s0 sf : State), ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ y R (s0 sf : State), sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom (f y s0) s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    li.subroutineOk fn spec' := by
  intro img hl
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro y R s0 hpc hrun hp hsp hL
  have hp' : s0.mem ⊨ spec.pre (f y s0) s0 ∗ R :=
    Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
  rcases reaches_outcome_iff.1 (subroutine_ok_iff.1 (h img hl) (f y s0) R s0 hpc hrun hp' hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨hoom_st, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left (hpost y s0 sf)) hq⟩⟩
  · exact absurd hq (hpanic _ _ s0 sf)
  · exact absurd hq (hexit _ code _ s0 sf)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom y R s0 sf hoom_st hq⟩))⟩

/-- Framed variant of `LinkedImage.subroutineOk_refine` where `spec'.pre` splits into `spec.pre`
    plus a frame `F y s0` preserved across the call and recombined in `spec'.post`. -/
theorem LinkedImage.subroutineOk_refine_frame {α β : Type} {li : Obj.LinkedImage} {fn : String}
    {spec : Spec α} {spec' : Spec β}
    (h : li.subroutineOk fn spec) (f : β → State → α) (F : β → State → SepProp)
    (hpre : ∀ y s0, spec'.pre y s0 ⊢ spec.pre (f y s0) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, spec.post (f y s0) s0 sf ∗ F y s0 ⊢ spec'.post y s0 sf)
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ x code R (s0 sf : State), ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ y R (s0 sf : State), sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom (f y s0) s0 sf ∗ (F y s0 ∗ R)) → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    li.subroutineOk fn spec' := by
  intro img hl
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro y R s0 hpc hrun hp hsp hL
  have hp' : s0.mem ⊨ spec.pre (f y s0) s0 ∗ (F y s0 ∗ R) := by
    have h1 := Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
    rwa [sepConj_assoc] at h1
  rcases reaches_outcome_iff.1 (subroutine_ok_iff.1 (h img hl) (f y s0) (F y s0 ∗ R) s0 hpc hrun hp' hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨hoom_st, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost y s0 sf)) hq
  · exact absurd hq (hpanic _ _ s0 sf)
  · exact absurd hq (hexit _ code _ s0 sf)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom y R s0 sf hoom_st hq⟩))⟩

end

end Arm64.CType
