/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.LibcHooks
import Arm64.Trusted.Spec.SepLogic

/-!
# Hook-Map Builders and `HookSat` Combinators

Association-list hook tables (`hookMap`) and `HookSat` / `HookOk` introduction and consequence
lemmas (`HookOk.mono`, `HookOk.comap`, `hookNoop_ok_of_entails`) for proving satisfiability of
extern-hook assumption bundles:

```lean
theorem WidgetHooks_sat : ∃ H, WidgetHooks H :=
  ⟨hookMap [("memcpy", hookMemcpy), ("memset", hookMemset)] (fun _ => none),
   { memcpy := by simp [hookMemcpy_ok], memset := by simp [hookMemset_ok] }⟩
```
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Association-list hook table: `hookMap entries base name` returns the first entry in `entries`
    matching `name`, or `base name` if none matches. -/
def hookMap : List (String × (State → State)) → (String → Option (State → State)) →
    String → Option (State → State)
  | [], base, name => base name
  | (n, f) :: rest, base, name => if name = n then some f else hookMap rest base name

@[simp] theorem hookMap_nil (base : String → Option (State → State)) (name : String) :
    hookMap [] base name = base name := rfl

@[simp] theorem hookMap_cons_self (n : String) (f : State → State)
    (rest : List (String × (State → State))) (base : String → Option (State → State)) :
    hookMap ((n, f) :: rest) base n = some f := by
  simp [hookMap]

@[simp] theorem hookMap_cons_of_ne {name n : String} (h : name ≠ n) (f : State → State)
    (rest : List (String × (State → State))) (base : String → Option (State → State)) :
    hookMap ((n, f) :: rest) base name = hookMap rest base name := by
  simp [hookMap, h]

theorem HookSat_of_HookOk {α : Type} {H : String → Option (State → State)} {name : String}
    {f : State → State} {spec : Spec α} (hH : H name = some f) (hf : HookOk f spec) :
    HookSat H name spec :=
  ⟨f, hH, hf⟩

theorem HookSat_iff_of_eq {α : Type} {H : String → Option (State → State)} {name : String}
    {f : State → State} {spec : Spec α} (hH : H name = some f) :
    HookSat H name spec ↔ HookOk f spec := by
  constructor
  · rintro ⟨g, hg, hok⟩
    rw [hH] at hg
    cases hg
    exact hok
  · exact HookSat_of_HookOk hH

@[simp] theorem HookSat_none {α : Type} {H : String → Option (State → State)} {name : String}
    {spec : Spec α} (hH : H name = none) : ¬ HookSat H name spec := by
  rintro ⟨f, hf, _⟩
  rw [hH] at hf
  cases hf

@[simp] theorem HookSat_hookMap_cons_self {α : Type} (n : String) (f : State → State)
    (rest : List (String × (State → State))) (base : String → Option (State → State))
    (spec : Spec α) :
    HookSat (hookMap ((n, f) :: rest) base) n spec ↔ HookOk f spec :=
  HookSat_iff_of_eq (hookMap_cons_self n f rest base)

@[simp] theorem HookSat_hookMap_cons_of_ne {α : Type} {name n : String} (h : name ≠ n)
    (f : State → State) (rest : List (String × (State → State)))
    (base : String → Option (State → State)) (spec : Spec α) :
    HookSat (hookMap ((n, f) :: rest) base) name spec ↔ HookSat (hookMap rest base) name spec := by
  unfold HookSat
  rw [hookMap_cons_of_ne h]

@[simp] theorem HookSat_hookMap_nil {α : Type} (base : String → Option (State → State))
    (name : String) (spec : Spec α) :
    HookSat (hookMap [] base) name spec ↔ HookSat base name spec := Iff.rfl

/-- Two contracts on the same symbol are met by the same hook: a bundle with fields
    `HookSat H n s₁` and `HookSat H n s₂` is satisfiable only if one `f` meets both. -/
theorem HookSat_and_iff {α β : Type} {H : String → Option (State → State)} {name : String}
    {s₁ : Spec α} {s₂ : Spec β} :
    (HookSat H name s₁ ∧ HookSat H name s₂) ↔
      ∃ f, H name = some f ∧ HookOk f s₁ ∧ HookOk f s₂ := by
  constructor
  · rintro ⟨⟨f, hf, h₁⟩, ⟨g, hg, h₂⟩⟩
    rw [hf] at hg
    cases hg
    exact ⟨f, hf, h₁, h₂⟩
  · rintro ⟨f, hf, h₁, h₂⟩
    exact ⟨⟨f, hf, h₁⟩, ⟨f, hf, h₂⟩⟩

theorem HookSat.same_hook {α β : Type} {H : String → Option (State → State)} {name : String}
    {s₁ : Spec α} {s₂ : Spec β} (h₁ : HookSat H name s₁) (h₂ : HookSat H name s₂) :
    ∃ f, HookOk f s₁ ∧ HookOk f s₂ :=
  let ⟨f, _, hf₁, hf₂⟩ := HookSat_and_iff.mp ⟨h₁, h₂⟩
  ⟨f, hf₁, hf₂⟩

/-- Consequence rule for `HookOk` on a fixed ghost type: strengthen the precondition, weaken the
    postcondition, and weaken the panic, exit, and OOM conditions (entailments under the same frame). -/
theorem HookOk.mono {α : Type} {f : State → State} {s₁ s₂ : Spec α} (h : HookOk f s₁)
    (hpre : ∀ x R s0, (s0.mem ⊨ s₂.pre x s0 ∗ R) → (s0.mem ⊨ s₁.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (s0.mem ⊨ s₂.pre x s0 ∗ R) →
      (sf.mem ⊨ s₁.post x s0 sf ∗ R) → (sf.mem ⊨ s₂.post x s0 sf ∗ R))
    (hpanic : ∀ x R s0 sf, (sf.mem ⊨ s₁.onPanic x s0 sf ∗ R) → (sf.mem ⊨ s₂.onPanic x s0 sf ∗ R))
    (hexit : ∀ x code R s0 sf,
      (sf.mem ⊨ s₁.onExit x code s0 sf ∗ R) → (sf.mem ⊨ s₂.onExit x code s0 sf ∗ R))
    (hoom : ∀ x R s0 sf,
      (sf.mem ⊨ s₁.onOom x s0 sf ∗ R) → (sf.mem ⊨ s₂.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    HookOk f s₂ := by
  intro x R s0 hrun hp hsp
  obtain ⟨hkeep, hsym, hout⟩ := h x R s0 hrun (hpre x R s0 hp) hsp
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hst, hq⟩ | ⟨code, hst, hq⟩ | ⟨hst, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 _ hp hq⟩
  · exact Or.inr (Or.inl ⟨hst, hpanic x R s0 _ hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hst, hexit x code R s0 _ hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hst, hoom x R s0 _ hq⟩))

/-- Change-of-ghost consequence rule for `HookOk`, for a source spec `s₁` that neither panics nor
    exits (default `⌜False⌝` `onPanic` / `onExit`): each `s₂` call `(y, R)` is an `s₁` call
    `(x, R')` whose postcondition implies `s₂.post y ∗ R`. -/
theorem HookOk.comap {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (h : HookOk f s₁)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ s₂.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ s₁.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ s₁.post x s0 sf ∗ R') → (sf.mem ⊨ s₂.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, ¬(sf.mem ⊨ s₁.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, ¬(sf.mem ⊨ s₁.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x y R R' s0 sf,
      (sf.mem ⊨ s₁.onOom x s0 sf ∗ R') → (sf.mem ⊨ s₂.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨x, R', hm, himp⟩ := hmap y R s0 hp
  obtain ⟨hkeep, hsym, hout⟩ := h x R' s0 hrun hm hsp
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨hst, hq⟩
  · exact Or.inl ⟨hret, hcc, himp _ hq⟩
  · exact False.elim (h_no_panic x R' s0 _ hq)
  · exact False.elim (h_no_exit x code R' s0 _ hq)
  · exact Or.inr (Or.inr (Or.inr ⟨hst, h_oom x y R R' s0 _ hq⟩))

theorem HookSat.mono {α β : Type} {H : String → Option (State → State)} {name : String}
    {s₁ : Spec α} {s₂ : Spec β} (h : HookSat H name s₁)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ s₂.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ s₁.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ s₁.post x s0 sf ∗ R') → (sf.mem ⊨ s₂.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, ¬(sf.mem ⊨ s₁.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, ¬(sf.mem ⊨ s₁.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x y R R' s0 sf,
      (sf.mem ⊨ s₁.onOom x s0 sf ∗ R') → (sf.mem ⊨ s₂.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    HookSat H name s₂ :=
  let ⟨f, hf, hok⟩ := h
  ⟨f, hf, HookOk.comap hok hmap h_no_panic h_no_exit h_oom⟩

/-- `hookNoop` meets any spec whose precondition entails its postcondition at the return state
    (memory unchanged), such as read-only `preserves P` specs with a stack-only footprint. -/
theorem hookNoop_ok_of_entails {α : Type} {spec : Spec α}
    (h : ∀ x s0, spec.pre x s0 ⊢ spec.post x s0 (hookNoop s0)) :
    HookOk hookNoop spec :=
  hookNoop_ok fun x _ s0 hpre => Satisfies.mono (sepConj_mono_left (h x s0)) hpre

end ProofLib
