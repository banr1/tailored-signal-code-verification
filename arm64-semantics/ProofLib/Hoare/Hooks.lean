/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Lemmas
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Stack
public import ProofLib.ObjectLoad
public import ProofLib.Library
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Extern Hooks and Subroutine Combinators

Lifts `HookOk` contracts and Rust panic stubs into `subroutine_ok` facts on rebased programs,
and provides consequence, ghost-refinement, case-splitting, trampoline (`B target`), and
library-dependency combinators for `subroutine_ok` and `library_ok`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- An extern entry point whose hook meets its contract is a subroutine meeting the contract. -/
theorem subroutine_ok_of_hookOk {α : Type} {prog : Program} {entry : BitVec 64}
    {f : State → State} {spec : Spec α}
    (hext : prog.externAt? entry = some f) (hok : HookOk f spec) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hkeep, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  exact reaches_outcome_extern hrun (hpc ▸ hext) hkeep (reaches_outcome_iff.mpr fun _ => ⟨f s0, Steps.refl _, hout⟩) hsym

/-- Absorb an extra frame `F` into `anyHeap` under `Spec.allowPanicWhen`. -/
theorem satisfies_allowPanicWhen_frame {φ ψ : Prop} {F R : SepProp} {m : Memory}
    (himp : φ → ψ) (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (F ∗ R)) :
    m ⊨ (⌜ψ⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  refine ⟨himp h.1, ?_⟩
  rw [← sepConj_assoc] at h
  exact Satisfies.mono (sepConj_mono_left (Entails.top_right fun _ => SepProp.holds_anyHeap_iff.mpr trivial)) h.2


/-- Consequence rule changing the ghost type and the frame for non-panicking, non-exiting specs
    (or when `spec`'s panic/exit postconditions are `⌜False⌝`). -/
theorem subroutine_ok_map {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry spec)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x y R R' s0 sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj ho) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_iff.mpr fun y R s0 hpc hrun hp hsp => reaches_outcome_iff.mpr fun hL => ?_
  obtain ⟨x, R', hm, himp_post⟩ := hmap y R s0 hp
  rcases reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R' s0 hpc hrun hm hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, himp_post sf hq⟩⟩
  · exact False.elim (h_no_panic x R' s0 sf hpan hq)
  · exact False.elim (h_no_exit x code R' s0 sf hex hq)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, h_oom x y R R' s0 sf hoom hq⟩))⟩

/-- Consequence rule changing the ghost type and the frame for specs that may panic (`onPanic`). -/
theorem subroutine_ok_map_panic {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry spec)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x y R R' s0 sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj ho) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_iff.mpr fun y R s0 hpc hrun hp hsp => reaches_outcome_iff.mpr fun hL => ?_
  obtain ⟨x, R', hm, himp_post, himp_panic⟩ := hmap y R s0 hp
  rcases reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R' s0 hpc hrun hm hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, himp_post sf hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, himp_panic sf hq⟩)⟩
  · exact False.elim (h_no_exit x code R' s0 sf hex hq)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, h_oom x y R R' s0 sf hoom hq⟩))⟩

/-- Consequence rule changing the ghost type and the frame for non-panicking, non-exiting specs
    with an explicit out-of-memory postcondition map (`onOom`). -/
theorem subroutine_ok_map_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry spec)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_iff.mpr fun y R s0 hpc hrun hp hsp => reaches_outcome_iff.mpr fun hL => ?_
  obtain ⟨x, R', hm, himp_post, himp_oom⟩ := hmap y R s0 hp
  rcases reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R' s0 hpc hrun hm hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, himp_post sf hq⟩⟩
  · exact False.elim (h_no_panic x R' s0 sf hpan hq)
  · exact False.elim (h_no_exit x code R' s0 sf hex hq)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, himp_oom sf hq⟩))⟩

/-- Case split on a ghost condition `c : α → Prop`. -/
theorem subroutine_ok_by_cases {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (c : α → Prop)
    (h1 : subroutine_ok prog entry
      { spec with pre := fun x s => ⌜c x⌝ ∗ spec.pre x s })
    (h2 : subroutine_ok prog entry
      { spec with pre := fun x s => ⌜¬ c x⌝ ∗ spec.pre x s }) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hc : c x
  · exact (subroutine_ok_iff.mp h1 x R s0 hpc hrun (by rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hc, hpre⟩) hsp).mono_outcome fun _ h => h
  · exact (subroutine_ok_iff.mp h2 x R s0 hpc hrun (by rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hc, hpre⟩) hsp).mono_outcome fun _ h => h

abbrev subroutine_ok_split := @subroutine_ok_by_cases

/-- Monotonicity rule for `subroutine_ok` using direct separation-logic entailment (`⊢`) on
    preconditions and return stack-pointer equality `sf.sp = s0.sp` on postconditions. -/
theorem subroutine_ok_mono_sp {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec spec' : Spec α}
    (hok : subroutine_ok prog entry_pc spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0)
    (hpost : ∀ x s0 sf, sf.sp = s0.sp → spec.post x s0 sf ⊢ spec'.post x s0 sf)
    (hpanic : ∀ x R s0 sf, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) → (sf.mem ⊨ spec'.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; first | exact hp | exact False.elim (not_satisfies_false_sepConj hp))
    (hexit : ∀ x code R s0 sf, (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) → (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; first | exact he | exact False.elim (not_satisfies_false_sepConj he))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    subroutine_ok prog entry_pc spec' := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hp hsp_align => reaches_outcome_iff.mpr fun hL => ?_
  rcases reaches_outcome_iff.mp (subroutine_ok_iff.mp hok x R s0 hpc hrun
      (Satisfies.mono (sepConj_mono_left (hpre x s0)) hp) hsp_align) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left (hpost x s0 sf hret.2.1)) hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic x R s0 sf hq⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hex, hexit x code R s0 sf hq⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom x R s0 sf hq⟩))⟩

/-- Ghost-refining consequence rule for `subroutine_ok` where postcondition adaptation is a direct
    separation-logic entailment (`specC.post y s0 sf ⊢ specA.post x s0 sf`). -/
theorem subroutine_ok_refine_entails {α β : Type} {prog : Program} {entry_pc : BitVec 64}
    {specC : Spec α} {specA : Spec β}
    (hok : subroutine_ok prog entry_pc specC)
    (h : ∀ x R s0, (s0.mem ⊨ specA.pre x s0 ∗ R) →
      ∃ y, (s0.mem ⊨ specC.pre y s0 ∗ R) ∧ ∀ sf, specC.post y s0 sf ⊢ specA.post x s0 sf)
    (hpanic : ∀ y R (s0 sf : State), ¬ (sf.mem ⊨ specC.onPanic y s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ y code R (s0 sf : State), ¬ (sf.mem ⊨ specC.onExit y code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y R (s0 sf : State),
      (sf.mem ⊨ specC.onOom y s0 sf ∗ R) → (sf.mem ⊨ specA.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    subroutine_ok prog entry_pc specA :=
  subroutine_ok_refine hok
    (fun x R s0 hp =>
      let ⟨y, hy, hpost⟩ := h x R s0 hp
      ⟨y, hy, fun sf hq => Satisfies.mono (sepConj_mono_left (hpost sf)) hq⟩)
    hpanic hexit (fun y x R s0 sf => hoom x y R s0 sf)

/-- Ghost- and residual-frame-refining consequence rule for `subroutine_ok`: allows carving an extra
    local frame `F : SepProp` from `specA.pre` across the execution of `specC`. -/
theorem subroutine_ok_refine_frame {α β : Type} {prog : Program} {entry_pc : BitVec 64}
    {specC : Spec α} {specA : Spec β}
    (hok : subroutine_ok prog entry_pc specC)
    (h : ∀ x R s0, (s0.mem ⊨ specA.pre x s0 ∗ R) →
      ∃ y F, (s0.mem ⊨ specC.pre y s0 ∗ (F ∗ R)) ∧
        ∀ sf, (sf.mem ⊨ specC.post y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ specA.post x s0 sf ∗ R))
    (hpanic : ∀ y R (s0 sf : State), ¬ (sf.mem ⊨ specC.onPanic y s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ y code R (s0 sf : State), ¬ (sf.mem ⊨ specC.onExit y code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y F R (s0 sf : State),
      (sf.mem ⊨ specC.onOom y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ specA.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    subroutine_ok prog entry_pc specA := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hp hsp => reaches_outcome_iff.mpr fun hL => ?_
  obtain ⟨y, F, hy, hpost⟩ := h x R s0 hp
  rcases reaches_outcome_iff.mp (subroutine_ok_iff.mp hok y (F ∗ R) s0 hpc hrun hy hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨hoom_st, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, hpost sf hq⟩⟩
  · exact absurd hq (hpanic y (F ∗ R) s0 sf)
  · exact absurd hq (hexit y code (F ∗ R) s0 sf)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom x y F R s0 sf hq⟩))⟩

/-- Use a non-panicking, non-exiting `subroutine_ok` fact at one ghost value to discharge one
    instance of another spec. -/
theorem subroutine_ok_at {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {spec' : Spec β} (h : subroutine_ok prog entry spec) (x : α)
    {y : β} {R : SepProp} {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hpre : ∃ R', (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
      ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code R' sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    reaches_outcome prog spec' y R s0 s0 := by
  obtain ⟨R', hm, himp_post⟩ := hpre
  refine reaches_outcome_iff.mpr fun hL => ?_
  rcases reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R' s0 hpc hrun hm hsp) hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, himp_post sf hq⟩⟩
  · exact False.elim (h_no_panic R' sf hpan hq)
  · exact False.elim (h_no_exit code R' sf hex hq)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, h_oom R' sf hoom hq⟩))⟩

/-- Attach `stackAt s.sp hookStack` to a specification's precondition and postcondition, leaving
    `onPanic`, `onExit`, and `onOom` unchanged. -/
def _root_.Arm64.Spec.withHookStack {α : Type} (spec : Spec α) (hookStack : Nat) : Spec α where
  pre := fun x s => spec.pre x s ∗ stackAt s.sp hookStack
  post := fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp hookStack
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

@[simp] theorem _root_.Arm64.Spec.withHookStack_pre {α : Type} (spec : Spec α) (n : Nat)
    (x : α) (s : State) :
    (spec.withHookStack n).pre x s = (spec.pre x s ∗ stackAt s.sp n) := rfl

@[simp] theorem _root_.Arm64.Spec.withHookStack_post {α : Type} (spec : Spec α) (n : Nat)
    (x : α) (s0 sf : State) :
    (spec.withHookStack n).post x s0 sf = (spec.post x s0 sf ∗ stackAt s0.sp n) := rfl

@[simp] theorem _root_.Arm64.Spec.withHookStack_onPanic {α : Type} (spec : Spec α) (n : Nat) :
    (spec.withHookStack n).onPanic = spec.onPanic := rfl

@[simp] theorem _root_.Arm64.Spec.withHookStack_onExit {α : Type} (spec : Spec α) (n : Nat) :
    (spec.withHookStack n).onExit = spec.onExit := rfl

@[simp] theorem _root_.Arm64.Spec.withHookStack_onOom {α : Type} (spec : Spec α) (n : Nat) :
    (spec.withHookStack n).onOom = spec.onOom := rfl

/-- An extern hook `hname` at stub offset `stub` meeting `spec` gives `subroutine_ok` at
    `fnAddr name + k` of `P.rebase b H`. -/
theorem hook_ok_at_raw {α : Type} {P : Program} {b : BitVec 64}
    {H : String → Option (State → State)} {name hname : String} {off k stub : Nat}
    {spec : Spec α}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (P.rebase 0 X).hookAtOff? stub = X hname)
    (hsat : HookSat H hname spec) :
    subroutine_ok (P.rebase b H) ((P.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  refine subroutine_ok_of_hookOk ?_ hok
  rw [Program.externAt?_fnAddr_add hfn hk hs, hstub, hf]

/-- An extern hook `hname` at stub offset `stub` in `code` meeting `spec` gives
    `subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub) spec`. -/
theorem hook_ok_stub {α : Type} {code : Program} {b : BitVec 64}
    {hooks : String → Option (State → State)} {hname : String} {stub : Nat}
    {spec : Spec α}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X hname)
    (hsat : HookSat hooks hname spec) :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  refine subroutine_ok_of_hookOk ?_ hok
  rw [Program.externAt?_rebase_add stub hs, hstub, hf]

/-- A non-panic hook `hname` at stub offset `stub` meeting `spec` gives `subroutine_ok` at
    `fnAddr name + k` of `P.rebase b (Rust.withPanics hooks)`. -/
theorem hook_ok_at {α : Type} {P : Program} {b : BitVec 64}
    {hooks : String → Option (State → State)} {name hname : String} {off k stub : Nat}
    {spec : Spec α}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat hooks hname spec) :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k) spec := by
  refine hook_ok_at_raw hfn hk hs hstub ?_
  obtain ⟨f, hf, hok⟩ := hsat
  exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩

/-- A stub `hname` that is a recognized Rust panic symbol (`Rust.isPanicSymbol hname = true`)
    evaluates to `some Rust.panicked` at `fnAddr name + k` of `P.rebase b (Rust.withPanics hooks)`. -/
theorem panic_at_panicSymbol {P : Program} {b : BitVec 64}
    {hooks : String → Option (State → State)} {name hname : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H hname)
    (hp : Rust.isPanicSymbol hname = true) :
    (P.rebase b (Rust.withPanics hooks)).externAt?
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked := by
  rw [Program.externAt?_fnAddr_add hfn hk hs, hstub, Rust.withPanics, hp]
  rfl

/-- A stub `hname` mapped to `some Rust.panicked` in `hooks` evaluates to `some Rust.panicked`
    at `fnAddr name + k` of `P.rebase b (Rust.withPanics hooks)`. -/
theorem panic_at_hook {P : Program} {b : BitVec 64}
    {hooks : String → Option (State → State)} {name hname : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H hname)
    (hp : hooks hname = some Rust.panicked) :
    (P.rebase b (Rust.withPanics hooks)).externAt?
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked := by
  rw [Program.externAt?_fnAddr_add hfn hk hs, hstub, Rust.withPanics]
  split <;> simp [hp]

/-- Bit 63 test (as produced by `tbnz x, #63`) in terms of `toNat`. -/
theorem getLsbD_63_iff (n : BitVec 64) : n.getLsbD 63 = true ↔ 2 ^ 63 ≤ n.toNat := by
  have := BitVec.msb_eq_decide n
  rw [BitVec.msb_eq_getLsbD_last] at this
  simp at this
  simp [this]

/-- A `b` instruction to a subroutine meeting `spec` meets `spec` (for specs that do not read
    the PC). -/
theorem subroutine_ok_of_b {α : Type} {prog : Program} {entry tgt : BitVec 64} {t : BitVec 64}
    {spec : Spec α} (hfetch : prog.fetch entry = some (.b t))
    (ht : entry + t = tgt) (_hno : false = false := rfl)
    (hpre : ∀ x s pc, spec.pre x (s.setPC pc) = spec.pre x s := by intros; rfl)
    (h : subroutine_ok prog tgt spec)
    (hpost : ∀ x s pc sf, spec.post x (s.setPC pc) sf = spec.post x s sf := by intros; rfl)
    (hpan : ∀ x s pc sf, spec.onPanic x (s.setPC pc) sf = spec.onPanic x s sf := by intros; rfl)
    (hexit : ∀ x code s pc sf, spec.onExit x code (s.setPC pc) sf = spec.onExit x code s sf := by intros; rfl)
    (hoom : ∀ x s pc sf, spec.onOom x (s.setPC pc) sf = spec.onOom x s sf := by intros; rfl) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok_iff.mpr fun x R s0 hpc hrun hm hsp => reaches_outcome_iff.mpr fun hcode => ?_
  have hex : prog.evalInst (.b t) s0 = s0.setPC tgt := by
    simp [Program.evalInst, execInstWithSvc, hpc, ht]
  have hstep : Step prog s0 (s0.setPC tgt) := by
    rw [← hex]
    exact Step.exec hrun (Program.fetchMem_of_fetch hcode (hpc ▸ hfetch))
  obtain ⟨sf, hsteps, hout⟩ :=
    reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R (s0.setPC tgt) rfl hrun (by rw [hpre]; exact hm)
      (by simpa [State.spAligned] using hsp)) hcode
  refine ⟨sf, Steps.step hstep hsteps, ?_⟩
  rcases hout with ⟨⟨hret_pc, hret_sp, hret_run⟩, ⟨hcc_sp, hcc_cs⟩, hq⟩ | ⟨hpan_sf, hq⟩ | ⟨code, hex_sf, hq⟩ | ⟨hoom_sf, hq⟩
  · exact Or.inl ⟨⟨by simpa using hret_pc, by simpa using hret_sp, hret_run⟩,
      ⟨by simpa using hcc_sp, by simpa [CalleeSavedPreserved] using hcc_cs⟩,
      by rwa [hpost] at hq⟩
  · exact Or.inr (Or.inl ⟨hpan_sf, by rwa [hpan] at hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_sf, by rwa [hexit] at hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_sf, by rwa [hoom] at hq⟩))

/-- Lift a `subroutine_ok` proof on `code.rebase img.base hooks` to `prog` (typically
    `Program.ofImage img hooks`, or a `.text`-sliced variant thereof) in $O(1)$ using
    `hEq : prog = code.rebase img.base hooks`. -/
theorem subroutine_ok_ofImage {α : Type} {code prog : Program} (img : Obj.Image)
    (hooks : String → Option (State → State)) (name : String) (spec : Spec α)
    (hEq : prog = code.rebase img.base hooks)
    (h : subroutine_ok (code.rebase img.base hooks)
      ((code.rebase img.base hooks).fnAddr name) spec) :
    subroutine_ok prog (prog.fnAddr name) spec :=
  @Eq.ndrec Program (code.rebase img.base hooks)
    (fun p => subroutine_ok p (p.fnAddr name) spec)
    h prog hEq.symm

/-- Establish `library_ok L` when `L.obj = some o`, every direct dependency `D ∈ L.deps`
    already satisfies `library_ok D`, and every contract in `L.contracts` holds in any
    image linking `o`. -/
theorem library_ok_of_deps {L : LibrarySpec} {o : Obj.ObjectInfo}
    (hobj : L.obj = some o)
    (hdeps : ∀ D ∈ L.deps, library_ok D)
    (hcontracts : ∀ (img : Obj.Image) (X : String → Option (State → State)),
      (∃ li : Obj.LinkedImage, o ∈ li.objects ∧ Obj.Loads li img) →
      ∀ c ∈ L.contracts, Contract.Holds L img X c) :
    library_ok L := by
  refine ⟨fun D hD _ => ?_, fun img X hLinks _ D hD hDT c hc => ?_⟩
  · rcases LibrarySpec.mem_closure_iff.1 hD with ⟨B, hB, hDB⟩ | rfl
    · exact (hdeps B hB).1 D hDB List.not_mem_nil
    · simp [hobj]
  · rcases LibrarySpec.mem_closure_iff.1 hD with ⟨B, hB, hDB⟩ | rfl
    · have hB_closure : B ∈ L.closure :=
        LibrarySpec.mem_closure_iff.2 (Or.inl ⟨B, hB, B.self_mem_closure⟩)
      have hLinksB : LinksIn B.closure img [] :=
        hLinks.mono fun D' hD' => ⟨L.closure_trans hB_closure hD', id⟩
      have hTrustedB : TrustedLibrariesOK [] img X B.closure :=
        fun _ _ h => False.elim (List.not_mem_nil h)
      exact (hdeps B hB).2 img X hLinksB hTrustedB D hDB hDT c hc
    · obtain ⟨li, hmem, hloads⟩ := hLinks
      have ho : o ∈ li.objects :=
        LinksIn.objectLoaded hmem D.self_mem_closure List.not_mem_nil hobj
      exact hcontracts img X ⟨li, ho, hloads⟩ c hc

/-- Special case of `library_ok_of_deps` when `L.deps = [B]` and `library_ok B`. -/
theorem library_ok_dep1 {L B : LibrarySpec} {o : Obj.ObjectInfo}
    (hB : library_ok B)
    (hdeps : L.deps = [B])
    (hobj : L.obj = some o)
    (hcontracts : ∀ (img : Obj.Image) (X : String → Option (State → State)),
      (∃ li : Obj.LinkedImage, o ∈ li.objects ∧ Obj.Loads li img) →
      ∀ c ∈ L.contracts, Contract.Holds L img X c) :
    library_ok L := by
  refine library_ok_of_deps hobj (fun D hD => ?_) hcontracts
  rw [hdeps, List.mem_singleton] at hD
  subst hD
  exact hB

end ProofLib

namespace Arm64
export ProofLib (
  subroutine_ok_mono_sp subroutine_ok_refine_entails subroutine_ok_refine_frame
  subroutine_ok_of_b subroutine_ok_ofImage library_ok_of_deps library_ok_dep1
)
end Arm64
