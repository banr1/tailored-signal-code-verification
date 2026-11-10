/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# AAPCS64 Procedure Call Combinators and Proof Rules

Proof-side `Spec` combinators (`Spec.split`, `Spec.fn1`..`fn3`, `Spec.withPreserves`,
`Spec.withStack`, `Spec.withGuard`, `Spec.withPanicWhen`) together with introduction,
elimination, consequence, and framing rules for `subroutine_ok`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Relational and Compositional `Spec` Combinators -/

/-- Build a relational `Spec α` from separate register and memory predicates. -/
@[simp, arm64_norm]
def _root_.Arm64.Spec.split {α : Type}
    (preRegs : α → State → Prop) (preMem : α → SepProp)
    (postRegs : α → State → State → Prop) (postMem : α → SepProp) : Spec α where
  pre  := fun x s0 => ⌜preRegs x s0⌝ ∗ preMem x
  post := fun x s0 sf => ⌜postRegs x s0 sf⌝ ∗ postMem x

/-- `Spec` for a pure unary 64-bit function `f` (`X0 ↦ f X0`). -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.fn1 (f : BitVec 64 → BitVec 64) : Spec (BitVec 64) where
  pre  := fun x s0 => ⌜s0.readReg64 .x0 = x⌝
  post := fun x _ sf => ⌜sf.readReg64 .x0 = f x⌝

/-- `Spec` for a pure binary 64-bit function `f` (`(X0, X1) ↦ f X0 X1` in `X0`). -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.fn2 (f : BitVec 64 → BitVec 64 → BitVec 64) :
    Spec (BitVec 64 × BitVec 64) where
  pre  := fun (a, b) s0 => ⌜s0.readReg64 .x0 = a ∧ s0.readReg64 .x1 = b⌝
  post := fun (a, b) _ sf => ⌜sf.readReg64 .x0 = f a b⌝

/-- `Spec` for a pure ternary 64-bit function `f` (`(X0, X1, X2) ↦ f X0 X1 X2` in `X0`). -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.fn3 (f : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre  := fun (a, b, c) s0 =>
    ⌜s0.readReg64 .x0 = a ∧ s0.readReg64 .x1 = b ∧ s0.readReg64 .x2 = c⌝
  post := fun (a, b, c) _ sf => ⌜sf.readReg64 .x0 = f a b c⌝

/-- Conjoin a preserved spatial assertion `F x` across `pre`, `post`, `onPanic`, `onExit`,
    and `onOom`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.withPreserves {α : Type} (spec : Spec α) (F : α → SepProp) : Spec α where
  pre     := fun x s0 => spec.pre x s0 ∗ F x
  post    := fun x s0 sf => spec.post x s0 sf ∗ F x
  onPanic := fun x s0 sf => spec.onPanic x s0 sf ∗ F x
  onExit  := fun x code s0 sf => spec.onExit x code s0 sf ∗ F x
  onOom   := fun x s0 sf => spec.onOom x s0 sf ∗ F x

/-- Conjoin a `len`-byte downward stack frame (`stackFrame s len`) to `pre` and `post`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.withStack {α : Type} (spec : Spec α) (len : Nat) : Spec α where
  pre     := fun x s0 => spec.pre x s0 ∗ stackFrame s0 len
  post    := fun x s0 sf => spec.post x s0 sf ∗ stackFrame sf len
  onPanic := spec.onPanic
  onExit  := spec.onExit
  onOom   := spec.onOom

/-- Conjoin a 16-byte downward stack frame (`stackFrame16 s`) to `pre` and `post`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.withStack16 {α : Type} (spec : Spec α) : Spec α where
  pre     := fun x s0 => spec.pre x s0 ∗ stackFrame16 s0
  post    := fun x s0 sf => spec.post x s0 sf ∗ stackFrame16 sf
  onPanic := spec.onPanic
  onExit  := spec.onExit
  onOom   := spec.onOom

/-- Conjoin a 32-byte downward stack frame (`stackFrame32 s`) to `pre` and `post`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.withStack32 {α : Type} (spec : Spec α) : Spec α where
  pre     := fun x s0 => spec.pre x s0 ∗ stackFrame32 s0
  post    := fun x s0 sf => spec.post x s0 sf ∗ stackFrame32 sf
  onPanic := spec.onPanic
  onExit  := spec.onExit
  onOom   := spec.onOom

/-- Prepend a pure guard `⌜G x⌝` to `spec.pre`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.withGuard {α : Type} (spec : Spec α) (G : α → Prop) : Spec α where
  pre     := fun x s0 => ⌜G x⌝ ∗ spec.pre x s0
  post    := spec.post
  onPanic := spec.onPanic
  onExit  := spec.onExit
  onOom   := spec.onOom

/-- Set `onPanic` to the pure condition `⌜P x⌝`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.withPanicWhen {α : Type} (spec : Spec α) (P : α → Prop) : Spec α where
  pre     := spec.pre
  post    := spec.post
  onPanic := fun x _ _ => ⌜P x⌝
  onExit  := spec.onExit
  onOom   := spec.onOom

theorem Entails.pure_mono {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ : SepProp) ⊢ ⌜ψ⌝ :=
  SepProp.entails_iff.mpr fun _ hp =>
    let ⟨he, hφ⟩ := SepProp.holds_pure_iff.mp hp
    SepProp.holds_pure_iff.mpr ⟨he, h hφ⟩

theorem subroutine_ok_mono_entails {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec spec' : Spec α}
    (h : subroutine_ok prog entry_pc spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ⊢ spec'.post x s0 sf)
    (hpanic : ∀ x R s0 sf, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) → (sf.mem ⊨ spec'.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; first | exact hp | exact False.elim (not_satisfies_false_sepConj hp))
    (hexit : ∀ x code R s0 sf, (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) → (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; first | exact he | exact False.elim (not_satisfies_false_sepConj he))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    subroutine_ok prog entry_pc spec' :=
  subroutine_ok_mono h
    (fun x _ s0 hp => Satisfies.mono (sepConj_mono_left (hpre x s0)) hp)
    (fun x _ s0 sf hq => Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq)
    hpanic hexit hoom

/-- Rule of Consequence (precondition strengthening / postcondition weakening) for `subroutine_ok`
    where all five specification clauses weaken by separation-logic entailment (`⊢`). -/
theorem _root_.Arm64.subroutine_ok.conseq {α : Type} {prog : Program} {entry : BitVec 64}
    {spec₁ spec₂ : Spec α}
    (hok : subroutine_ok prog entry spec₁)
    (h_pre : ∀ x s0, spec₂.pre x s0 ⊢ spec₁.pre x s0)
    (h_post : ∀ x s0 sf, spec₁.post x s0 sf ⊢ spec₂.post x s0 sf)
    (h_panic : ∀ x s0 sf, spec₁.onPanic x s0 sf ⊢ spec₂.onPanic x s0 sf)
    (h_exit : ∀ x code s0 sf, spec₁.onExit x code s0 sf ⊢ spec₂.onExit x code s0 sf)
    (h_oom : ∀ x s0 sf, spec₁.onOom x s0 sf ⊢ spec₂.onOom x s0 sf :=
      by intro x s0 sf; exact Entails.refl _) :
    subroutine_ok prog entry spec₂ :=
  subroutine_ok_mono_entails hok h_pre h_post
    (fun x _ s0 sf hp => Satisfies.mono (sepConj_mono_left (h_panic x s0 sf)) hp)
    (fun x code _ s0 sf he => Satisfies.mono (sepConj_mono_left (h_exit x code s0 sf)) he)
    (fun x _ s0 sf ho => Satisfies.mono (sepConj_mono_left (h_oom x s0 sf)) ho)

/-! ## `Spec.split` Rules -/

/-- Introduction rule for `subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem)`. -/
theorem _root_.Arm64.Spec.split.intro {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → State → Prop} {preMem : α → SepProp}
    {postRegs : α → State → State → Prop} {postMem : α → SepProp}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      preRegs x s0 →
      (s0.mem ⊨ preMem x ∗ R) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0
        (SubroutinePost (Spec.split preRegs preMem postRegs postMem) x R s0)) :
    subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem) :=
  subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => by
    rw [Spec.split, sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact reaches_pc_mono (h x R s0 hpc hrun hpre.1 hpre.2 hsp) (fun _ _ _ hp => hp)
      (fun _ _ ho => False.elim ho)

/-- Elimination rule for `subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem)`. -/
theorem _root_.Arm64.Spec.split.apply {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → State → Prop} {preMem : α → SepProp}
    {postRegs : α → State → State → Prop} {postMem : α → SepProp}
    (h : subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem))
    (x : α) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hregs : preRegs x s0) (hmem : s0.mem ⊨ preMem x ∗ R)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0 (fun sf =>
      postRegs x s0 sf ∧ (sf.mem ⊨ postMem x ∗ R) ∧ CallingConventionPreserved s0 sf) := by
  have hpre : s0.mem ⊨ (Spec.split preRegs preMem postRegs postMem).pre x s0 ∗ R := by
    rw [Spec.split, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hregs, hmem⟩
  refine reaches_pc_mono (subroutine_ok_apply_full h x R hpc hrun hpre h_sp_align) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  rw [Spec.split, sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact ⟨hpost.1, hpost.2, hcc⟩

/-- Frame rule for `Spec.split`: any frame assertion `F x` is preserved across `subroutine_ok`. -/
theorem _root_.Arm64.Spec.split.frame {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → State → Prop} {preMem : α → SepProp}
    {postRegs : α → State → State → Prop} {postMem : α → SepProp}
    (h : subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem))
    (F : α → SepProp) :
    subroutine_ok prog entry
      (Spec.split preRegs (fun x => preMem x ∗ F x) postRegs (fun x => postMem x ∗ F x)) := by
  apply Spec.split.intro
  intro x R s0 hpc hrun hregs hmem hsp
  rw [sepConj_assoc] at hmem
  refine reaches_pc_mono (Spec.split.apply h x (F x ∗ R) hpc hrun hregs hmem hsp) ?_
  intro sf _ _ ⟨hr, hm, hcc⟩
  refine ⟨?_, hcc⟩
  rw [Spec.split, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc]
  exact ⟨hr, hm⟩

/-- Monotonicity rule for `Spec.split`. -/
theorem _root_.Arm64.Spec.split.mono {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs preRegs' : α → State → Prop} {preMem preMem' : α → SepProp}
    {postRegs postRegs' : α → State → State → Prop} {postMem postMem' : α → SepProp}
    (h : subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem))
    (hpreR : ∀ x s0, preRegs' x s0 → preRegs x s0)
    (hpreM : ∀ x, preMem' x ⊢ preMem x)
    (hpostR : ∀ x s0 sf, postRegs x s0 sf → postRegs' x s0 sf)
    (hpostM : ∀ x, postMem x ⊢ postMem' x) :
    subroutine_ok prog entry (Spec.split preRegs' preMem' postRegs' postMem') :=
  subroutine_ok_mono_entails h
    (fun x s0 => sepConj_mono (Entails.pure_mono (hpreR x s0)) (hpreM x))
    (fun x s0 sf => sepConj_mono (Entails.pure_mono (hpostR x s0 sf)) (hpostM x))

/-! ## `Spec.withPreserves` Framing Rule -/

/-- Framing rule for `Spec.withPreserves`: any `subroutine_ok` proof for `spec` lifts to
    `spec.withPreserves F` for any preserved spatial assertion `F : α → SepProp`. -/
theorem _root_.Arm64.Spec.withPreserves.frame {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) (F : α → SepProp) :
    subroutine_ok prog entry (spec.withPreserves F) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h ⊢
  intro x R s0 hpc hrun hpre hsp hL
  simp only [sepConj_assoc] at hpre
  rcases h x (F x ∗ R) s0 hpc hrun hpre hsp hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpanic, hq⟩ | ⟨code, hexit, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    simpa only [sepConj_assoc] using hq
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpanic, ?_⟩)⟩
    simpa only [sepConj_assoc] using hq
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))⟩
    simpa only [sepConj_assoc] using hq
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, ?_⟩))⟩
    simpa only [sepConj_assoc] using hq

end ProofLib
