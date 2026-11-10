/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.CoreLemmas
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model
import ProofLib.Hoare.SubroutineOk

/-!
# Partial-Correctness Safety and Step-Indexed Weakest Preconditions

Partial-correctness proof rules for `safe_until`, `safe_until_pc`, `safe_reaches`, and
`safe_subroutine_ok`, total-to-partial weakening from `reaches_stop` and `subroutine_ok`,
step-indexed weakest preconditions (`wp_idx` and `SepWP_idx`), and sentinel-`LR` first-stop
bridges for `StepsUntil (SubroutineStop s0)`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Alias of `Arm64.Step.status_running` in the `ProofLib` namespace. -/
@[deprecated Arm64.Step.status_running (since := "2026-10-26")]
theorem Step.status_running {prog : Program} {s s' : State} (h : Step prog s s') :
    s.status = .Running :=
  Arm64.Step.status_running h

/-- Comparing two `Steps` runs from the same start state `s0`: by determinism of `Step`,
    one run is a prefix of the other (`Steps prog s₁ s₂ ∨ Steps prog s₂ s₁`). -/
theorem Steps.compare {prog : Program} {s0 s₁ s₂ : State}
    (h₁ : Steps prog s0 s₁) (h₂ : Steps prog s0 s₂) :
    Steps prog s₁ s₂ ∨ Steps prog s₂ s₁ := by
  induction h₁ with
  | refl => exact Or.inl h₂
  | step hstep₁ _ ih =>
    cases h₂ with
    | refl => exact Or.inr (.step hstep₁ ‹_›)
    | step hstep₂ hrest₂ =>
      cases Step.deterministic hstep₁ hstep₂
      exact ih hrest₂

/-- Along any execution `Steps prog s0 sf`, every state `t` reachable from `s0` is either
    strictly before `sf` on the deterministic trace (and therefore `.Running` by
    `Arm64.Step.status_running`) or reachable from `sf` (`Steps prog sf t`). In particular, no execution
    from `s0` can reach a non-`.Running` state (fault, halt, panic, exit, or OOM) strictly before
    `sf`. -/
theorem Steps.running_or_steps_of {prog : Program} {s0 sf t : State}
    (hsf : Steps prog s0 sf) (ht : Steps prog s0 t) :
    t.status = .Running ∨ Steps prog sf t := by
  rcases Steps.compare hsf ht with hafter | hbefore
  · exact Or.inr hafter
  · cases hbefore with
    | refl => exact Or.inr (.refl _)
    | step hstep _ => exact Or.inl (Arm64.Step.status_running hstep)

/-- Comparing two `StepsUntil` runs from the same state: either `s2` lies at or after `s1`
    (a `StepsUntil` run from `s1` reaches it), or `s2` lies strictly before `s1`, in which case
    `s2` is `.Running` and has not yet satisfied `stop`. -/
theorem StepsUntil.compare {prog : Program} {stop : State → Prop} {s0 s1 s2 : State}
    (h1 : StepsUntil prog stop s0 s1) (h2 : StepsUntil prog stop s0 s2) :
    StepsUntil prog stop s1 s2 ∨ (¬ stop s2 ∧ s2.status = .Running) := by
  induction h1 with
  | refl => exact Or.inl h2
  | @step a b c hnstop hstep _ ih =>
    cases h2 with
    | refl => exact Or.inr ⟨hnstop, Arm64.Step.status_running hstep⟩
    | step _ hstep2 hrest2 =>
      cases Step.deterministic hstep hstep2
      exact ih hrest2

/-! ## Generic `safe_until` and `reaches_stop` Rules -/

/-- A concrete `StepsUntil` run to a stopping state `sf` satisfying `Q sf` gives `safe_until`
    with postcondition `Q` (by determinism of `Step`, every `StepsUntil` run from `s0` is a
    prefix of it). -/
theorem safe_until_of_stepsUntil {prog : Program} {stop : State → Prop} {s0 sf : State}
    {Q oom : State → Prop}
    (h_steps : StepsUntil prog stop s0 sf) (h_stop : stop sf) (h_Q : Q sf) :
    safe_until prog stop s0 Q oom := by
  intro _ s hs
  rcases StepsUntil.compare h_steps hs with h | ⟨hnstop, hrun⟩
  · cases h with
    | refl => exact Or.inl ⟨h_stop, h_Q⟩
    | step hnstop _ _ => exact absurd h_stop hnstop
  · exact Or.inr (Or.inr ⟨hnstop, hrun⟩)

/-- Total-to-partial weakening: `reaches_stop` implies `safe_until` with the same postcondition `Q`. -/
theorem _root_.Arm64.reaches_stop.to_safe {prog : Program} {stop : State → Prop} {s0 : State}
    {Q oom : State → Prop} (h : reaches_stop prog stop s0 Q) :
    safe_until prog stop s0 Q oom := by
  intro hL
  obtain ⟨sf, h_steps, h_stop, h_Q⟩ := h hL
  exact safe_until_of_stepsUntil h_steps h_stop h_Q hL

/-- Prefix rule for `safe_until`: run to an intermediate state `s1` via `StepsUntil`, then continue. -/
theorem safe_until.prefix {prog : Program} {stop : State → Prop} {s0 s1 : State}
    {Q oom : State → Prop}
    (h_steps : StepsUntil prog stop s0 s1) (h_rest : safe_until prog stop s1 Q oom) :
    safe_until prog stop s0 Q oom := by
  intro hL s hs
  have hL1 := h_steps.toSteps.codeLoaded hL
  rcases StepsUntil.compare h_steps hs with h | ⟨hnstop, hrun⟩
  · exact h_rest hL1 s h
  · exact Or.inr (Or.inr ⟨hnstop, hrun⟩)

/-- At a stopping state: `stop s` and `Q s` suffice. -/
theorem safe_until.done {prog : Program} {stop : State → Prop} {s : State} {Q oom : State → Prop}
    (h_stop : stop s) (h_Q : Q s) :
    safe_until prog stop s Q oom :=
  safe_until_of_stepsUntil (StepsUntil.refl s) h_stop h_Q

/-- Single-step forward rule for `safe_until`: the current state does not satisfy `stop`, takes a
    step to `s'`, and execution from `s'` is safe. -/
theorem safe_until.step {prog : Program} {stop : State → Prop} {s s' : State} {Q oom : State → Prop}
    (h_nstop : ¬ stop s) (h_step : Step prog s s')
    (h_rest : safe_until prog stop s' Q oom) :
    safe_until prog stop s Q oom :=
  safe_until.prefix (StepsUntil.step h_nstop h_step (StepsUntil.refl s')) h_rest


/-! ## Specializations to `safe_until_pc` -/

/-- A concrete first-visit run to `t`, ending running and satisfying `post`, gives `safe_until_pc`. -/
theorem safe_until_pc_of_stepsUntilPC {prog : Program} {t : BitVec 64} {s0 sf : State}
    {post oom : State → Prop}
    (h_steps : StepsUntilPC prog t s0 sf) (h_pc : sf.pc = t) (h_run : sf.status = .Running)
    (h_post : post sf) : safe_until_pc prog t s0 post oom :=
  safe_until_of_stepsUntil h_steps h_pc ⟨h_run, h_post⟩

/-- Prefix rule: run to an intermediate state `s1` without visiting `t`, then continue. -/
theorem safe_until_pc.prefix {prog : Program} {t : BitVec 64} {s0 s1 : State}
    {post oom : State → Prop}
    (h_steps : StepsUntilPC prog t s0 s1) (h_rest : safe_until_pc prog t s1 post oom) :
    safe_until_pc prog t s0 post oom :=
  safe_until.prefix h_steps h_rest

/-- At the target: `.Running` and `post` suffice. -/
theorem safe_until_pc.done {prog : Program} {t : BitVec 64} {s : State} {post oom : State → Prop}
    (h_pc : s.pc = t) (h_run : s.status = .Running) (h_post : post s) :
    safe_until_pc prog t s post oom :=
  safe_until_pc_of_stepsUntilPC (StepsUntil.refl s) h_pc h_run h_post

/-- Single-step forward rule for `safe_until_pc`. -/
theorem safe_until_pc.step {prog : Program} {t : BitVec 64} {s s' : State} {post oom : State → Prop}
    (h_ne : s.pc ≠ t) (h_step : Step prog s s')
    (h_rest : safe_until_pc prog t s' post oom) :
    safe_until_pc prog t s post oom :=
  safe_until.step h_ne h_step h_rest

private theorem safe_until_pc_of_steps_oom {prog : Program} {t : BitVec 64} {s0 sf : State}
    {oom : State → Prop}
    (hsteps : Steps prog s0 sf) (hoom : sf.status = .OutOfMemory) (hoom_sf : oom sf) :
    ∀ s, StepsUntilPC prog t s0 s →
      (s.pc = t ∧ s.status = .Running ∧ True) ∨ (s.status = .OutOfMemory ∧ oom s) ∨ (s.pc ≠ t ∧ s.status = .Running) := by
  induction hsteps with
  | refl =>
    intro s hs
    cases hs with
    | refl => exact Or.inr (Or.inl ⟨hoom, hoom_sf⟩)
    | step _ hstep _ =>
      have hrun := Arm64.Step.status_running hstep
      rw [hoom] at hrun; contradiction
  | @step a b c hstep1 _ ih =>
    intro s hs
    cases hs with
    | refl =>
      by_cases hpc : a.pc = t
      · exact Or.inl ⟨hpc, Arm64.Step.status_running hstep1, trivial⟩
      · exact Or.inr (Or.inr ⟨hpc, Arm64.Step.status_running hstep1⟩)
    | step _ hstep2 hrest2 =>
      cases Step.deterministic hstep1 hstep2
      exact ih hoom hoom_sf s hrest2

/-- Total correctness (`reaches_pc`) implies `safe_until_pc` with a trivial postcondition: if
    execution reaches `t` running (or terminates in `.OutOfMemory` satisfying `oom`), then no state
    before the first visit to `t` faults. -/
theorem safe_until_pc_of_reaches_pc {prog : Program} {t : BitVec 64} {s0 : State}
    {post oom : State → Prop} (h : reaches_pc prog t s0 post oom) :
    safe_until_pc prog t s0 (fun _ => True) oom := by
  intro hL
  rcases h hL with ⟨sf, hsteps, ⟨hpc, hrun, _⟩ | ⟨hoom, hoom_sf⟩⟩
  · obtain ⟨sm, hsm, hsm_pc, hrest⟩ := hsteps.toStepsUntilPC hpc
    have hsm_run : sm.status = .Running := by
      cases hrest with
      | refl => exact hrun
      | step hstep _ => exact Arm64.Step.status_running hstep
    exact safe_until_pc_of_stepsUntilPC hsm hsm_pc hsm_run trivial hL
  · exact safe_until_pc_of_steps_oom hsteps hoom hoom_sf


/-! ## `safe_reaches` and `safe_subroutine_ok` Rules -/

/-- Every total-correctness subroutine proof (`subroutine_ok`) weakens to partial correctness
    and memory safety (`safe_subroutine_ok`) with the same `Spec`. -/
theorem _root_.Arm64.subroutine_ok.to_safe {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry_pc spec) :
    safe_subroutine_ok prog entry_pc spec := by
  intro x R s0 h_entry h_pre hL
  exact Or.inl (reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R s0 h_entry.1 h_entry.2.1 h_pre h_entry.2.2) hL)

/-- From `subroutine_ok prog entry spec` and the AAPCS64 entry conditions, execution reaches an
    outcome state `sf` (`SubroutineOutcome spec x R s0 sf`) and every state `t` reachable from
    `s0` is either `.Running` (prior to `sf`) or reachable from `sf` (`Steps prog sf t`). -/
theorem _root_.Arm64.subroutine_ok.no_fault_before_outcome {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem) :
    ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t := by
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.mp (subroutine_ok_iff.mp hok x R s0 hpc hrun hpre hsp) hL
  exact ⟨sf, hsteps, hout, fun _ ht => Steps.running_or_steps_of hsteps ht⟩

/-- From `raw_subroutine_ok prog entry spec` and the entry conditions, execution reaches an
    outcome state `sf` (`SubroutineOutcome spec x R s0 sf`) and every state `t` reachable from
    `s0` is either `.Running` (prior to `sf`) or reachable from `sf` (`Steps prog sf t`). -/
theorem _root_.Arm64.raw_subroutine_ok.no_fault_before_outcome {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (hok : raw_subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hL : prog.CodeLoaded s0.mem) :
    ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t := by
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.mp (raw_subroutine_ok_iff.mp hok x R s0 hpc hrun hpre) hL
  exact ⟨sf, hsteps, hout, fun _ ht => Steps.running_or_steps_of hsteps ht⟩

/-- Corollary of `subroutine_ok.no_fault_before_outcome` for the `Returned` disjunct (when the
    specification forbids panic, exit, and OOM, which are the `Spec` defaults): execution reaches
    a normal return state `sf` (`Returned s0 sf`, `CallingConventionPreserved s0 sf`,
    `sf.mem ⊨ spec.post x s0 sf ∗ R`) and every state `t` reachable from `s0` is either `.Running`
    (up to and including `sf`, since `sf.status = .Running`) or reachable from `sf`. -/
theorem _root_.Arm64.subroutine_ok.no_fault_before_return {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∃ sf, Steps prog s0 sf ∧
      Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t := by
  obtain ⟨sf, hsteps, hout, hsafe⟩ :=
    subroutine_ok.no_fault_before_outcome hok x R s0 hpc hrun hpre hsp hL
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, hret, hcc, hpost, hsafe⟩
  · rw [h_noPanic] at hp; exact absurd hp not_satisfies_false_sepConj
  · rw [h_noExit] at he; exact absurd he not_satisfies_false_sepConj
  · rw [h_noOom] at hoom; exact absurd hoom not_satisfies_false_sepConj

/-- Corollary of `raw_subroutine_ok.no_fault_before_outcome` for the `Returned` disjunct (when the
    specification forbids panic, exit, and OOM): execution reaches a normal return state `sf` and
    every state `t` reachable from `s0` is either `.Running` or reachable from `sf`. -/
theorem _root_.Arm64.raw_subroutine_ok.no_fault_before_return {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (hok : raw_subroutine_ok prog entry spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h_noPanic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noExit : ∀ x c s0 sf, spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (h_noOom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    ∃ sf, Steps prog s0 sf ∧
      Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
      ∀ t, Steps prog s0 t → t.status = .Running ∨ Steps prog sf t := by
  obtain ⟨sf, hsteps, hout, hsafe⟩ :=
    raw_subroutine_ok.no_fault_before_outcome hok x R s0 hpc hrun hpre hL
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, hret, hcc, hpost, hsafe⟩
  · rw [h_noPanic] at hp; exact absurd hp not_satisfies_false_sepConj
  · rw [h_noExit] at he; exact absurd he not_satisfies_false_sepConj
  · rw [h_noOom] at hoom; exact absurd hoom not_satisfies_false_sepConj

/-- A total-correctness `subroutine_ok` proof (with unsatisfiable `onPanic` and `onExit`) implies
    that the subroutine never faults before its first visit to `lr`. -/
theorem _root_.Arm64.subroutine_ok.safe {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry_pc spec)
    (x : α) (R : SepProp) {s0 : State} (h_entry : AapcsEntry s0 entry_pc)
    (h_pre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he) :
    safe_until_pc prog (s0.readReg64 Reg.lr) s0 (fun _ => True)
      (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R) :=
  safe_until_pc_of_reaches_pc
    (subroutine_ok_apply_full h x R h_entry.1 h_entry.2.1 h_pre h_entry.2.2 h_no_panic h_no_exit)

/-- Introduction rule for `safe_subroutine_ok` from a pointwise `safe_reaches` proof. -/
theorem safe_subroutine_ok.intro {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ x R s0, AapcsEntry s0 entry_pc → (s0.mem ⊨ spec.pre x s0 ∗ R) →
      safe_reaches prog s0 (SubroutineOutcome spec x R s0)) :
    safe_subroutine_ok prog entry_pc spec := h


/-! ## Step-Indexed Weakest Precondition (`wp_idx` and `SepWP_idx`) -/

/-- Step-indexed weakest precondition for partial correctness & recursion.
    At each step `n + 1`, either `stop s ∧ Q s` holds, or `¬ stop s` holds and `s` is `.Running`,
    can take a `Step` (so it has not faulted or halted), and every successor satisfies
    `wp_idx prog stop Q n`. -/
def wp_idx (prog : Program) (stop : State → Prop) (Q : State → Prop) : Nat → State → Prop
  | 0,     _ => True
  | n + 1, s =>
    (stop s ∧ Q s) ∨
    (¬ stop s ∧ s.status = .Running ∧ (∃ s', Step prog s s') ∧
      ∀ s', Step prog s s' → wp_idx prog stop Q n s')

/-- Framed separation-logic step-indexed weakest precondition. -/
def SepWP_idx (prog : Program) (stop : State → Prop) (n : Nat) (s : State) (P : SepProp)
    (post : State → SepProp → Prop) : Prop :=
  ∀ R : SepProp, (s.mem ⊨ P ∗ R) → prog.CodeLoaded s.mem →
    wp_idx prog stop (fun sf => ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ post sf P_f) n s


/-! ## Sentinel-LR First-Stop Bridge (`StepsUntil (SubroutineStop s0)`) -/

/-- If `s0.readReg64 Reg.lr = s0.pc` at a `.Running` entry state `s0`, then `Returned s0 s0`
    (and therefore `SubroutineStop s0 s0`) already holds at step 0. Consequently, any
    `StepsUntil prog (SubroutineStop s0) s0 sf` derivation must stop in 0 steps (`sf = s0`).
    This explains why `reaches_outcome` in `Arm64.Trusted.Spec.Hoare` uses `Steps` while
    `subroutine_ok` places no constraint on `s0.readReg64 Reg.lr`. -/
theorem stepsUntil_subroutineStop_eq_self_of_lr_eq_pc
    {prog : Program} {s0 sf : State}
    (hrun : s0.status = .Running)
    (hlr : s0.readReg64 Reg.lr = s0.pc)
    (hsteps : StepsUntil prog (SubroutineStop s0) s0 sf) :
    sf = s0 := by
  have hstop0 : SubroutineStop s0 s0 := Or.inl ⟨hlr.symm, rfl, hrun⟩
  cases hsteps with
  | refl _ => rfl
  | step hnot _ _ => exact False.elim (hnot hstop0)

/-- If `s0.readReg64 Reg.lr` is an unmapped/non-executable return sentinel at `sm`
    (`prog.fetchMem sm.mem (s0.readReg64 Reg.lr) = none` and
    `prog.externAt? (s0.readReg64 Reg.lr) = none`), any `Steps prog sm sf'` starting from a
    `SubroutineStop s0 sm` state and ending in a non-`.Halted` state `sf'` must have `sf' = sm`. -/
theorem steps_eq_of_subroutineStop_sentinel_lr {prog : Program} {s0 sm sf' : State}
    (h_fetch : prog.fetchMem sm.mem (s0.readReg64 Reg.lr) = none)
    (h_ext : prog.externAt? (s0.readReg64 Reg.lr) = none)
    (hsm_stop : SubroutineStop s0 sm)
    (h_rest : Steps prog sm sf')
    (h_nhalt : sf'.status ≠ .Halted) :
    sf' = sm := by
  cases h_rest with
  | refl => rfl
  | @step _ s2 _ hstep hrest2 =>
    have hsm_run : sm.status = .Running := hstep.running_of_step
    rcases hsm_stop with ⟨hpc, _, _⟩ | hpan | ⟨code, hex⟩ | hoom
    · cases hstep with
      | exec _ hf =>
        rw [hpc, h_fetch] at hf
        contradiction
      | halt_unmapped _ _ _ =>
        have heq := hrest2.eq_of_halted rfl
        subst heq
        exact False.elim (h_nhalt rfl)
      | extern _ he _ _ =>
        rw [hpc, h_ext] at he
        contradiction
      | extern_fault _ he _ =>
        rw [hpc, h_ext] at he
        contradiction
    · rw [hsm_run] at hpan; contradiction
    · rw [hsm_run] at hex; contradiction
    · rw [hsm_run] at hoom; contradiction

/-- Every `SubroutineOutcome` state satisfies `SubroutineStop`. -/
theorem _root_.Arm64.SubroutineOutcome.to_subroutineStop {α : Type} {spec : Spec α} {x : α}
    {R : SepProp} {s0 sf : State} (hout : SubroutineOutcome spec x R s0 sf) :
    SubroutineStop s0 sf := by
  rcases hout with ⟨hret, _, _⟩ | ⟨hpan, _⟩ | ⟨code, hex, _⟩ | ⟨hoom, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex⟩))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- No `SubroutineOutcome` state has `status = .Halted`. -/
theorem _root_.Arm64.SubroutineOutcome.status_ne_halted {α : Type} {spec : Spec α} {x : α}
    {R : SepProp} {s0 sf : State} (hout : SubroutineOutcome spec x R s0 sf) :
    sf.status ≠ .Halted := by
  rcases hout with ⟨⟨_, _, hrun⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨code, hex, _⟩ | ⟨hoom, _⟩
  · simp [hrun]
  · simp [hpan]
  · simp [hex]
  · simp [hoom]

/-- When `s0.readReg64 Reg.lr` is a universal-fetch-none return sentinel
    (`∀ m, prog.fetchMem m (s0.readReg64 Reg.lr) = none` in every memory `m`, and
    `prog.externAt? (s0.readReg64 Reg.lr) = none`), any `Steps prog s0 sf` reaching a
    `SubroutineOutcome` state `sf` is the unique first `SubroutineStop s0` state along the
    trace (`StepsUntil prog (SubroutineStop s0) s0 sf`). -/
theorem stepsUntil_of_steps_subroutineOutcome_sentinel_lr {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {R : SepProp} {s0 sf : State}
    (h_fetch : ∀ m, prog.fetchMem m (s0.readReg64 Reg.lr) = none)
    (h_ext : prog.externAt? (s0.readReg64 Reg.lr) = none)
    (h_steps : Steps prog s0 sf)
    (hout : SubroutineOutcome spec x R s0 sf) :
    StepsUntil prog (SubroutineStop s0) s0 sf := by
  obtain ⟨sm, h_until, hsm_stop, h_rest⟩ := h_steps.toStepsUntil hout.to_subroutineStop
  have heq := steps_eq_of_subroutineStop_sentinel_lr (h_fetch sm.mem) h_ext hsm_stop h_rest
    hout.status_ne_halted
  exact heq ▸ h_until

/-- Sentinel-LR first-stop bridge: from `subroutine_ok prog entry_pc spec`, whenever the
    caller's return address `s0.readReg64 Reg.lr` is a universal-fetch-none return sentinel
    (`∀ m, prog.fetchMem m (s0.readReg64 Reg.lr) = none` in every memory `m`, and
    `prog.externAt? (s0.readReg64 Reg.lr) = none`), execution reaches a `SubroutineOutcome`
    state `sf` at the first `SubroutineStop s0` (`StepsUntil prog (SubroutineStop s0) s0 sf`). -/
theorem _root_.Arm64.subroutine_ok.stepsUntil_of_sentinel_lr {α : Type} {prog : Program}
    {entry_pc : BitVec 64} {spec : Spec α} (hok : subroutine_ok prog entry_pc spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem)
    (h_fetch : ∀ m, prog.fetchMem m (s0.readReg64 Reg.lr) = none)
    (h_ext : prog.externAt? (s0.readReg64 Reg.lr) = none) :
    ∃ sf : State, StepsUntil prog (SubroutineStop s0) s0 sf ∧ SubroutineOutcome spec x R s0 sf := by
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.mp (subroutine_ok_iff.mp hok x R s0 hpc hrun hpre hsp) hL
  exact ⟨sf, stepsUntil_of_steps_subroutineOutcome_sentinel_lr h_fetch h_ext hsteps hout, hout⟩

/-- Sentinel-LR first-stop bridge for `raw_subroutine_ok`. -/
theorem _root_.Arm64.raw_subroutine_ok.stepsUntil_of_sentinel_lr {α : Type} {prog : Program}
    {entry_pc : BitVec 64} {spec : Spec α} (hok : raw_subroutine_ok prog entry_pc spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h_fetch : ∀ m, prog.fetchMem m (s0.readReg64 Reg.lr) = none)
    (h_ext : prog.externAt? (s0.readReg64 Reg.lr) = none) :
    ∃ sf : State, StepsUntil prog (SubroutineStop s0) s0 sf ∧ SubroutineOutcome spec x R s0 sf := by
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.mp (raw_subroutine_ok_iff.mp hok x R s0 hpc hrun hpre) hL
  exact ⟨sf, stepsUntil_of_steps_subroutineOutcome_sentinel_lr h_fetch h_ext hsteps hout, hout⟩

/-- Unaligned-LR corollary of `subroutine_ok.stepsUntil_of_sentinel_lr`: any 4-byte-unaligned
    return address `(s0.readReg64 Reg.lr).toNat % 4 ≠ 0` (such as `1#64` or `prog.base + 1#64`
    when `prog.base` is 4-byte aligned) has `prog.fetchMem m (s0.readReg64 Reg.lr) = none` in
    every memory `m`. -/
theorem _root_.Arm64.subroutine_ok.stepsUntil_of_unaligned_lr {α : Type} {prog : Program}
    {entry_pc : BitVec 64} {spec : Spec α} (hok : subroutine_ok prog entry_pc spec)
    (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem)
    (h_unalign : (s0.readReg64 Reg.lr).toNat % 4 ≠ 0)
    (h_ext : prog.externAt? (s0.readReg64 Reg.lr) = none) :
    ∃ sf : State, StepsUntil prog (SubroutineStop s0) s0 sf ∧ SubroutineOutcome spec x R s0 sf :=
  hok.stepsUntil_of_sentinel_lr x R s0 hpc hrun hpre hsp hL
    (fun m => by simp [Program.fetchMem, h_unalign, ite_self]) h_ext

end ProofLib
