/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP.Structural
public import ProofLib.Hoare.SafeReaches
import Arm64.Trusted.Spec.SepLogic
import Arm64.Trusted.Spec.Hoare

/-!
# Framed Partial-Correctness Weakest Precondition

Defines `SafeSepWP` and `SafeSepWP1` over `safe_reaches` for proving `safe_subroutine_ok` (partial
correctness with memory safety). Provides structural rules, bridges from total `SepWP` segments,
framed partial and total subroutine call rules, measure-free loop induction (`SafeSepWP.loop`), and
entry/return combinators (`safe_subroutine_ok_of_safeSepWP`, `SafeSepWP.ret_of_sepWP`).
-/

set_option autoImplicit false

namespace ProofLib

open Arm64

@[expose] public section

/-! ## Judgments -/

/-- Framed partial-correctness weakest precondition: for every frame `R` with `s.mem ⊨ P ∗ R`,
    execution of `prog` from `s` either reaches a state `sf` with a spatial context `P_f` such that
    `sf.mem ⊨ P_f ∗ R` and `Q sf P_f`, or runs forever without faulting (`safe_reaches`). -/
def SafeSepWP (prog : Program) (s : State) (P : SepProp) (Q : State → SepProp → Prop) : Prop :=
  ∀ R : SepProp, (s.mem ⊨ P ∗ R) →
    safe_reaches prog s (fun sf => ∃ P_f : SepProp, (sf.mem ⊨ P_f ∗ R) ∧ Q sf P_f)

/-- `SafeSepWP` that first takes at least one machine step (used for loop bodies, where a
    zero-length iteration must be ruled out). -/
def SafeSepWP1 (prog : Program) (s : State) (P : SepProp) (Q : State → SepProp → Prop) : Prop :=
  ∀ R : SepProp, (s.mem ⊨ P ∗ R) → prog.CodeLoaded s.mem →
    ∃ s1, Step prog s s1 ∧
      safe_reaches prog s1 (fun sf => ∃ P_f : SepProp, (sf.mem ⊨ P_f ∗ R) ∧ Q sf P_f)

/-! ## Structural rules -/

/-- The postcondition already holds at the current state. -/
theorem SafeSepWP.done {prog : Program} {s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (h : Q s P) : SafeSepWP prog s P Q :=
  fun _ hm => safe_reaches.done ⟨P, hm, h⟩

/-- Postcondition weakening. -/
theorem SafeSepWP.mono {prog : Program} {s : State} {P : SepProp} {Q Q' : State → SepProp → Prop}
    (h : SafeSepWP prog s P Q) (himp : ∀ sf Pf, Q sf Pf → Q' sf Pf) : SafeSepWP prog s P Q' :=
  fun R hm => (h R hm).mono fun _ ⟨Pf, hmf, hq⟩ => ⟨Pf, hmf, himp _ _ hq⟩

/-- Precondition strengthening by separation-logic entailment. -/
theorem SafeSepWP.weaken_pre {prog : Program} {s : State} {P P' : SepProp}
    {Q : State → SepProp → Prop} (h : SafeSepWP prog s P Q) (hent : P' ⊢ P) :
    SafeSepWP prog s P' Q :=
  fun R hm => h R (Satisfies.mono (sepConj_mono_left hent) hm)

/-- Eliminate a pure conjunct `⌜φ⌝` at the head of the spatial context into a hypothesis. -/
theorem SafeSepWP.pure_elim {prog : Program} {s : State} {φ : Prop} {P : SepProp}
    {Q : State → SepProp → Prop} (h : φ → SafeSepWP prog s P Q) :
    SafeSepWP prog s (⌜φ⌝ ∗ P) Q := by
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

/-- Eliminate an existential `∃∗ a, P a` spatial context into a universally quantified variable. -/
theorem SafeSepWP.exists_elim {β : Sort _} {prog : Program} {s : State} {P : β → SepProp}
    {Q : State → SepProp → Prop} (h : ∀ a, SafeSepWP prog s (P a) Q) :
    SafeSepWP prog s (∃∗ a, P a) Q := by
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

/-- Sequential composition: a partial run to `Mid` continued by a partial run from every
    reached `Mid` state. -/
theorem SafeSepWP.bind {prog : Program} {s : State} {P : SepProp}
    {Mid Q : State → SepProp → Prop} (h1 : SafeSepWP prog s P Mid)
    (h2 : ∀ sm Pm, Mid sm Pm → SafeSepWP prog sm Pm Q) : SafeSepWP prog s P Q :=
  fun R hm => (h1 R hm).bind fun _ _ ⟨Pm, hmm, hmid⟩ => h2 _ Pm hmid R hmm

/-- Postcondition weakening for `SafeSepWP1`. -/
theorem SafeSepWP1.mono {prog : Program} {s : State} {P : SepProp}
    {Q Q' : State → SepProp → Prop}
    (h : SafeSepWP1 prog s P Q) (himp : ∀ sf Pf, Q sf Pf → Q' sf Pf) : SafeSepWP1 prog s P Q' := by
  intro R hm hL
  obtain ⟨s1, hst, hs⟩ := h R hm hL
  exact ⟨s1, hst, hs.mono fun _ ⟨Pf, hmf, hq⟩ => ⟨Pf, hmf, himp _ _ hq⟩⟩

/-- Forget the "at least one step" guarantee. -/
theorem SafeSepWP1.toSafeSepWP {prog : Program} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop} (h : SafeSepWP1 prog s P Q) : SafeSepWP prog s P Q := by
  intro R hm hL
  obtain ⟨s1, hst, hs⟩ := h R hm hL
  exact safe_reaches.step hst hs hL

/-! ## Bridges from total `SepWP` segments -/

/-- Compose a total `SepWP` segment to `mid` with a `SafeSepWP` continuation from the reached
    state (`oom = ⌜False⌝` rules out out-of-memory termination). -/
theorem SafeSepWP.of_sepWP {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sf Pf => SafeSepWP prog sf Pf Q)) : SafeSepWP prog s P Q := by
  intro R hm hL
  obtain ⟨sf, hsteps, hcase⟩ := h R hm hL
  rcases hcase with ⟨_, _, Pf, hmf, hsafe⟩ | ⟨_, hoom⟩
  · exact safe_reaches.steps hsteps (hsafe R hmf) hL
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Total `SepWP` segment that may run out of memory: out-of-memory states satisfying
    `oom sf ∗ R` must be accepted by `Q` (`hoom`). -/
theorem SafeSepWP.of_sepWP_oom {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sf Pf => SafeSepWP prog sf Pf Q) oom)
    (hoom : ∀ R sf, sf.status = .OutOfMemory → (sf.mem ⊨ oom sf ∗ R) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf) : SafeSepWP prog s P Q := by
  intro R hm hL
  obtain ⟨sf, hsteps, hcase⟩ := h R hm hL
  rcases hcase with ⟨_, _, Pf, hmf, hsafe⟩ | ⟨hst, hoomR⟩
  · exact safe_reaches.steps hsteps (hsafe R hmf) hL
  · exact safe_reaches.steps hsteps (safe_reaches.done (hoom R sf hst hoomR)) hL

/-- A total `SepWP` run whose postcondition implies `Q`. -/
theorem SafeSepWP.of_total {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop} (h : SepWP prog mid s P (fun sf Pf => Q sf Pf)) :
    SafeSepWP prog s P Q := by
  intro R hm hL
  obtain ⟨sf, hsteps, hcase⟩ := h R hm hL
  rcases hcase with ⟨_, _, Pf, hmf, hq⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨sf, hsteps, Pf, hmf, hq⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- `SafeSepWP.of_sepWP` for loop bodies: when `s.pc ≠ mid`, the `SepWP` run takes at least one
    step, giving `SafeSepWP1`. -/
theorem SafeSepWP1.of_sepWP {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop} (hne : s.pc ≠ mid)
    (h : SepWP prog mid s P (fun sf Pf => SafeSepWP prog sf Pf Q)) : SafeSepWP1 prog s P Q := by
  intro R hm hL
  obtain ⟨sf, hsteps, hcase⟩ := h R hm hL
  rcases hcase with ⟨hpc, _, Pf, hmf, hsafe⟩ | ⟨_, hoom⟩
  · cases hsteps with
    | refl => exact absurd hpc hne
    | step hst hrest => exact ⟨_, hst, safe_reaches.steps hrest (hsafe R hmf)⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## Calls -/

/-- Framed partial call rule: at a call site `s` (`pc = entry`, `.Running`, aligned `sp`,
    `lr = ret_pc`) whose spatial context `P` splits into `spec.pre x s` and a caller frame `F`,
    compose a `safe_subroutine_ok` callee with continuation `hnext` upon return. Panic, exit, and
    out-of-memory callee outcomes are discharged via `h_panic`, `h_exit`, and `h_oom` (defaulting
    to `⌜False⌝` elimination). -/
theorem SafeSepWP.call_subroutine_frame {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hcall : safe_subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp} {Q : State → SepProp → Prop} {ret_pc : BitVec 64}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SafeSepWP prog sf (spec.post x s sf ∗ F) Q)
    (h_panic : ∀ R sf, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ (F ∗ R)) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ hp; exact False.elim (not_satisfies_false_sepConj hp))
    (h_exit : ∀ R code sf, sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R)) → ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ _ he; exact False.elim (not_satisfies_false_sepConj he))
    (h_oom : ∀ R sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ ho; exact False.elim (not_satisfies_false_sepConj ho)) :
    SafeSepWP prog s P Q := by
  intro R hm
  refine safe_reaches.call hcall x (F ∗ R) ⟨hpc, hrun, hsp_align⟩ (hpre R hm) ?_
  intro sf _ hout
  rcases hout with ⟨⟨hpc_sf, hsp, hrun_sf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨hst, hp⟩ | ⟨code, hst, he⟩ |
      ⟨hst, ho⟩
  · rw [← sepConj_assoc] at hpost
    exact hnext sf (hpc_sf.trans hlr) hrun_sf hsp hcs R hpost
  · exact safe_reaches.done (h_panic R sf hst hp)
  · exact safe_reaches.done (h_exit R code sf hst he)
  · exact safe_reaches.done (h_oom R sf hst ho)

/-- `SafeSepWP.call_subroutine_frame` for a total-correctness (`subroutine_ok`) callee. -/
theorem SafeSepWP.call_subroutine_frame_total {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp} {Q : State → SepProp → Prop} {ret_pc : BitVec 64}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SafeSepWP prog sf (spec.post x s sf ∗ F) Q)
    (h_panic : ∀ R sf, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ (F ∗ R)) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ hp; exact False.elim (not_satisfies_false_sepConj hp))
    (h_exit : ∀ R code sf, sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R)) → ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ _ he; exact False.elim (not_satisfies_false_sepConj he))
    (h_oom : ∀ R sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ ho; exact False.elim (not_satisfies_false_sepConj ho)) :
    SafeSepWP prog s P Q :=
  SafeSepWP.call_subroutine_frame hcall.to_safe hpc hrun hsp_align hlr hpre hnext
    h_panic h_exit h_oom

/-! ## Loops without a termination measure -/

/-- Loop rule without a termination measure: if from every state satisfying `Inv` the body takes
    at least one step (`SafeSepWP1`) and partially reaches `Inv` or the exit `Q`, then execution
    from an `Inv` state partially reaches `Q` or runs forever without faulting. -/
theorem SafeSepWP.loop {prog : Program} (Inv : State → SepProp → Prop)
    {Q : State → SepProp → Prop}
    (hbody : ∀ st Pst, Inv st Pst → SafeSepWP1 prog st Pst (fun sf Pf => Inv sf Pf ∨ Q sf Pf))
    {s : State} {P : SepProp} (h0 : Inv s P) : SafeSepWP prog s P Q := by
  intro R hm
  refine safe_reaches.loop (I := fun st => ∃ Pst, (st.mem ⊨ Pst ∗ R) ∧ Inv st Pst)
    (fun st ⟨Pst, hmst, hinv⟩ hL => ?_) ⟨P, hm, h0⟩
  obtain ⟨s1, hst, hs⟩ := hbody st Pst hinv R hmst hL
  exact ⟨s1, hst, hs.mono fun _ ⟨Pf, hmf, hq⟩ =>
    hq.elim (fun hi => Or.inl ⟨Pf, hmf, hi⟩) (fun hq => Or.inr ⟨Pf, hmf, hq⟩)⟩

/-! ## Entry and return -/

/-- Entry rule (partial-correctness counterpart to `subroutine_ok_of_sepWP_init`): establish
    `safe_subroutine_ok` from a `SafeSepWP` starting at `s0` whose postcondition yields
    `SubroutineOutcome spec x R s0 sf`. -/
theorem safe_subroutine_ok_of_safeSepWP {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SafeSepWP prog s0 P_init (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → SubroutineOutcome spec x R s0 sf)) :
    safe_subroutine_ok prog entry_pc spec := by
  intro x R s0 hentry hpre
  obtain ⟨P_init, hm0, hsafe⟩ := h x R s0 hentry.1 hentry.2.1 hpre hentry.2.2
  exact (hsafe R hm0).mono fun _ ⟨_, hmf, hout⟩ => hout hmf

/-- Return closer for `safe_subroutine_ok_of_safeSepWP`: lift a final total `SepWP` segment to
    `s0.readReg64 Reg.lr` (matching `subroutine_ok_of_sepWP_init` and `wp_done`) into `SafeSepWP`,
    propagating `spec.onOom`. -/
theorem SafeSepWP.ret_of_sepWP {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} {P : SepProp}
    (h : SepWP prog (s0.readReg64 Reg.lr) s P (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf)) :
    SafeSepWP prog s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → SubroutineOutcome spec x R s0 sf) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hcase⟩ := h R' hm hL
  rcases hcase with ⟨hpc, hrun, Pf, hmf, hpost, hsp, hcs⟩ | ⟨hst, hoom⟩
  · exact Or.inl ⟨sf, hsteps, Pf, hmf, fun hR =>
      Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hR⟩⟩
  · exact Or.inl ⟨sf, hsteps, spec.onOom x s0 sf, hoom, fun hR =>
      Or.inr (Or.inr (Or.inr ⟨hst, hR⟩))⟩

end -- @[expose] public section

end ProofLib
