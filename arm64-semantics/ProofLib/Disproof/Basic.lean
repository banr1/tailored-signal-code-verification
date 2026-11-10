/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Safety
public import ProofLib.Invariant
public import ProofLib.SepLogic
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Determinism and Refutation Combinators

Provides multi-step trace determinism lemmas, the unaligned return-address sentinel guard
`HaltsAtReturn`, and combinators for refuting `safe_subroutine_ok` and `subroutine_ok` via
exceptions, postcondition violations, panic postcondition violations, or frame-canary corruption.
-/

@[expose] public section

namespace ProofLib.Disproof

open Arm64 ProofLib

/-! ## Terminal States and Determinism of `Steps` -/

/-- A machine state is terminal when its execution status is no longer `.Running`
    (i.e. `.Halted`, `.Exception msg`, `.Panicked`, or `.Exited code`). -/
def _root_.Arm64.State.isTerminal (s : State) : Prop :=
  s.status ≠ .Running

theorem isTerminal_of_exception {s : State} {msg : String} (h : s.status = .Exception msg) :
    s.isTerminal := by
  intro hrun; rw [h] at hrun; cases hrun

theorem isTerminal_of_panicked {s : State} (h : s.status = .Panicked) :
    s.isTerminal := by
  intro hrun; rw [h] at hrun; cases hrun

theorem isTerminal_of_halted {s : State} (h : s.status = .Halted) :
    s.isTerminal := by
  intro hrun; rw [h] at hrun; cases hrun

theorem Step.not_isTerminal {prog : Program} {s s' : State} (h : Step prog s s') :
    ¬ s.isTerminal := by
  intro hterm
  exact hterm (Arm64.Step.status_running h)

theorem Steps.eq_of_isTerminal {prog : Program} {s s' : State}
    (hsteps : Steps prog s s') (hterm : s.isTerminal) : s' = s := by
  cases hsteps with
  | refl => rfl
  | step hstep _ => exact absurd hterm (Step.not_isTerminal hstep)

/-- Comparing a `StepsUntil prog stop s0 sf` run with an arbitrary `Steps prog s0 s_out` run:
    either `s_out` is reached at or after `sf` (`Steps prog sf s_out`), or `s_out` occurs
    strictly before `sf` on the trace, in which case `¬ stop s_out ∧ s_out.status = .Running`. -/
theorem StepsUntil.compare_steps {prog : Program} {stop : State → Prop} {s0 sf s_out : State}
    (h1 : StepsUntil prog stop s0 sf) (h2 : Steps prog s0 s_out) :
    Steps prog sf s_out ∨ (¬ stop s_out ∧ s_out.status = .Running) := by
  induction h1 with
  | refl => exact Or.inl h2
  | step hnstop hstep1 _ ih =>
    cases h2 with
    | refl => exact Or.inr ⟨hnstop, Arm64.Step.status_running hstep1⟩
    | step hstep2 hrest2 =>
      cases Step.deterministic hstep1 hstep2
      exact ih hrest2

/-! ## Return-Address Sentinel Guard (`HaltsAtReturn`) -/

theorem SubroutineOutcome.toSubroutineStop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hpan, _⟩ | ⟨code, hexit, _⟩ | ⟨hoom, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hexit⟩))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- A return address `lr := s0.readReg64 .lr` halts immediately upon return when `lr` is not an
    external hook (`prog.externAt? lr = none`) and has no executable instruction in any
    `CodeLoaded` memory (`∀ m, prog.CodeLoaded m → prog.fetchMem m lr = none`).
    Using an unaligned return sentinel such as `lr = 1#64` in counterexample entry states
    discharges this automatically via `HaltsAtReturn.of_unaligned`. -/
def HaltsAtReturn (prog : Program) (s0 : State) : Prop :=
  prog.externAt? (s0.readReg64 Reg.lr) = none ∧
  ∀ m, prog.CodeLoaded m → prog.fetchMem m (s0.readReg64 Reg.lr) = none

/-- Any 4-byte-unaligned return address (such as `1#64`) has `fetchMem = none` in every memory,
    so `HaltsAtReturn` reduces to `prog.externAt? lr = none`. -/
theorem HaltsAtReturn.of_unaligned {prog : Program} {s0 : State}
    (hextern : prog.externAt? (s0.readReg64 Reg.lr) = none)
    (hunalign : (s0.readReg64 Reg.lr).toNat % 4 ≠ 0) :
    HaltsAtReturn prog s0 := by
  refine ⟨hextern, fun m _ => ?_⟩
  unfold Program.fetchMem
  simp [hextern, hunalign]

theorem Step.eq_halted_of_no_fetch {prog : Program} {s s' : State}
    (hextern : prog.externAt? s.pc = none)
    (hfetch : prog.fetchMem s.mem s.pc = none)
    (hstep : Step prog s s') :
    s' = { s with status := .Halted } := by
  cases hstep with
  | exec _ hfm => rw [hfetch] at hfm; cases hfm
  | extern _ hex _ _ => rw [hextern] at hex; cases hex
  | extern_fault _ hex _ => rw [hextern] at hex; cases hex
  | halt_unmapped => rfl

theorem Steps.eq_or_halted_of_no_fetch {prog : Program} {s sf : State}
    (hextern : prog.externAt? s.pc = none)
    (hfetch : prog.fetchMem s.mem s.pc = none)
    (hsteps : Steps prog s sf) :
    sf = s ∨ sf = { s with status := .Halted } := by
  cases hsteps with
  | refl => exact Or.inl rfl
  | step hstep hrest =>
    have hs' := Step.eq_halted_of_no_fetch hextern hfetch hstep
    subst hs'
    have hterm : ({ s with status := ExecStatus.Halted } : State).isTerminal :=
      isTerminal_of_halted rfl
    exact Or.inr (Steps.eq_of_isTerminal hrest hterm)

private theorem toStepsUntil_returned_aux {prog : Program} {s0 s sf : State}
    (hsteps : Steps prog s sf) (hcs : prog.CodeLoaded s.mem)
    (hlr : HaltsAtReturn prog s0) (hnot_halt : sf.status ≠ .Halted) :
    StepsUntil prog (Returned s0) s sf := by
  induction hsteps with
  | refl => exact .refl _
  | @step a b c hstep hrest ih =>
    refine .step ?_ hstep (ih (Step.codeLoaded hstep hcs) hnot_halt)
    intro hret
    have hextern : prog.externAt? a.pc = none := by rw [hret.1]; exact hlr.1
    have hfetch : prog.fetchMem a.mem a.pc = none := by rw [hret.1]; exact hlr.2 a.mem hcs
    have hb := Step.eq_halted_of_no_fetch hextern hfetch hstep
    subst hb
    have hc := Steps.eq_of_isTerminal hrest (isTerminal_of_halted rfl)
    subst hc
    exact hnot_halt rfl

/-- When `HaltsAtReturn prog s0` holds and `sf.status ≠ .Halted`, any `Steps prog s0 sf` run
    from a `CodeLoaded` state `s0` never visits a `Returned s0` state strictly before `sf`,
    and therefore lifts to `StepsUntil prog (Returned s0) s0 sf`. -/
theorem Steps.toStepsUntil_returned_of_haltsAtReturn {prog : Program} {s0 sf : State}
    (hsteps : Steps prog s0 sf) (hcode : prog.CodeLoaded s0.mem)
    (hlr : HaltsAtReturn prog s0) (hnot_halt : sf.status ≠ .Halted) :
    StepsUntil prog (Returned s0) s0 sf :=
  toStepsUntil_returned_aux hsteps hcode hlr hnot_halt

/-- If `StepsUntil prog (Returned s0) s0 sf` holds, then any `s_out` reachable from `s0`
    satisfying `SubroutineStop s0 s_out` must be reached at or after `sf` (`Steps prog sf s_out`). -/
theorem StepsUntil.steps_from_of_subroutineStop {prog : Program} {s0 sf s_out : State}
    (huntil : StepsUntil prog (Returned s0) s0 sf)
    (hsteps : Steps prog s0 s_out)
    (hstop : SubroutineStop s0 s_out) :
    Steps prog sf s_out := by
  rcases StepsUntil.compare_steps huntil hsteps with h | ⟨hnret, hrun⟩
  · exact h
  · rcases hstop with hret | hpan | ⟨code, hexit⟩ | hoom
    · exact absurd hret hnret
    · rw [hrun] at hpan; cases hpan
    · rw [hrun] at hexit; cases hexit
    · rw [hrun] at hoom; cases hoom

/-! ## Refuting `subroutine_ok` and `safe_subroutine_ok` via `.Exception` -/

/-- Refute `safe_subroutine_ok prog entry_pc spec` from a `StepsUntil prog (Returned s0) s0 sf`
    trace ending in `sf.status = .Exception msg` (requires no assumption on `s0.readReg64 .lr`). -/
theorem not_safe_subroutine_ok_of_stepsUntil_exception {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 sf : State} {msg : String}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (huntil : StepsUntil prog (Returned s0) s0 sf)
    (hexc : sf.status = .Exception msg) :
    ¬ safe_subroutine_ok prog entry_pc spec := by
  intro hsafe
  rcases hsafe x R s0 hentry hpre hcode with ⟨s_out, hsteps_out, hout⟩ | hinf
  · have hstop := SubroutineOutcome.toSubroutineStop hout
    have hpost_steps := StepsUntil.steps_from_of_subroutineStop huntil hsteps_out hstop
    have heq := Steps.eq_of_isTerminal hpost_steps (isTerminal_of_exception hexc)
    subst heq
    rcases hstop with ⟨_, _, hrun⟩ | hpan | ⟨_, hexit⟩ | hoom
    · rw [hexc] at hrun; cases hrun
    · rw [hexc] at hpan; cases hpan
    · rw [hexc] at hexit; cases hexit
    · rw [hexc] at hoom; cases hoom
  · have hrun := (hinf sf huntil.toSteps).1
    rw [hexc] at hrun; cases hrun

/-- Refute `safe_subroutine_ok prog entry_pc spec` by exhibiting `x : α`, `R : SepProp`,
    `s0 sf : State`, and `msg : String` such that:
    - `AapcsEntry s0 entry_pc`,
    - `prog.CodeLoaded s0.mem`,
    - `s0.mem ⊨ spec.pre x s0 ∗ R`,
    - `Steps prog s0 sf`, and `sf.status = .Exception msg`.
    The return-address guard `HaltsAtReturn prog s0` is auto-discharged when `s0.readReg64 .lr`
    is an unaligned sentinel such as `1#64`. -/
theorem not_safe_subroutine_ok_of_exception {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 sf : State} {msg : String}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hsteps : Steps prog s0 sf)
    (hexc : sf.status = .Exception msg)
    (hlr : HaltsAtReturn prog s0 := by
      first
      | exact HaltsAtReturn.of_unaligned (by decide) (by decide)
      | exact HaltsAtReturn.of_unaligned rfl (by decide)) :
    ¬ safe_subroutine_ok prog entry_pc spec := by
  have hnot_halt : sf.status ≠ .Halted := by rw [hexc]; intro h; cases h
  have huntil := Steps.toStepsUntil_returned_of_haltsAtReturn hsteps hcode hlr hnot_halt
  exact not_safe_subroutine_ok_of_stepsUntil_exception x R hentry hcode hpre huntil hexc

/-! ## Refuting `subroutine_ok` via Postcondition Violation or Frame Canary Corruption -/

/-- Refute `safe_subroutine_ok prog entry_pc spec` when a valid entry state `(x, R, s0)` reaches
    a `Returned s0 sf` state where `¬ (sf.mem ⊨ spec.post x s0 sf ∗ R)` (and `HaltsAtReturn prog s0`
    causes `sf` to halt after return, ruling out infinite `.Running` traces). -/
theorem not_safe_subroutine_ok_of_post_false {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 sf : State}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hsteps : Steps prog s0 sf)
    (hret : Returned s0 sf)
    (hpost_false : ¬ (sf.mem ⊨ spec.post x s0 sf ∗ R))
    (hlr : HaltsAtReturn prog s0 := by
      first
      | exact HaltsAtReturn.of_unaligned (by decide) (by decide)
      | exact HaltsAtReturn.of_unaligned rfl (by decide)) :
    ¬ safe_subroutine_ok prog entry_pc spec := by
  intro hsafe
  have hnot_halt : sf.status ≠ .Halted := by rw [hret.2.2]; intro h; cases h
  have huntil := Steps.toStepsUntil_returned_of_haltsAtReturn hsteps hcode hlr hnot_halt
  have hcsf : prog.CodeLoaded sf.mem := Steps.codeLoaded hsteps hcode
  have hextern : prog.externAt? sf.pc = none := by rw [hret.1]; exact hlr.1
  have hfetch : prog.fetchMem sf.mem sf.pc = none := by rw [hret.1]; exact hlr.2 sf.mem hcsf
  rcases hsafe x R s0 hentry hpre hcode with ⟨s_out, hsteps_out, hout⟩ | hinf
  · have hstop := SubroutineOutcome.toSubroutineStop hout
    have hfrom := StepsUntil.steps_from_of_subroutineStop huntil hsteps_out hstop
    rcases Steps.eq_or_halted_of_no_fetch hextern hfetch hfrom with rfl | hhalted
    · rcases hout with ⟨_, _, hpost⟩ | ⟨hpan, _⟩ | ⟨_, hexit, _⟩ | ⟨hoom, _⟩
      · exact hpost_false hpost
      · rw [hret.2.2] at hpan; cases hpan
      · rw [hret.2.2] at hexit; cases hexit
      · rw [hret.2.2] at hoom; cases hoom
    · subst hhalted
      rcases hstop with ⟨_, _, hrun⟩ | hpan | ⟨_, hexit⟩ | hoom
      · cases hrun
      · cases hpan
      · cases hexit
      · cases hoom
  · have hstep_halt : Step prog sf { sf with status := .Halted } :=
      Step.halt_unmapped hret.2.2 hfetch hextern
    have hsteps_halt : Steps prog s0 { sf with status := .Halted } :=
      hsteps.trans (.step hstep_halt (.refl _))
    have hrun := (hinf { sf with status := .Halted } hsteps_halt).1
    cases hrun

/-- Refute `subroutine_ok prog entry_pc spec` when execution reaches a terminal `.Panicked`
    state `sf` where `¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R)`. -/
theorem not_subroutine_ok_of_panic_post_false {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 sf : State}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hsteps : Steps prog s0 sf)
    (hpan : sf.status = .Panicked)
    (hpost_false : ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))
    (hlr : HaltsAtReturn prog s0 := by
      first
      | exact HaltsAtReturn.of_unaligned (by decide) (by decide)
      | exact HaltsAtReturn.of_unaligned rfl (by decide)) :
    ¬ subroutine_ok prog entry_pc spec := by
  intro hok
  have hnot_halt : sf.status ≠ .Halted := by rw [hpan]; intro h; cases h
  have huntil := Steps.toStepsUntil_returned_of_haltsAtReturn hsteps hcode hlr hnot_halt
  simp only [subroutine_ok_iff, reaches_outcome_iff] at hok
  obtain ⟨s_out, hsteps_out, hout⟩ := hok x R s0 hentry.1 hentry.2.1 hpre hentry.2.2 hcode
  have hstop := SubroutineOutcome.toSubroutineStop hout
  have hfrom := StepsUntil.steps_from_of_subroutineStop huntil hsteps_out hstop
  have heq := Steps.eq_of_isTerminal hfrom (isTerminal_of_panicked hpan)
  subst heq
  rcases hout with ⟨hret, _, _⟩ | ⟨_, honPanic⟩ | ⟨_, hexit, _⟩ | ⟨hoom, _⟩
  · have hrun := hret.2.2; rw [hpan] at hrun; cases hrun
  · exact hpost_false honPanic
  · rw [hpan] at hexit; cases hexit
  · rw [hpan] at hoom; cases hoom

theorem read8_of_satisfies_frame_canary {P R : SepProp} {m : Memory}
    {canary_addr : BitVec 64} {v0 : BitVec 8}
    (h : m ⊨ P ∗ ((canary_addr ↦₈ v0) ∗ R)) :
    m.read8 canary_addr = v0 := by
  have h' : m ⊨ (canary_addr ↦₈ v0) ∗ (P ∗ R) := by
    rwa [sepConj_left_comm]
  exact (IsBlock.pointsTo8 canary_addr v0).read h'

/-- If the separation-logic frame includes a canary byte `canary_addr ↦₈ v0`
    (`s0.mem ⊨ spec.pre x s0 ∗ ((canary_addr ↦₈ v0) ∗ R)`) and execution returns in state `sf`
    having overwritten `canary_addr` (`sf.mem.read8 canary_addr = v1` with `v1 ≠ v0`), then
    `¬ safe_subroutine_ok prog entry_pc spec`. -/
theorem not_safe_subroutine_ok_of_frame_canary {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 sf : State}
    {canary_addr : BitVec 64} {v0 v1 : BitVec 8}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ ((canary_addr ↦₈ v0) ∗ R))
    (hsteps : Steps prog s0 sf)
    (hret : Returned s0 sf)
    (hread : sf.mem.read8 canary_addr = v1)
    (hne : v1 ≠ v0)
    (hlr : HaltsAtReturn prog s0 := by
      first
      | exact HaltsAtReturn.of_unaligned (by decide) (by decide)
      | exact HaltsAtReturn.of_unaligned rfl (by decide)) :
    ¬ safe_subroutine_ok prog entry_pc spec := by
  refine not_safe_subroutine_ok_of_post_false x ((canary_addr ↦₈ v0) ∗ R)
    hentry hcode hpre hsteps hret ?_ hlr
  intro hpost
  have heq := read8_of_satisfies_frame_canary hpost
  rw [hread] at heq
  exact hne heq

/-- Frame-canary refutation for `subroutine_ok` with a byte canary `canary_addr ↦₈ v0`. -/
theorem not_subroutine_ok_of_frame_canary {α : Type}
    {prog : Program} {entry_pc : BitVec 64} {spec : Spec α}
    (x : α) (R : SepProp) {s0 sf : State}
    {canary_addr : BitVec 64} {v0 v1 : BitVec 8}
    (hentry : AapcsEntry s0 entry_pc)
    (hcode : prog.CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ ((canary_addr ↦₈ v0) ∗ R))
    (hsteps : Steps prog s0 sf)
    (hret : Returned s0 sf)
    (hread : sf.mem.read8 canary_addr = v1)
    (hne : v1 ≠ v0)
    (hlr : HaltsAtReturn prog s0 := by
      first
      | exact HaltsAtReturn.of_unaligned (by decide) (by decide)
      | exact HaltsAtReturn.of_unaligned rfl (by decide)) :
    ¬ subroutine_ok prog entry_pc spec := by
  intro hok
  exact not_safe_subroutine_ok_of_frame_canary x R hentry hcode hpre hsteps hret hread hne hlr hok.to_safe

end ProofLib.Disproof
