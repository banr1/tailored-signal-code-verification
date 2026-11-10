/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Safety
public import ProofLib.Abi.Aapcs
import Arm64.Trusted.Spec.SepLogic
import Arm64.Trusted.Spec.Hoare

/-!
# Composition Rules for Partial-Correctness Reachability

Progress, step-counted determinism (`StepsN`), composition combinators for `safe_reaches`
(including the termination-measure-free loop rule `safe_reaches.loop` and the step-indexed bridge
`safe_reaches_of_wp_idx`), and structural rules for `safe_subroutine_ok`.
-/

set_option autoImplicit false

namespace ProofLib

open Arm64

@[expose] public section

/-! ## Progress and Step-Counted Execution -/

/-- A `.Running` state always has a `Step` successor: an instruction decodes at `pc`
    (`Step.exec`), `pc` is a hooked entry point (`Step.extern` / `Step.extern_fault`), or nothing
    can be fetched and the machine halts (`Step.halt_unmapped`). -/
theorem Step.progress (prog : Program) {s : State} (h : s.status = .Running) :
    ∃ s', Step prog s s' := by
  cases hf : prog.fetchMem s.mem s.pc with
  | some inst => exact ⟨_, Step.exec h hf⟩
  | none =>
    cases he : prog.externAt? s.pc with
    | none => exact ⟨_, Step.halt_unmapped h hf he⟩
    | some f =>
      by_cases hk : s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab
      · exact ⟨_, Step.extern h he hk.1 hk.2⟩
      · exact ⟨_, Step.extern_fault h he hk⟩

/-- `n`-step execution of `prog`. -/
inductive StepsN (prog : Program) : Nat → State → State → Prop where
  | refl (s : State) : StepsN prog 0 s s
  | step {n : Nat} {s1 s2 s3 : State} (h : Step prog s1 s2) (hs : StepsN prog n s2 s3) :
      StepsN prog (n + 1) s1 s3

theorem StepsN.toSteps {prog : Program} {n : Nat} {s t : State} (h : StepsN prog n s t) :
    Steps prog s t := by
  induction h with
  | refl s => exact Steps.refl s
  | step h _ ih => exact Steps.step h ih

theorem StepsN.of_steps {prog : Program} {s t : State} (h : Steps prog s t) :
    ∃ n, StepsN prog n s t := by
  induction h with
  | refl s => exact ⟨0, StepsN.refl s⟩
  | step h _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, StepsN.step h hn⟩

/-- A run of positive length starts with a step. -/
theorem StepsN.head_step {prog : Program} {n : Nat} {s t : State} (h : StepsN prog n s t)
    (hn : 0 < n) : ∃ s', Step prog s s' := by
  cases h with
  | refl => omega
  | step hst _ => exact ⟨_, hst⟩

/-- Two runs from the same state: the shorter is a prefix of the longer (determinism). -/
theorem StepsN.det_prefix {prog : Program} :
    ∀ {a b : Nat} {s u t : State}, StepsN prog a s u → StepsN prog b s t → a ≤ b →
      StepsN prog (b - a) u t := by
  intro a
  induction a with
  | zero =>
    intro b s u t hu ht _
    cases hu
    simpa using ht
  | succ a ih =>
    intro b s u t hu ht hab
    cases hu with
    | step h1 hrest =>
      cases ht with
      | refl => omega
      | step h2 hrest2 =>
        cases Step.deterministic h1 h2
        have hle : a ≤ _ := Nat.le_of_succ_le_succ hab
        simpa [Nat.succ_sub_succ] using ih hrest hrest2 hle

/-- Any two runs from the same state are comparable. -/
theorem StepsN.compare {prog : Program} {a b : Nat} {s u t : State}
    (hu : StepsN prog a s u) (ht : StepsN prog b s t) :
    (a ≤ b ∧ StepsN prog (b - a) u t) ∨ (b < a ∧ StepsN prog (a - b) t u) := by
  by_cases hab : a ≤ b
  · exact Or.inl ⟨hab, StepsN.det_prefix hu ht hab⟩
  · exact Or.inr ⟨Nat.lt_of_not_le hab, StepsN.det_prefix ht hu (by omega)⟩

/-! ## `safe_reaches` Combinators -/

theorem _root_.Arm64.safe_reaches.of_total {prog : Program} {s0 : State} {Q : State → Prop}
    (h : prog.CodeLoaded s0.mem → ∃ sf, Steps prog s0 sf ∧ Q sf) :
    safe_reaches prog s0 Q :=
  fun hL => Or.inl (h hL)

theorem _root_.Arm64.safe_reaches.done {prog : Program} {s0 : State} {Q : State → Prop}
    (h : Q s0) : safe_reaches prog s0 Q :=
  fun _ => Or.inl ⟨s0, Steps.refl s0, h⟩

theorem _root_.Arm64.safe_reaches.mono {prog : Program} {s0 : State} {Q Q' : State → Prop}
    (h : safe_reaches prog s0 Q) (himp : ∀ s, Q s → Q' s) : safe_reaches prog s0 Q' := by
  intro hL
  rcases h hL with ⟨sf, hsf, hQ⟩ | hall
  · exact Or.inl ⟨sf, hsf, himp sf hQ⟩
  · exact Or.inr hall

private theorem good_of_before_or_after {prog : Program} {s0 s1 t : State}
    (hs1 : Steps prog s0 s1) (ht : Steps prog s0 t)
    (hall1 : ∀ u, Steps prog s1 u → u.status = .Running ∧ ∃ u', Step prog u u') :
    t.status = .Running ∧ ∃ t', Step prog t t' := by
  rcases Steps.compare hs1 ht with hs1t | hts1
  · exact hall1 t hs1t
  · cases hts1 with
    | refl => exact hall1 _ (Steps.refl _)
    | step hst _ => exact ⟨Arm64.Step.status_running hst, _, hst⟩

/-- Compose a partial run to `Q1` with a partial continuation from every reachable `Q1` state. -/
theorem _root_.Arm64.safe_reaches.bind {prog : Program} {s0 : State} {Q1 Q2 : State → Prop}
    (h1 : safe_reaches prog s0 Q1)
    (h2 : ∀ s1, Steps prog s0 s1 → Q1 s1 → safe_reaches prog s1 Q2) :
    safe_reaches prog s0 Q2 := by
  intro hL
  rcases h1 hL with ⟨s1, hs1, hQ1⟩ | hall
  · rcases h2 s1 hs1 hQ1 (hs1.codeLoaded hL) with ⟨sf, hsf, hQ2⟩ | hall1
    · exact Or.inl ⟨sf, hs1.trans hsf, hQ2⟩
    · exact Or.inr fun t ht => good_of_before_or_after hs1 ht hall1
  · exact Or.inr hall

theorem _root_.Arm64.safe_reaches.step {prog : Program} {s s1 : State} {Q : State → Prop}
    (hstep : Step prog s s1) (h : safe_reaches prog s1 Q) : safe_reaches prog s Q := by
  intro hL
  rcases h (hstep.codeLoaded hL) with ⟨sf, hsf, hQ⟩ | hall
  · exact Or.inl ⟨sf, Steps.step hstep hsf, hQ⟩
  · refine Or.inr fun t ht => ?_
    cases ht with
    | refl => exact ⟨Arm64.Step.status_running hstep, _, hstep⟩
    | step h' hrest =>
      cases Step.deterministic hstep h'
      exact hall t hrest

theorem _root_.Arm64.safe_reaches.steps {prog : Program} {s s1 : State} {Q : State → Prop}
    (hsteps : Steps prog s s1) (h : safe_reaches prog s1 Q) : safe_reaches prog s Q := by
  induction hsteps with
  | refl => exact h
  | step hst _ ih => exact safe_reaches.step hst (ih h)

/-- Compose a total prefix reaching `Q1` with a partial continuation to `Q2`. -/
theorem _root_.Arm64.safe_reaches.seq_total {prog : Program} {s0 : State} {Q1 Q2 : State → Prop}
    (h1 : prog.CodeLoaded s0.mem → ∃ s1, Steps prog s0 s1 ∧ Q1 s1)
    (h2 : ∀ s1, Steps prog s0 s1 → Q1 s1 → safe_reaches prog s1 Q2) :
    safe_reaches prog s0 Q2 :=
  safe_reaches.bind (safe_reaches.of_total h1) h2

/-- Partial-correctness call rule: compose a `safe_subroutine_ok` callee at AAPCS entry `s`
    (with caller frame `Rc`) with a partial continuation from every callee outcome. -/
theorem _root_.Arm64.safe_reaches.call {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hcallee : safe_subroutine_ok prog entry spec)
    {s : State} (x : α) (Rc : SepProp) (hentry : AapcsEntry s entry)
    (hpre : s.mem ⊨ spec.pre x s ∗ Rc) {Q : State → Prop}
    (hcont : ∀ sf, Steps prog s sf → SubroutineOutcome spec x Rc s sf → safe_reaches prog sf Q) :
    safe_reaches prog s Q :=
  safe_reaches.bind (hcallee x Rc s hentry hpre) hcont

/-- Total-correctness callee (`subroutine_ok`) used at a partial-correctness call site. -/
theorem _root_.Arm64.safe_reaches.call_total {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hcallee : subroutine_ok prog entry spec)
    {s : State} (x : α) (Rc : SepProp) (hentry : AapcsEntry s entry)
    (hpre : s.mem ⊨ spec.pre x s ∗ Rc) {Q : State → Prop}
    (hcont : ∀ sf, Steps prog s sf → SubroutineOutcome spec x Rc s sf → safe_reaches prog sf Q) :
    safe_reaches prog s Q :=
  safe_reaches.call hcallee.to_safe x Rc hentry hpre hcont

/-! ## Loop Rule Without a Termination Measure -/

/-- If from every loop-head state `I s` the machine takes at least one step and then safely
    reaches `I` or `Exit`, then from `I s0` execution safely reaches `Exit`. -/
theorem _root_.Arm64.safe_reaches.loop {prog : Program} {I Exit : State → Prop}
    (hbody : ∀ s, I s → prog.CodeLoaded s.mem →
      ∃ s1, Step prog s s1 ∧ safe_reaches prog s1 (fun s' => I s' ∨ Exit s'))
    {s0 : State} (h0 : I s0) : safe_reaches prog s0 Exit := by
  intro hL
  by_cases hex : ∃ sf, Steps prog s0 sf ∧ Exit sf
  · exact Or.inl hex
  · right
    have key : ∀ n s, I s → Steps prog s0 s → ∀ t, StepsN prog n s t →
        t.status = .Running ∧ ∃ t', Step prog t t' := by
      intro n
      induction n using Nat.strongRecOn with
      | _ n ih =>
        intro s hI hs0s t hnt
        have hLs : prog.CodeLoaded s.mem := hs0s.codeLoaded hL
        obtain ⟨s1, hstep, hsafe⟩ := hbody s hI hLs
        cases hnt with
        | refl => exact ⟨Arm64.Step.status_running hstep, _, hstep⟩
        | step hst hrest =>
          rename_i m t1
          cases Step.deterministic hst hstep
          rcases hsafe (hstep.codeLoaded hLs) with ⟨s', hs1s', hIE⟩ | hall
          · rcases hIE with hI' | hE'
            · obtain ⟨k, hk⟩ := StepsN.of_steps hs1s'
              rcases StepsN.compare hk hrest with ⟨_, hs't⟩ | ⟨hlt, hts'⟩
              · exact ih (m - k) (by omega) s' hI' (hs0s.trans (Steps.step hstep hs1s')) t hs't
              · obtain ⟨t', hst'⟩ := StepsN.head_step hts' (by omega)
                exact ⟨Arm64.Step.status_running hst', _, hst'⟩
            · exact absurd ⟨s', hs0s.trans (Steps.step hstep hs1s'), hE'⟩ hex
          · exact hall t hrest.toSteps
    intro t ht
    obtain ⟨n, hn⟩ := StepsN.of_steps ht
    exact key n s0 h0 (Steps.refl _) t hn

/-- Loop rule for a total iteration body returning to `I` or reaching `Exit`. -/
theorem _root_.Arm64.safe_reaches.loop_total {prog : Program} {I Exit : State → Prop}
    (hbody : ∀ s, I s → prog.CodeLoaded s.mem →
      ∃ s1, Step prog s s1 ∧ ∃ s', Steps prog s1 s' ∧ (I s' ∨ Exit s'))
    {s0 : State} (h0 : I s0) : safe_reaches prog s0 Exit :=
  safe_reaches.loop (fun s hI hL =>
    let ⟨s1, hst, hrest⟩ := hbody s hI hL
    ⟨s1, hst, safe_reaches.of_total fun _ => hrest⟩) h0

/-! ## Step-Indexed Bridge -/

private theorem good_of_wp_idx {prog : Program} {stop Q : State → Prop} :
    ∀ {s t : State}, Steps prog s t → (∀ n, wp_idx prog stop Q n s) →
      (¬ ∃ sf, Steps prog s sf ∧ (stop sf ∧ Q sf)) → ∀ n, wp_idx prog stop Q n t := by
  intro s t hst
  induction hst with
  | refl => exact fun h _ => h
  | @step a b c hab _ ih =>
    intro hall hno
    refine ih (fun n => ?_) (fun ⟨sf, hsf, hq⟩ => hno ⟨sf, Steps.step hab hsf, hq⟩)
    rcases hall (n + 1) with hq | ⟨_, _, _, hnext⟩
    · exact absurd ⟨a, Steps.refl a, hq⟩ hno
    · exact hnext b hab

/-- If `wp_idx prog stop Q n s` holds for every index `n` when code is loaded, execution from `s`
    safely reaches a `stop` state satisfying `Q`. -/
theorem safe_reaches_of_wp_idx {prog : Program} {stop Q : State → Prop} {s : State}
    (h : prog.CodeLoaded s.mem → ∀ n, wp_idx prog stop Q n s) :
    safe_reaches prog s (fun sf => stop sf ∧ Q sf) := by
  intro hL
  by_cases hex : ∃ sf, Steps prog s sf ∧ (stop sf ∧ Q sf)
  · exact Or.inl hex
  · refine Or.inr fun t ht => ?_
    rcases good_of_wp_idx ht (h hL) hex 1 with hq | ⟨_, hrun, hstep, _⟩
    · exact absurd ⟨t, ht, hq⟩ hex
    · exact ⟨hrun, hstep⟩

/-! ## `safe_subroutine_ok` Structural Rules -/

/-- Outcome-level monotonicity for `safe_subroutine_ok`: strengthen the precondition (possibly
    changing the ghost type) and weaken the outcome. -/
theorem _root_.Arm64.safe_subroutine_ok.mono_outcome {α β : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} {spec' : Spec β}
    (h : safe_subroutine_ok prog entry spec)
    (href : ∀ (y : β) (R : SepProp) (s0 : State), AapcsEntry s0 entry →
      (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ x, (s0.mem ⊨ spec.pre x s0 ∗ R) ∧
        ∀ sf, SubroutineOutcome spec x R s0 sf → SubroutineOutcome spec' y R s0 sf) :
    safe_subroutine_ok prog entry spec' := by
  intro y R s0 hentry hpre
  obtain ⟨x, hx, himp⟩ := href y R s0 hentry hpre
  exact (h x R s0 hentry hx).mono himp

/-- Monotonicity rule for `safe_subroutine_ok` (mirror of `subroutine_ok_mono`). -/
theorem _root_.Arm64.safe_subroutine_ok.mono {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec spec' : Spec α}
    (h : safe_subroutine_ok prog entry_pc spec)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec'.pre x s0 ∗ R) → (s0.mem ⊨ spec.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec.post x s0 sf ∗ R) → (sf.mem ⊨ spec'.post x s0 sf ∗ R))
    (hpanic : ∀ x R s0 sf, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) →
        (sf.mem ⊨ spec'.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; first | exact hp | exact False.elim (not_satisfies_false_sepConj hp))
    (hexit : ∀ x code R s0 sf, (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) →
        (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; first | exact he | exact False.elim (not_satisfies_false_sepConj he))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    safe_subroutine_ok prog entry_pc spec' :=
  h.mono_outcome fun x R s0 _ hp => ⟨x, hpre x R s0 hp, fun sf hout => by
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
    · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq⟩
    · exact Or.inr (Or.inl ⟨hpan, hpanic x R s0 sf hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hexit x code R s0 sf hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom x R s0 sf hq⟩))⟩

/-- Rule of consequence for `safe_subroutine_ok` by separation-logic entailment (mirror of
    `subroutine_ok.conseq`). -/
theorem _root_.Arm64.safe_subroutine_ok.conseq {α : Type} {prog : Program} {entry : BitVec 64}
    {spec₁ spec₂ : Spec α}
    (hok : safe_subroutine_ok prog entry spec₁)
    (h_pre : ∀ x s0, spec₂.pre x s0 ⊢ spec₁.pre x s0)
    (h_post : ∀ x s0 sf, spec₁.post x s0 sf ⊢ spec₂.post x s0 sf)
    (h_panic : ∀ x s0 sf, spec₁.onPanic x s0 sf ⊢ spec₂.onPanic x s0 sf)
    (h_exit : ∀ x code s0 sf, spec₁.onExit x code s0 sf ⊢ spec₂.onExit x code s0 sf)
    (h_oom : ∀ x s0 sf, spec₁.onOom x s0 sf ⊢ spec₂.onOom x s0 sf :=
      by intro x s0 sf; exact Entails.refl _) :
    safe_subroutine_ok prog entry spec₂ :=
  hok.mono
    (fun x _ s0 hp => Satisfies.mono (sepConj_mono_left (h_pre x s0)) hp)
    (fun x _ s0 sf hq => Satisfies.mono (sepConj_mono_left (h_post x s0 sf)) hq)
    (fun x _ s0 sf hp => Satisfies.mono (sepConj_mono_left (h_panic x s0 sf)) hp)
    (fun x code _ s0 sf he => Satisfies.mono (sepConj_mono_left (h_exit x code s0 sf)) he)
    (fun x _ s0 sf ho => Satisfies.mono (sepConj_mono_left (h_oom x s0 sf)) ho)

/-- Frame rule for `safe_subroutine_ok` (mirror of `Spec.withPreserves.frame`): a preserved
    spatial resource `F x` can be conjoined to every clause. -/
theorem _root_.Arm64.Spec.withPreserves.safe_frame {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (h : safe_subroutine_ok prog entry spec)
    (F : α → SepProp) : safe_subroutine_ok prog entry (spec.withPreserves F) := by
  intro x R s0 hentry hpre
  simp only [sepConj_assoc] at hpre
  refine (h x (F x ∗ R) s0 hentry hpre).mono fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · exact Or.inl ⟨hret, hcc, by simpa only [Spec.withPreserves, sepConj_assoc] using hq⟩
  · exact Or.inr (Or.inl ⟨hpan, by simpa only [Spec.withPreserves, sepConj_assoc] using hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex,
      by simpa only [Spec.withPreserves, sepConj_assoc] using hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, by simpa only [Spec.withPreserves, sepConj_assoc] using hq⟩))

end

end ProofLib
