/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Arm64
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.Hoare.Hooks
public import ProofLib.Hoare.HookMap
import ProofLib.Hoare.Model
import ProofLib.Hoare.SubroutineOk

/-!
# Trap and Panic-Stub Transfer Across Program Variants

Transfers total-correctness judgments across program variants `P₁` and `P₂` whose external
hook tables agree except where `P₁` installs trap hooks (`TrapsOnly P₁ P₂`) or panic-or-trap
hooks (`PanicsOrTrapsOnly P₁ P₂`). Any execution ending in `OutcomeStatus` avoids trap hooks,
and any execution ending in `NonPanicOutcomeStatus` avoids panic-or-trap hooks, so
`subroutine_ok`, `SepWP`, `reaches_pc`, `exit_ok`, and related judgments transfer directly
from `P₁` to `P₂`. The `trap_transfer h using tac` tactic automates this transfer across
quantifiers, `Prop` structures, and definitions.
-/

@[expose] public section

namespace ProofLib.Variant

open Arm64 ProofLib

/-! ## Outcome statuses, traps, and panic-or-trap hooks -/

/-- A machine status that can end a total-correctness judgement: `.Running` (at the target PC),
    `.Panicked`, `.Exited c`, or `.OutOfMemory`. -/
def OutcomeStatus (st : ExecStatus) : Prop :=
  st = .Running ∨ st = .Panicked ∨ (∃ c, st = .Exited c) ∨ st = .OutOfMemory

/-- A machine status that can end a non-panicking total-correctness judgement: `.Running`,
    `.Exited c`, or `.OutOfMemory`. -/
def NonPanicOutcomeStatus (st : ExecStatus) : Prop :=
  st = .Running ∨ (∃ c, st = .Exited c) ∨ st = .OutOfMemory

/-- A trap: a hook whose result is never in an `OutcomeStatus` (e.g. `.Exception msg` or `.Halted`). -/
def IsTrap (f : State → State) : Prop :=
  ∀ s, ¬ OutcomeStatus (f s).status

/-- A panic-or-trap hook: a hook whose result is never in a `NonPanicOutcomeStatus` (e.g.
    `Rust.panicked` or any `IsTrap` hook). -/
def IsPanicOrTrap (f : State → State) : Prop :=
  ∀ s, ¬ NonPanicOutcomeStatus (f s).status

/-- `P₁` differs from `P₂` only by traps: same base, code, symbols, stubs, and `svc`, and at every
    PC the hook of `P₁` is either equal to the hook of `P₂` or a trap. -/
structure TrapsOnly (P₁ P₂ : Program) : Prop where
  base : P₁.base = P₂.base := by rfl
  code : P₁.code = P₂.code := by rfl
  symbols : P₁.symbols = P₂.symbols := by rfl
  stubs : P₁.stubs = P₂.stubs := by rfl
  svc : P₁.svc = P₂.svc := by rfl
  hook : ∀ pc, P₁.externAt? pc = P₂.externAt? pc ∨ ∃ f, P₁.externAt? pc = some f ∧ IsTrap f

/-- `P₁` differs from `P₂` only by panic or trap hooks: same base, code, symbols, stubs, and `svc`,
    and at every PC the hook of `P₁` is either equal to the hook of `P₂` or a panic-or-trap hook. -/
structure PanicsOrTrapsOnly (P₁ P₂ : Program) : Prop where
  base : P₁.base = P₂.base := by rfl
  code : P₁.code = P₂.code := by rfl
  symbols : P₁.symbols = P₂.symbols := by rfl
  stubs : P₁.stubs = P₂.stubs := by rfl
  svc : P₁.svc = P₂.svc := by rfl
  hook : ∀ pc, P₁.externAt? pc = P₂.externAt? pc ∨ ∃ f, P₁.externAt? pc = some f ∧ IsPanicOrTrap f

theorem OutcomeStatus.of_running {st : ExecStatus} (h : st = .Running) : OutcomeStatus st :=
  Or.inl h

theorem OutcomeStatus.of_panicked {st : ExecStatus} (h : st = .Panicked) : OutcomeStatus st :=
  Or.inr (Or.inl h)

theorem OutcomeStatus.of_exited {st : ExecStatus} {c : BitVec 64} (h : st = .Exited c) :
    OutcomeStatus st :=
  Or.inr (Or.inr (Or.inl ⟨c, h⟩))

theorem OutcomeStatus.of_outOfMemory {st : ExecStatus} (h : st = .OutOfMemory) : OutcomeStatus st :=
  Or.inr (Or.inr (Or.inr h))

theorem NonPanicOutcomeStatus.of_running {st : ExecStatus} (h : st = .Running) :
    NonPanicOutcomeStatus st :=
  Or.inl h

theorem NonPanicOutcomeStatus.of_exited {st : ExecStatus} {c : BitVec 64} (h : st = .Exited c) :
    NonPanicOutcomeStatus st :=
  Or.inr (Or.inl ⟨c, h⟩)

theorem NonPanicOutcomeStatus.of_outOfMemory {st : ExecStatus} (h : st = .OutOfMemory) :
    NonPanicOutcomeStatus st :=
  Or.inr (Or.inr h)

theorem NonPanicOutcomeStatus.to_outcomeStatus {st : ExecStatus} (h : NonPanicOutcomeStatus st) :
    OutcomeStatus st := by
  rcases h with hr | ⟨c, hc⟩ | hoom
  · exact .of_running hr
  · exact .of_exited hc
  · exact .of_outOfMemory hoom

theorem not_outcomeStatus_exception (msg : String) : ¬ OutcomeStatus (.Exception msg) := by
  simp [OutcomeStatus]

theorem not_nonPanicOutcomeStatus_panicked : ¬ NonPanicOutcomeStatus .Panicked := by
  simp [NonPanicOutcomeStatus]

theorem not_nonPanicOutcomeStatus_exception (msg : String) :
    ¬ NonPanicOutcomeStatus (.Exception msg) :=
  fun h => not_outcomeStatus_exception msg h.to_outcomeStatus

theorem isTrap_of_exception {f : State → State} (h : ∀ s, ∃ msg, (f s).status = .Exception msg) :
    IsTrap f := by
  intro s
  obtain ⟨msg, hm⟩ := h s
  rw [hm]
  exact not_outcomeStatus_exception msg

theorem IsTrap.to_isPanicOrTrap {f : State → State} (h : IsTrap f) : IsPanicOrTrap f :=
  fun s hnp => h s hnp.to_outcomeStatus

theorem isPanicOrTrap_of_panicked {f : State → State} (h : ∀ s, (f s).status = .Panicked) :
    IsPanicOrTrap f := by
  intro s
  rw [h s]
  exact not_nonPanicOutcomeStatus_panicked

/-- Canonical trap hook setting `status := .Exception msg`. -/
def trapHook (msg : String := "trap") (s : State) : State :=
  s.setStatus (.Exception msg)

@[simp] theorem trapHook_isTrap (msg : String := "trap") : IsTrap (trapHook msg) :=
  isTrap_of_exception fun _ => ⟨msg, rfl⟩

@[simp] theorem trapHook_isPanicOrTrap (msg : String := "trap") : IsPanicOrTrap (trapHook msg) :=
  (trapHook_isTrap msg).to_isPanicOrTrap

@[simp] theorem panicked_isPanicOrTrap : IsPanicOrTrap Rust.panicked :=
  isPanicOrTrap_of_panicked fun _ => rfl

theorem TrapsOnly.refl (P : Program) : TrapsOnly P P :=
  { hook := fun _ => Or.inl rfl }

theorem TrapsOnly.trans {P₁ P₂ P₃ : Program} (h12 : TrapsOnly P₁ P₂) (h23 : TrapsOnly P₂ P₃) :
    TrapsOnly P₁ P₃ where
  base := h12.base.trans h23.base
  code := h12.code.trans h23.code
  symbols := h12.symbols.trans h23.symbols
  stubs := h12.stubs.trans h23.stubs
  svc := h12.svc.trans h23.svc
  hook pc := by
    rcases h12.hook pc with heq | ⟨f, hf, ht⟩
    · rw [heq]; exact h23.hook pc
    · exact Or.inr ⟨f, hf, ht⟩

theorem TrapsOnly.findSymbol? {P₁ P₂ : Program} (h : TrapsOnly P₁ P₂) (sym : String) :
    P₁.findSymbol? sym = P₂.findSymbol? sym := by
  simp only [Program.findSymbol?, h.symbols, h.stubs]

theorem TrapsOnly.fnOff {P₁ P₂ : Program} (h : TrapsOnly P₁ P₂) (sym : String) :
    P₁.fnOff sym = P₂.fnOff sym := by
  simp only [Program.fnOff, h.findSymbol?]

theorem TrapsOnly.fnAddr {P₁ P₂ : Program} (h : TrapsOnly P₁ P₂) (sym : String) :
    P₁.fnAddr sym = P₂.fnAddr sym := by
  simp only [Program.fnAddr, h.base, h.fnOff]

theorem TrapsOnly.to_panicsOrTrapsOnly {P₁ P₂ : Program} (h : TrapsOnly P₁ P₂) :
    PanicsOrTrapsOnly P₁ P₂ where
  base := h.base
  code := h.code
  symbols := h.symbols
  stubs := h.stubs
  svc := h.svc
  hook pc := (h.hook pc).imp id fun ⟨f, hf, ht⟩ => ⟨f, hf, ht.to_isPanicOrTrap⟩

theorem PanicsOrTrapsOnly.refl (P : Program) : PanicsOrTrapsOnly P P :=
  (TrapsOnly.refl P).to_panicsOrTrapsOnly

theorem PanicsOrTrapsOnly.trans {P₁ P₂ P₃ : Program}
    (h12 : PanicsOrTrapsOnly P₁ P₂) (h23 : PanicsOrTrapsOnly P₂ P₃) :
    PanicsOrTrapsOnly P₁ P₃ where
  base := h12.base.trans h23.base
  code := h12.code.trans h23.code
  symbols := h12.symbols.trans h23.symbols
  stubs := h12.stubs.trans h23.stubs
  svc := h12.svc.trans h23.svc
  hook pc := by
    rcases h12.hook pc with heq | ⟨f, hf, ht⟩
    · rw [heq]; exact h23.hook pc
    · exact Or.inr ⟨f, hf, ht⟩

theorem PanicsOrTrapsOnly.findSymbol? {P₁ P₂ : Program} (h : PanicsOrTrapsOnly P₁ P₂)
    (sym : String) : P₁.findSymbol? sym = P₂.findSymbol? sym := by
  simp only [Program.findSymbol?, h.symbols, h.stubs]

theorem PanicsOrTrapsOnly.fnOff {P₁ P₂ : Program} (h : PanicsOrTrapsOnly P₁ P₂) (sym : String) :
    P₁.fnOff sym = P₂.fnOff sym := by
  simp only [Program.fnOff, h.findSymbol?]

theorem PanicsOrTrapsOnly.fnAddr {P₁ P₂ : Program} (h : PanicsOrTrapsOnly P₁ P₂) (sym : String) :
    P₁.fnAddr sym = P₂.fnAddr sym := by
  simp only [Program.fnAddr, h.base, h.fnOff]

/-! ## Step and multi-step transfer lemmas -/

theorem CodeLoaded_of_trapsOnly {P₁ P₂ : Program} (h : TrapsOnly P₁ P₂) {m : Memory}
    (hL : P₂.CodeLoaded m) : P₁.CodeLoaded m := by
  unfold Program.CodeLoaded at hL ⊢
  rw [h.base, h.code]
  exact hL

theorem CodeLoaded_of_panicsOrTrapsOnly {P₁ P₂ : Program} (h : PanicsOrTrapsOnly P₁ P₂)
    {m : Memory} (hL : P₂.CodeLoaded m) : P₁.CodeLoaded m := by
  unfold Program.CodeLoaded at hL ⊢
  rw [h.base, h.code]
  exact hL

theorem fetchMem_eq_of_externAt_eq {P₁ P₂ : Program} {m : Memory} {pc : BitVec 64}
    (h : P₁.externAt? pc = P₂.externAt? pc) : P₁.fetchMem m pc = P₂.fetchMem m pc := by
  unfold Program.fetchMem
  rw [h]

/-- Off the traps, a step of `P₁` is a step of `P₂`. -/
theorem Step.of_externAt_eq {P₁ P₂ : Program} {s s' : State}
    (hpc : P₁.externAt? s.pc = P₂.externAt? s.pc) (hs : Step P₁ s s')
    (hsvc : P₁.svc = P₂.svc := by rfl) : Step P₂ s s' := by
  have hf : P₁.fetchMem s.mem s.pc = P₂.fetchMem s.mem s.pc := fetchMem_eq_of_externAt_eq hpc
  have hev : ∀ inst, P₁.evalInst inst s = P₂.evalInst inst s := fun inst => by
    unfold Program.evalInst; rw [hsvc]
  cases hs with
  | @exec inst hr hfe => rw [hev inst]; exact .exec hr (hf ▸ hfe)
  | halt_unmapped hr hfe he => exact .halt_unmapped hr (hf ▸ hfe) (hpc ▸ he)
  | extern hr he hk hsy => exact .extern hr (hpc ▸ he) hk hsy
  | extern_fault hr he hn => exact .extern_fault hr (hpc ▸ he) hn

theorem Steps.eq_of_not_running {P : Program} {s sf : State} (h : Steps P s sf)
    (hs : s.status ≠ .Running) : sf = s := by
  cases h with
  | refl => rfl
  | step h1 _ => cases h1 <;> contradiction

theorem StepsUntil.eq_of_not_running {P : Program} {stop : State → Prop} {s sf : State}
    (h : StepsUntil P stop s sf) (hs : s.status ≠ .Running) : sf = s := by
  cases h with
  | refl => rfl
  | step _ h1 _ => cases h1 <;> contradiction

/-- Step-sequence transfer when every differing hook of `P₁` lands in a status outside `allow`
    and `sf` has status in `allow`. -/
theorem Steps.of_externAt_or_avoid {P₁ P₂ : Program} {allow : ExecStatus → Prop}
    (hrun : allow .Running) (hexc : ∀ msg, ¬ allow (.Exception msg))
    (hhook : ∀ pc, P₁.externAt? pc = P₂.externAt? pc ∨
      ∃ f, P₁.externAt? pc = some f ∧ ∀ s, ¬ allow (f s).status)
    {s sf : State} (h : Steps P₁ s sf) (hallow : allow sf.status)
    (hsvc : P₁.svc = P₂.svc := by rfl) :
    Steps P₂ s sf := by
  induction h with
  | refl => exact .refl _
  | @step s1 s2 s3 h1 h2 ih =>
    rcases hhook s1.pc with heq | ⟨f, hf, hbad⟩
    · exact .step (Step.of_externAt_eq heq h1 hsvc) (ih hallow)
    · exfalso
      cases h1 with
      | exec _ hfe => simp [Program.fetchMem, hf] at hfe
      | halt_unmapped _ _ he => simp [hf] at he
      | extern _ he _ _ =>
        rw [hf] at he
        cases he
        have hnr : (f s1).status ≠ .Running := fun hr => hbad s1 (hr ▸ hrun)
        have h23 := Steps.eq_of_not_running h2 hnr
        subst h23
        exact hbad s1 hallow
      | extern_fault _ _ _ =>
        have h23 := Steps.eq_of_not_running h2 (by simp)
        subst h23
        exact hexc _ hallow

/-- `StepsUntil` transfer when every differing hook of `P₁` lands in a status outside `allow`
    and `sf` has status in `allow`. -/
theorem StepsUntil.of_externAt_or_avoid {P₁ P₂ : Program} {allow : ExecStatus → Prop}
    (hrun : allow .Running) (hexc : ∀ msg, ¬ allow (.Exception msg))
    (hhook : ∀ pc, P₁.externAt? pc = P₂.externAt? pc ∨
      ∃ f, P₁.externAt? pc = some f ∧ ∀ s, ¬ allow (f s).status)
    {stop : State → Prop} {s sf : State} (h : StepsUntil P₁ stop s sf) (hallow : allow sf.status)
    (hsvc : P₁.svc = P₂.svc := by rfl) :
    StepsUntil P₂ stop s sf := by
  induction h with
  | refl => exact .refl _
  | @step s1 s2 s3 hcont h1 h2 ih =>
    rcases hhook s1.pc with heq | ⟨f, hf, hbad⟩
    · exact .step hcont (Step.of_externAt_eq heq h1 hsvc) (ih hallow)
    · exfalso
      cases h1 with
      | exec _ hfe => simp [Program.fetchMem, hf] at hfe
      | halt_unmapped _ _ he => simp [hf] at he
      | extern _ he _ _ =>
        rw [hf] at he
        cases he
        have hnr : (f s1).status ≠ .Running := fun hr => hbad s1 (hr ▸ hrun)
        have h23 := StepsUntil.eq_of_not_running h2 hnr
        subst h23
        exact hbad s1 hallow
      | extern_fault _ _ _ =>
        have h23 := StepsUntil.eq_of_not_running h2 (by simp)
        subst h23
        exact hexc _ hallow

/-- A `P₁` run that ends in an `OutcomeStatus` is a `P₂` run under `TrapsOnly P₁ P₂`. -/
theorem Steps.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {s sf : State}
    (h : Steps P₁ s sf) (hout : OutcomeStatus sf.status) : Steps P₂ s sf :=
  Steps.of_externAt_or_avoid (.of_running rfl) not_outcomeStatus_exception hT.hook h hout hT.svc

/-- A `StepsUntil P₁` run that ends in an `OutcomeStatus` is a `StepsUntil P₂` run. -/
theorem StepsUntil.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {stop : State → Prop}
    {s sf : State} (h : StepsUntil P₁ stop s sf) (hout : OutcomeStatus sf.status) :
    StepsUntil P₂ stop s sf :=
  StepsUntil.of_externAt_or_avoid (.of_running rfl) not_outcomeStatus_exception hT.hook h hout hT.svc

/-- A `P₁` run that ends in a `NonPanicOutcomeStatus` is a `P₂` run under
    `PanicsOrTrapsOnly P₁ P₂`. -/
theorem Steps.of_panicsOrTrapsOnly {P₁ P₂ : Program} (hT : PanicsOrTrapsOnly P₁ P₂) {s sf : State}
    (h : Steps P₁ s sf) (hout : NonPanicOutcomeStatus sf.status) : Steps P₂ s sf :=
  Steps.of_externAt_or_avoid (.of_running rfl) not_nonPanicOutcomeStatus_exception hT.hook h hout
    hT.svc

/-- A `StepsUntil P₁` run that ends in a `NonPanicOutcomeStatus` is a `StepsUntil P₂` run. -/
theorem StepsUntil.of_panicsOrTrapsOnly {P₁ P₂ : Program} (hT : PanicsOrTrapsOnly P₁ P₂)
    {stop : State → Prop} {s sf : State} (h : StepsUntil P₁ stop s sf)
    (hout : NonPanicOutcomeStatus sf.status) : StepsUntil P₂ stop s sf :=
  StepsUntil.of_externAt_or_avoid (.of_running rfl) not_nonPanicOutcomeStatus_exception hT.hook h
    hout hT.svc

/-! ## Judgment transfer lemmas -/

theorem SubroutineOutcome.outcomeStatus {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : OutcomeStatus sf.status := by
  rcases h with ⟨⟨_, _, hr⟩, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨hoom, _⟩
  · exact .of_running hr
  · exact .of_panicked hp
  · exact .of_exited hc
  · exact .of_outOfMemory hoom

theorem SubroutineOutcome.nonPanicOutcomeStatus {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf)
    (hpanic : ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R)) : NonPanicOutcomeStatus sf.status := by
  rcases h with ⟨⟨_, _, hr⟩, _⟩ | ⟨_, hq⟩ | ⟨c, hc, _⟩ | ⟨hoom, _⟩
  · exact .of_running hr
  · exact absurd hq hpanic
  · exact .of_exited hc
  · exact .of_outOfMemory hoom

theorem reaches_outcome.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {α : Type}
    {spec : Spec α} {x : α} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P₁ spec x R s0 s) : reaches_outcome P₂ spec x R s0 s := by
  refine reaches_outcome_iff.mpr fun hL => ?_
  obtain ⟨sf, hs, hout⟩ := reaches_outcome_iff.mp h (CodeLoaded_of_trapsOnly hT hL)
  exact ⟨sf, Steps.of_trapsOnly hT hs (SubroutineOutcome.outcomeStatus hout), hout⟩

theorem reaches_outcome.of_panicsOrTrapsOnly {P₁ P₂ : Program} (hT : PanicsOrTrapsOnly P₁ P₂)
    {α : Type} {spec : Spec α} {x : α} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P₁ spec x R s0 s)
    (hpanic : ∀ sf : State, ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ hp; exact not_satisfies_false_sepConj hp) :
    reaches_outcome P₂ spec x R s0 s := by
  refine reaches_outcome_iff.mpr fun hL => ?_
  obtain ⟨sf, hs, hout⟩ := reaches_outcome_iff.mp h (CodeLoaded_of_panicsOrTrapsOnly hT hL)
  exact ⟨sf, Steps.of_panicsOrTrapsOnly hT hs
    (SubroutineOutcome.nonPanicOutcomeStatus hout (hpanic sf)), hout⟩

/-- `subroutine_ok` transfers from the trapping program `P₁` to `P₂`. -/
theorem _root_.Arm64.subroutine_ok.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {α : Type}
    {entry : BitVec 64} {spec : Spec α} (h : subroutine_ok P₁ entry spec) :
    subroutine_ok P₂ entry spec :=
  subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre hal =>
    reaches_outcome.of_trapsOnly hT (subroutine_ok_iff.mp h x R s0 hpc hrun hpre hal)

/-- Variant of `subroutine_ok.of_trapsOnly` that discharges entry-address and spec equalities via
    `wp_unfold` (for `@[irreducible, wp_unfold]` wrappers emitted by `declare_rebased_program`). -/
theorem _root_.Arm64.subroutine_ok.of_trapsOnly_eq {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {α : Type} {entry₁ entry₂ : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok P₁ entry₁ spec₁)
    (hentry : entry₁ = entry₂ := by first | rfl | simp only [wp_unfold])
    (hspec : spec₁ = spec₂ := by first | rfl | simp only [wp_unfold]) :
    subroutine_ok P₂ entry₂ spec₂ := by
  subst hentry hspec
  exact _root_.Arm64.subroutine_ok.of_trapsOnly hT h

/-- `Program.subroutineOk` transfers from `P₁` to `P₂` under `TrapsOnly P₁ P₂`. -/
theorem _root_.Arm64.Program.subroutineOk.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {S α : Type} [ToBaseSpec S α] {sym : String} {spec : S}
    (h : P₁.subroutineOk sym spec) :
    P₂.subroutineOk sym spec := by
  unfold Program.subroutineOk at h ⊢
  rw [← hT.fnAddr sym, ← hT.base]
  exact subroutine_ok.of_trapsOnly hT h

/-- Non-panicking `subroutine_ok` transfers from `P₁` to `P₂` under `PanicsOrTrapsOnly P₁ P₂`. -/
theorem _root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {α : Type} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P₁ entry spec)
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp) :
    subroutine_ok P₂ entry spec :=
  subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre hal =>
    reaches_outcome.of_panicsOrTrapsOnly hT (subroutine_ok_iff.mp h x R s0 hpc hrun hpre hal) (hpanic x R s0)

/-- Variant of `subroutine_ok.of_panicsOrTrapsOnly` that discharges entry-address and spec
    equalities via `wp_unfold`. -/
theorem _root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly_eq {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {α : Type} {entry₁ entry₂ : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok P₁ entry₁ spec₁)
    (hentry : entry₁ = entry₂ := by first | rfl | simp only [wp_unfold])
    (hspec : spec₁ = spec₂ := by first | rfl | simp only [wp_unfold])
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec₁.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp) :
    subroutine_ok P₂ entry₂ spec₂ := by
  subst hentry hspec
  exact _root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly hT h hpanic

/-- Non-panicking `Program.subroutineOk` transfers from `P₁` to `P₂` under
    `PanicsOrTrapsOnly P₁ P₂`. -/
theorem _root_.Arm64.Program.subroutineOk.of_panicsOrTrapsOnly {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {S α : Type} [ToBaseSpec S α] {sym : String} {spec : S}
    (h : P₁.subroutineOk sym spec)
    (hpanic : ∀ x R (s0 sf : State),
      ¬ (sf.mem ⊨ (ToBaseSpec.toSpec spec P₁.base).onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp) :
    P₂.subroutineOk sym spec := by
  unfold Program.subroutineOk at h ⊢
  rw [← hT.fnAddr sym, ← hT.base]
  exact _root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly hT h hpanic

theorem _root_.Arm64.raw_subroutine_ok.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {α : Type} {entry : BitVec 64} {spec : Spec α} (h : raw_subroutine_ok P₁ entry spec) :
    raw_subroutine_ok P₂ entry spec :=
  raw_subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre =>
    reaches_outcome.of_trapsOnly hT (raw_subroutine_ok_iff.mp h x R s0 hpc hrun hpre)

theorem _root_.Arm64.raw_subroutine_ok.of_trapsOnly_eq {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {α : Type} {entry₁ entry₂ : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : raw_subroutine_ok P₁ entry₁ spec₁)
    (hentry : entry₁ = entry₂ := by first | rfl | simp only [wp_unfold])
    (hspec : spec₁ = spec₂ := by first | rfl | simp only [wp_unfold]) :
    raw_subroutine_ok P₂ entry₂ spec₂ := by
  subst hentry hspec
  exact _root_.Arm64.raw_subroutine_ok.of_trapsOnly hT h

theorem _root_.Arm64.Program.rawSubroutineOk.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {S α : Type} [ToBaseSpec S α] {sym : String} {spec : S}
    (h : P₁.rawSubroutineOk sym spec) :
    P₂.rawSubroutineOk sym spec := by
  unfold Program.rawSubroutineOk at h ⊢
  rw [← hT.fnAddr sym, ← hT.base]
  exact _root_.Arm64.raw_subroutine_ok.of_trapsOnly hT h

theorem _root_.Arm64.raw_subroutine_ok.of_panicsOrTrapsOnly {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {α : Type} {entry : BitVec 64} {spec : Spec α}
    (h : raw_subroutine_ok P₁ entry spec)
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp) :
    raw_subroutine_ok P₂ entry spec :=
  raw_subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre =>
    reaches_outcome.of_panicsOrTrapsOnly hT (raw_subroutine_ok_iff.mp h x R s0 hpc hrun hpre) (hpanic x R s0)

theorem _root_.Arm64.raw_subroutine_ok.of_panicsOrTrapsOnly_eq {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {α : Type} {entry₁ entry₂ : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : raw_subroutine_ok P₁ entry₁ spec₁)
    (hentry : entry₁ = entry₂ := by first | rfl | simp only [wp_unfold])
    (hspec : spec₁ = spec₂ := by first | rfl | simp only [wp_unfold])
    (hpanic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec₁.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp) :
    raw_subroutine_ok P₂ entry₂ spec₂ := by
  subst hentry hspec
  exact _root_.Arm64.raw_subroutine_ok.of_panicsOrTrapsOnly hT h hpanic

theorem _root_.Arm64.Program.rawSubroutineOk.of_panicsOrTrapsOnly {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {S α : Type} [ToBaseSpec S α] {sym : String} {spec : S}
    (h : P₁.rawSubroutineOk sym spec)
    (hpanic : ∀ x R (s0 sf : State),
      ¬ (sf.mem ⊨ (ToBaseSpec.toSpec spec P₁.base).onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp) :
    P₂.rawSubroutineOk sym spec := by
  unfold Program.rawSubroutineOk at h ⊢
  rw [← hT.fnAddr sym, ← hT.base]
  exact _root_.Arm64.raw_subroutine_ok.of_panicsOrTrapsOnly hT h hpanic

theorem _root_.Arm64.reaches_pc.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {target : BitVec 64} {s0 : State} {post oom : State → Prop} (h : reaches_pc P₁ target s0 post oom) :
    reaches_pc P₂ target s0 post oom := by
  intro hL
  rcases h (CodeLoaded_of_trapsOnly hT hL) with ⟨sf, hs, ⟨hpc, hr, hp⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, Steps.of_trapsOnly hT hs (.of_running hr), Or.inl ⟨hpc, hr, hp⟩⟩
  · exact ⟨sf, Steps.of_trapsOnly hT hs (.of_outOfMemory hoom), Or.inr ⟨hoom, hq⟩⟩

theorem _root_.Arm64.reaches_pc.of_panicsOrTrapsOnly {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {target : BitVec 64} {s0 : State} {post oom : State → Prop}
    (h : reaches_pc P₁ target s0 post oom) :
    reaches_pc P₂ target s0 post oom := by
  intro hL
  rcases h (CodeLoaded_of_panicsOrTrapsOnly hT hL) with ⟨sf, hs, ⟨hpc, hr, hp⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, Steps.of_panicsOrTrapsOnly hT hs (.of_running hr), Or.inl ⟨hpc, hr, hp⟩⟩
  · exact ⟨sf, Steps.of_panicsOrTrapsOnly hT hs (.of_outOfMemory hoom), Or.inr ⟨hoom, hq⟩⟩

theorem _root_.Arm64.reaches_stop.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {stop : State → Prop} {s0 : State} {Q : State → Prop} (h : reaches_stop P₁ stop s0 Q)
    (hout : ∀ sf, stop sf → Q sf → OutcomeStatus sf.status) :
    reaches_stop P₂ stop s0 Q := by
  intro hL
  obtain ⟨sf, hs, hst, hq⟩ := h (CodeLoaded_of_trapsOnly hT hL)
  exact ⟨sf, StepsUntil.of_trapsOnly hT hs (hout sf hst hq), hst, hq⟩

theorem _root_.Arm64.code_ok.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {α : Type}
    {entry exit : BitVec 64} {spec : Spec α} (h : code_ok P₁ entry exit spec) :
    code_ok P₂ entry exit spec :=
  fun x R s0 hpc hrun hpre => _root_.Arm64.reaches_pc.of_trapsOnly hT (h x R s0 hpc hrun hpre)

theorem _root_.Arm64.code_ok.of_panicsOrTrapsOnly {P₁ P₂ : Program} (hT : PanicsOrTrapsOnly P₁ P₂)
    {α : Type} {entry exit : BitVec 64} {spec : Spec α} (h : code_ok P₁ entry exit spec) :
    code_ok P₂ entry exit spec :=
  fun x R s0 hpc hrun hpre =>
    _root_.Arm64.reaches_pc.of_panicsOrTrapsOnly hT (h x R s0 hpc hrun hpre)

theorem _root_.Arm64.exits_with.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {code : BitVec 64} {s0 : State} {post oom : State → Prop} (h : exits_with P₁ code s0 post oom) :
    exits_with P₂ code s0 post oom := by
  intro hL
  rcases h (CodeLoaded_of_trapsOnly hT hL) with ⟨sf, hs, ⟨hc, hp⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, Steps.of_trapsOnly hT hs (.of_exited hc), Or.inl ⟨hc, hp⟩⟩
  · exact ⟨sf, Steps.of_trapsOnly hT hs (.of_outOfMemory hoom), Or.inr ⟨hoom, hq⟩⟩

theorem _root_.Arm64.exits_with.of_panicsOrTrapsOnly {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {code : BitVec 64} {s0 : State} {post oom : State → Prop}
    (h : exits_with P₁ code s0 post oom) :
    exits_with P₂ code s0 post oom := by
  intro hL
  rcases h (CodeLoaded_of_panicsOrTrapsOnly hT hL) with ⟨sf, hs, ⟨hc, hp⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, Steps.of_panicsOrTrapsOnly hT hs (.of_exited hc), Or.inl ⟨hc, hp⟩⟩
  · exact ⟨sf, Steps.of_panicsOrTrapsOnly hT hs (.of_outOfMemory hoom), Or.inr ⟨hoom, hq⟩⟩

theorem _root_.Arm64.exit_ok.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {α : Type}
    {entry : BitVec 64} {code : α → BitVec 64} {spec : Spec α} (h : exit_ok P₁ entry code spec) :
    exit_ok P₂ entry code spec :=
  fun x R s0 hpc hrun hpre => _root_.Arm64.exits_with.of_trapsOnly hT (h x R s0 hpc hrun hpre)

theorem _root_.Arm64.exit_ok.of_panicsOrTrapsOnly {P₁ P₂ : Program} (hT : PanicsOrTrapsOnly P₁ P₂)
    {α : Type} {entry : BitVec 64} {code : α → BitVec 64} {spec : Spec α}
    (h : exit_ok P₁ entry code spec) :
    exit_ok P₂ entry code spec :=
  fun x R s0 hpc hrun hpre =>
    _root_.Arm64.exits_with.of_panicsOrTrapsOnly hT (h x R s0 hpc hrun hpre)

theorem _root_.ProofLib.SepWP.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {target : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : SepWP P₁ target s P post oom) :
    SepWP P₂ target s P post oom :=
  fun R hR => _root_.Arm64.reaches_pc.of_trapsOnly hT (h R hR)

theorem _root_.ProofLib.SepWP.of_panicsOrTrapsOnly {P₁ P₂ : Program} (hT : PanicsOrTrapsOnly P₁ P₂)
    {target : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : SepWP P₁ target s P post oom) :
    SepWP P₂ target s P post oom :=
  fun R hR => _root_.Arm64.reaches_pc.of_panicsOrTrapsOnly hT (h R hR)

theorem _root_.ProofLib.SepWPp.of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : SepWPp P₁ ret s P Q Qp oom) :
    SepWPp P₂ ret s P Q Qp oom := by
  intro R hR hL
  obtain ⟨sf, hs, hout⟩ := h R hR (CodeLoaded_of_trapsOnly hT hL)
  refine ⟨sf, Steps.of_trapsOnly hT hs ?_, hout⟩
  rcases hout with ⟨_, hr, _⟩ | ⟨hp, _⟩ | ⟨hoom, _⟩
  · exact .of_running hr
  · exact .of_panicked hp
  · exact .of_outOfMemory hoom

/-! ## Composed transfer and contract weakening -/

/-- Transfer non-panicking `subroutine_ok` across `PanicsOrTrapsOnly P₁ P₂` and weaken its contract
    via `subroutine_ok_mono_sp`. -/
theorem _root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly_mono_sp {α : Type} {P₁ P₂ : Program}
    (hT : PanicsOrTrapsOnly P₁ P₂) {entry_pc : BitVec 64} {spec spec' : Spec α}
    (hok : subroutine_ok P₁ entry_pc spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0)
    (hpost : ∀ x s0 sf, sf.sp = s0.sp → spec.post x s0 sf ⊢ spec'.post x s0 sf)
    (hno_panic : ∀ x R (s0 sf : State), ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ x code R s0 sf, (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) → (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; first | exact he | exact False.elim (not_satisfies_false_sepConj he))
    (hoom : ∀ x R s0 sf, (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    subroutine_ok P₂ entry_pc spec' :=
  subroutine_ok_mono_sp (_root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly hT hok hno_panic) hpre
    hpost (fun x R s0 sf hp => False.elim (hno_panic x R s0 sf hp)) hexit hoom

/-! ## Hook tables that differ only by traps or panics -/

/-- Per symbol name, hook table `X₁` agrees with `X₂` or has a trap. -/
def HooksTrapOnly (X₁ X₂ : String → Option (State → State)) : Prop :=
  ∀ n, X₁ n = X₂ n ∨ ∃ f, X₁ n = some f ∧ IsTrap f

/-- Per symbol name, hook table `X₁` agrees with `X₂` or has a panic-or-trap hook. -/
def HooksPanicOrTrapOnly (X₁ X₂ : String → Option (State → State)) : Prop :=
  ∀ n, X₁ n = X₂ n ∨ ∃ f, X₁ n = some f ∧ IsPanicOrTrap f

theorem HooksTrapOnly.refl (X : String → Option (State → State)) : HooksTrapOnly X X :=
  fun _ => Or.inl rfl

theorem HooksTrapOnly.trans {X₁ X₂ X₃ : String → Option (State → State)}
    (h12 : HooksTrapOnly X₁ X₂) (h23 : HooksTrapOnly X₂ X₃) : HooksTrapOnly X₁ X₃ := by
  intro n
  rcases h12 n with heq | ⟨f, hf, ht⟩
  · rw [heq]; exact h23 n
  · exact Or.inr ⟨f, hf, ht⟩

theorem HooksPanicOrTrapOnly.refl (X : String → Option (State → State)) :
    HooksPanicOrTrapOnly X X :=
  fun _ => Or.inl rfl

theorem HooksPanicOrTrapOnly.trans {X₁ X₂ X₃ : String → Option (State → State)}
    (h12 : HooksPanicOrTrapOnly X₁ X₂) (h23 : HooksPanicOrTrapOnly X₂ X₃) :
    HooksPanicOrTrapOnly X₁ X₃ := by
  intro n
  rcases h12 n with heq | ⟨f, hf, ht⟩
  · rw [heq]; exact h23 n
  · exact Or.inr ⟨f, hf, ht⟩

/-- `findSome?` over a list preserves a pointwise `P f` hook-table relation. -/
theorem findSome?_predOnly {β : Type} {P : (State → State) → Prop} (l : List β)
    {g₁ g₂ : β → Option (State → State)}
    (h : ∀ b, g₁ b = g₂ b ∨ ∃ f, g₁ b = some f ∧ P f) :
    l.findSome? g₁ = l.findSome? g₂ ∨ ∃ f, l.findSome? g₁ = some f ∧ P f := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rcases h b with hb | ⟨f, hf, ht⟩
    · cases hg : g₁ b with
      | none =>
        have hg2 : g₂ b = none := hb ▸ hg
        simp only [List.findSome?_cons, hg, hg2]
        exact ih
      | some f =>
        have hg2 : g₂ b = some f := hb ▸ hg
        left
        simp only [List.findSome?_cons, hg, hg2]
    · simp only [List.findSome?_cons, hf]
      exact Or.inr ⟨f, rfl, ht⟩

/-- `Option.or` preserves a pointwise `P f` hook-table relation on both arguments. -/
theorem or_predOnly_both {P : (State → State) → Prop}
    {a₁ a₂ c₁ c₂ : Option (State → State)}
    (ha : a₁ = a₂ ∨ ∃ f, a₁ = some f ∧ P f)
    (hc : c₁ = c₂ ∨ ∃ f, c₁ = some f ∧ P f) :
    a₁.or c₁ = a₂.or c₂ ∨ ∃ f, a₁.or c₁ = some f ∧ P f := by
  rcases ha with rfl | ⟨f, rfl, ht⟩
  · cases a₁ with
    | none => exact hc
    | some g => exact Or.inl rfl
  · exact Or.inr ⟨f, rfl, ht⟩

/-- Rebasing a program with extern and override tables that differ only by traps. -/
theorem TrapsOnly.rebase_both (P : Program) (b : BitVec 64)
    {X₁ X₂ O₁ O₂ : String → Option (State → State)}
    (hX : HooksTrapOnly X₁ X₂) (hO : HooksTrapOnly O₁ O₂) :
    TrapsOnly (P.rebase b X₁ O₁) (P.rebase b X₂ O₂) where
  base := rfl
  code := rfl
  hook pc := by
    dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase]
    refine or_predOnly_both (findSome?_predOnly _ fun ⟨n, o⟩ => ?_)
      (findSome?_predOnly _ fun ⟨n, o⟩ => ?_)
    · dsimp only; split
      · exact hX n
      · exact Or.inl rfl
    · dsimp only; split
      · exact hO n
      · exact Or.inl rfl

/-- Rebasing a program with two extern hook tables that differ only by traps. -/
theorem TrapsOnly.rebase (P : Program) (b : BitVec 64) {X₁ X₂ : String → Option (State → State)}
    (h : HooksTrapOnly X₁ X₂) (O : String → Option (State → State) := fun _ => none) :
    TrapsOnly (P.rebase b X₁ O) (P.rebase b X₂ O) :=
  TrapsOnly.rebase_both P b h (.refl O)

/-- Rebasing a program with extern and override tables that differ only by panics or traps. -/
theorem PanicsOrTrapsOnly.rebase_both (P : Program) (b : BitVec 64)
    {X₁ X₂ O₁ O₂ : String → Option (State → State)}
    (hX : HooksPanicOrTrapOnly X₁ X₂) (hO : HooksPanicOrTrapOnly O₁ O₂) :
    PanicsOrTrapsOnly (P.rebase b X₁ O₁) (P.rebase b X₂ O₂) where
  base := rfl
  code := rfl
  hook pc := by
    dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase]
    refine or_predOnly_both (findSome?_predOnly _ fun ⟨n, o⟩ => ?_)
      (findSome?_predOnly _ fun ⟨n, o⟩ => ?_)
    · dsimp only; split
      · exact hX n
      · exact Or.inl rfl
    · dsimp only; split
      · exact hO n
      · exact Or.inl rfl

/-- Rebasing a program with two extern hook tables that differ only by panics or traps. -/
theorem PanicsOrTrapsOnly.rebase (P : Program) (b : BitVec 64)
    {X₁ X₂ : String → Option (State → State)}
    (h : HooksPanicOrTrapOnly X₁ X₂) (O : String → Option (State → State) := fun _ => none) :
    PanicsOrTrapsOnly (P.rebase b X₁ O) (P.rebase b X₂ O) :=
  PanicsOrTrapsOnly.rebase_both P b h (.refl O)

/-- `X` with every symbol name satisfying `p` replaced by the hook `trap`. -/
def trapAt (p : String → Bool) (trap : State → State) (X : String → Option (State → State)) :
    String → Option (State → State) :=
  fun n => if p n then some trap else X n

/-- `X` with every symbol name satisfying `p` mapped to `Rust.panicked`. -/
def panicAt (p : String → Bool) (X : String → Option (State → State)) :
    String → Option (State → State) :=
  trapAt p Rust.panicked X

theorem withPanics_eq_panicAt (X : String → Option (State → State)) :
    Rust.withPanics X = panicAt Rust.isPanicSymbol X := rfl

theorem HooksTrapOnly.trapAt {p : String → Bool} {trap : State → State} (ht : IsTrap trap)
    (X : String → Option (State → State)) :
    HooksTrapOnly (ProofLib.Variant.trapAt p trap X) X := by
  intro n
  by_cases hn : p n = true
  · exact Or.inr ⟨trap, by simp [ProofLib.Variant.trapAt, hn], ht⟩
  · exact Or.inl (by simp [ProofLib.Variant.trapAt, hn])

theorem HooksPanicOrTrapOnly.trapAt {p : String → Bool} {trap : State → State}
    (ht : IsPanicOrTrap trap) (X : String → Option (State → State)) :
    HooksPanicOrTrapOnly (ProofLib.Variant.trapAt p trap X) X := by
  intro n
  by_cases hn : p n = true
  · exact Or.inr ⟨trap, by simp [ProofLib.Variant.trapAt, hn], ht⟩
  · exact Or.inl (by simp [ProofLib.Variant.trapAt, hn])

theorem HooksPanicOrTrapOnly.panicAt (p : String → Bool) (X : String → Option (State → State)) :
    HooksPanicOrTrapOnly (ProofLib.Variant.panicAt p X) X :=
  HooksPanicOrTrapOnly.trapAt panicked_isPanicOrTrap X

/-- Replacing panic stubs `panicAt p X` with `trapAt p g X` (or any table agreeing outside `p`)
    satisfies `HooksPanicOrTrapOnly`. -/
theorem HooksPanicOrTrapOnly.panicAt_replace (p : String → Bool)
    (g : String → Option (State → State)) (X : String → Option (State → State)) :
    HooksPanicOrTrapOnly (ProofLib.Variant.panicAt p X) (fun n => if p n then g n else X n) := by
  intro n
  by_cases hn : p n = true
  · exact Or.inr ⟨Rust.panicked, by simp [ProofLib.Variant.panicAt, ProofLib.Variant.trapAt, hn],
      panicked_isPanicOrTrap⟩
  · exact Or.inl (by simp [ProofLib.Variant.panicAt, ProofLib.Variant.trapAt, hn])

/-- `Rust.withPanics X` differs from `X` only by panic hooks. -/
theorem HooksPanicOrTrapOnly.withPanics_left (X : String → Option (State → State)) :
    HooksPanicOrTrapOnly (Rust.withPanics X) X :=
  HooksPanicOrTrapOnly.panicAt Rust.isPanicSymbol X

/-- Adding identical `hookMap` entries on top of two fallback tables preserves `HooksTrapOnly`. -/
theorem HooksTrapOnly.hookMap (entries : List (String × (State → State)))
    {X₁ X₂ : String → Option (State → State)} (h : HooksTrapOnly X₁ X₂) :
    HooksTrapOnly (ProofLib.hookMap entries X₁) (ProofLib.hookMap entries X₂) := by
  induction entries with
  | nil => exact h
  | cons p rest ih =>
    rcases p with ⟨n, f⟩
    intro m
    by_cases hm : m = n
    · subst hm
      exact Or.inl (by simp only [ProofLib.hookMap_cons_self])
    · simp only [ProofLib.hookMap_cons_of_ne hm]
      exact ih m

/-- Prepending `hookMap` entries that are all traps gives `HooksTrapOnly (hookMap entries X) X`. -/
theorem HooksTrapOnly.hookMap_traps (entries : List (String × (State → State)))
    (htraps : ∀ p ∈ entries, IsTrap p.2) (X : String → Option (State → State)) :
    HooksTrapOnly (ProofLib.hookMap entries X) X := by
  induction entries with
  | nil => exact .refl X
  | cons p rest ih =>
    rcases p with ⟨n, f⟩
    intro m
    by_cases hm : m = n
    · subst hm
      exact Or.inr ⟨f, ProofLib.hookMap_cons_self m f rest X, htraps (m, f) List.mem_cons_self⟩
    · simp only [ProofLib.hookMap_cons_of_ne hm]
      exact ih (fun q hq => htraps q (List.mem_cons_of_mem _ hq)) m

/-- Adding identical `hookMap` entries on top of two fallback tables preserves
    `HooksPanicOrTrapOnly`. -/
theorem HooksPanicOrTrapOnly.hookMap (entries : List (String × (State → State)))
    {X₁ X₂ : String → Option (State → State)} (h : HooksPanicOrTrapOnly X₁ X₂) :
    HooksPanicOrTrapOnly (ProofLib.hookMap entries X₁) (ProofLib.hookMap entries X₂) := by
  induction entries with
  | nil => exact h
  | cons p rest ih =>
    rcases p with ⟨n, f⟩
    intro m
    by_cases hm : m = n
    · subst hm
      exact Or.inl (by simp only [ProofLib.hookMap_cons_self])
    · simp only [ProofLib.hookMap_cons_of_ne hm]
      exact ih m

end ProofLib.Variant

namespace ProofLib
export ProofLib.Variant (
  OutcomeStatus NonPanicOutcomeStatus IsTrap IsPanicOrTrap trapHook trapHook_isTrap
  trapHook_isPanicOrTrap panicked_isPanicOrTrap TrapsOnly PanicsOrTrapsOnly
  HooksTrapOnly HooksPanicOrTrapOnly trapAt panicAt withPanics_eq_panicAt
)
end ProofLib

/-- `trap_transfer h using tac` proves a statement about a program `P₂` from `h`, the same
    statement about a variant `P₁` with extra trapping or panicking hooks, by applying
    `subroutine_ok.of_trapsOnly` / `subroutine_ok.of_panicsOrTrapsOnly` and their siblings,
    descending through `∀`, `→`, `Prop` structures, and definitions. `tac` must close the
    `TrapsOnly P₁ P₂` or `PanicsOrTrapsOnly P₁ P₂` side goals. -/
syntax (name := trapTransfer) "trap_transfer " term " using " tacticSeq : tactic

end

public meta section

namespace ProofLib.Variant

open Lean Meta Elab Tactic

/-- The `TrapsOnly` transfer lemmas tried at a leaf judgement, in order. -/
def trapTransferLemmas : List Name :=
  [``_root_.Arm64.subroutine_ok.of_trapsOnly, ``_root_.Arm64.Program.subroutineOk.of_trapsOnly,
    ``_root_.Arm64.subroutine_ok.of_trapsOnly_eq, ``_root_.ProofLib.SepWPp.of_trapsOnly,
    ``_root_.ProofLib.SepWP.of_trapsOnly, ``_root_.Arm64.raw_subroutine_ok.of_trapsOnly,
    ``_root_.Arm64.Program.rawSubroutineOk.of_trapsOnly,
    ``_root_.Arm64.raw_subroutine_ok.of_trapsOnly_eq, ``_root_.Arm64.code_ok.of_trapsOnly,
    ``_root_.Arm64.exit_ok.of_trapsOnly, ``reaches_outcome.of_trapsOnly,
    ``_root_.Arm64.reaches_pc.of_trapsOnly, ``_root_.Arm64.exits_with.of_trapsOnly]

/-- The `PanicsOrTrapsOnly` transfer lemmas tried when `TrapsOnly` does not close the side goal. -/
def panicOrTrapTransferLemmas : List Name :=
  [``_root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly,
    ``_root_.Arm64.Program.subroutineOk.of_panicsOrTrapsOnly,
    ``_root_.Arm64.subroutine_ok.of_panicsOrTrapsOnly_eq,
    ``_root_.ProofLib.SepWP.of_panicsOrTrapsOnly,
    ``_root_.Arm64.raw_subroutine_ok.of_panicsOrTrapsOnly,
    ``_root_.Arm64.Program.rawSubroutineOk.of_panicsOrTrapsOnly,
    ``_root_.Arm64.raw_subroutine_ok.of_panicsOrTrapsOnly_eq,
    ``_root_.Arm64.code_ok.of_panicsOrTrapsOnly, ``_root_.Arm64.exit_ok.of_panicsOrTrapsOnly,
    ``_root_.Arm64.reaches_pc.of_panicsOrTrapsOnly, ``_root_.Arm64.exits_with.of_panicsOrTrapsOnly]

private def closeTransferSideGoal (disc : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (gi : MVarId) : TacticM Unit := do
  let ty ← instantiateMVars (← gi.getType)
  if ty.isAppOf ``TrapsOnly || ty.isAppOf ``PanicsOrTrapsOnly then
    let runDisc (g : MVarId) : TacticM (List MVarId) := do
      Term.withoutErrToSorry <| withTheReader Term.Context
        (fun c => { c with errToSorry := false }) <| evalTacticAt (← `(tactic| ($disc))) g
    let s ← saveState
    try
      let remaining ← runDisc gi
      if remaining.isEmpty then return
      restoreState s
    catch _ => restoreState s
    let remaining ← Term.withoutErrToSorry <| withTheReader Term.Context
      (fun c => { c with errToSorry := false }) <|
      evalTacticAt (← `(tactic| (try simp only [wp_unfold]; ($disc)))) gi
    unless remaining.isEmpty do throwError "TrapsOnly / PanicsOrTrapsOnly side goal not closed"
  else
    let remaining ← Term.withoutErrToSorry <| withTheReader Term.Context
      (fun c => { c with errToSorry := false }) <|
      evalTacticAt (← `(tactic| first
        | rfl
        | (simp only [wp_unfold]; done)
        | (intro _ _ _ _ hp; exact _root_.Arm64.not_satisfies_false_sepConj hp))) gi
    unless remaining.isEmpty do throwError "unexpected side goal"

private partial def unfoldUntilAppOf (ty : Expr) (c : Name) (fuel : Nat := 16) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isAppOf c || fuel == 0 then return ty
  match ← unfoldDefinition? ty with
  | some ty' => unfoldUntilAppOf ty' c (fuel - 1)
  | none => return ty

/-- Close goal `g` (a statement about `P₂`) from `h` (the same statement about `P₁`). `disc` proves
    the `TrapsOnly` or `PanicsOrTrapsOnly` side goals. -/
partial def trapTransferCore (disc : TSyntax ``Lean.Parser.Tactic.tacticSeq) (g : MVarId)
    (h : Expr) (fuel : Nat := 16) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "trap_transfer: gave up (too many unfoldings)"
  let tgt ← whnfR (← g.getType)
  if tgt.isForall then
    let (x, g') ← g.intro1
    return ← trapTransferCore disc g' (mkApp h (.fvar x)) fuel
  for lem in trapTransferLemmas ++ panicOrTrapTransferLemmas do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
      let mut matchedH := false
      let mut rest := #[]
      for gi in gs do
        let gty ← instantiateMVars (← gi.getType)
        if gty.isAppOf ``TrapsOnly || gty.isAppOf ``PanicsOrTrapsOnly then
          rest := rest.push gi
        else if !matchedH && (← isDefEq gty (← inferType h)) then
          gi.assign h
          matchedH := true
        else if !(← gi.isAssigned) then
          rest := rest.push gi
      unless matchedH do throwError "premise did not match hypothesis"
      for gi in rest do
        unless ← gi.isAssigned do
          closeTransferSideGoal disc gi
      return
    catch _ => restoreState s
  let env ← getEnv
  match tgt.getAppFn with
  | .const c _ =>
    if isStructure env c then
      let gs ← g.constructor
      let fields := getStructureFields env c
      let hty ← unfoldUntilAppOf (← inferType h) c
      unless hty.isAppOf c do throwError "trap_transfer: hypothesis is not a `{c}`"
      for (gi, f) in gs.zip fields.toList do
        trapTransferCore disc gi (← mkProjection h f) fuel
      for gi in gs.drop fields.size do
        unless ← gi.isAssigned do
          throwError "trap_transfer: unexpected goal{indentExpr (← gi.getType)}"
      return
    match ← unfoldDefinition? tgt with
    | some tgt' => trapTransferCore disc (← g.change tgt') h (fuel - 1)
    | none => throwError "trap_transfer: no transfer lemma applies to{indentExpr tgt}"
  | _ => throwError "trap_transfer: no transfer lemma applies to{indentExpr tgt}"

@[tactic trapTransfer]
def evalTrapTransfer : Tactic := fun stx => do
  match stx with
  | `(tactic| trap_transfer $h using $disc) =>
    let g ← getMainGoal
    let h ← g.withContext <| Term.elabTerm h none
    trapTransferCore disc g h
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

end ProofLib.Variant

end
