/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
import ProofLib.Hoare.Model

/-!
# Proof-Side Hoare Judgments and Outcome Combinators

Defines total-correctness block and unaligned-entry subroutine judgments (`reaches_pc`, `code_ok`,
`raw_subroutine_ok`, `Program.rawSubroutineOk`) alongside trace-agnostic introduction, elimination,
and consequence combinators on `reaches_outcome` and `subroutine_ok`.
-/

namespace Arm64

@[expose] public section

/-- If `prog.CodeLoaded s0.mem` holds, execution of `prog` from `s0` reaches either a running state
    `sf` at `target_pc` satisfying `post sf` or an `.OutOfMemory` state satisfying `oom sf`. -/
def reaches_pc (prog : Program) (target_pc : BitVec 64) (s0 : State) (post : State → Prop)
    (oom : State → Prop := fun _ => False) : Prop :=
  prog.CodeLoaded s0.mem →
    ∃ sf, Steps prog s0 sf ∧
      ((sf.pc = target_pc ∧ sf.status = .Running ∧ post sf) ∨ (sf.status = .OutOfMemory ∧ oom sf))

/-- Framed Hoare triple for a code block from `entry_pc` to `exit_pc`. -/
def code_ok {α : Type} (prog : Program) (entry_pc exit_pc : BitVec 64) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    s0.pc = entry_pc →
    s0.status = .Running →
    (s0.mem ⊨ spec.pre x s0 ∗ R) →
    reaches_pc prog exit_pc s0
      (fun sf => sf.mem ⊨ spec.post x s0 sf ∗ R)
      (fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)

end

public section

/-- Framed total-correctness subroutine Hoare triple without the AAPCS64 entry alignment assumption
    `s0.spAligned = true`. Prefer `subroutine_ok` for standard AAPCS64 functions. -/
def raw_subroutine_ok {α : Type} (prog : Program) (entry_pc : BitVec 64) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    s0.pc = entry_pc →
    s0.status = .Running →
    (s0.mem ⊨ spec.pre x s0 ∗ R) →
    reaches_outcome prog spec x R s0 s0

/-- Unfolding characterization of `raw_subroutine_ok`. -/
theorem raw_subroutine_ok_iff {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} :
    raw_subroutine_ok prog entry_pc spec ↔
      ∀ (x : α) (R : SepProp) (s0 : State),
        s0.pc = entry_pc →
        s0.status = .Running →
        (s0.mem ⊨ spec.pre x s0 ∗ R) →
        reaches_outcome prog spec x R s0 s0 :=
  Iff.rfl

end

@[expose] public section

/-- Position-independent `raw_subroutine_ok` judgment by symbol name, instantiating `spec` at
    `prog.base`. -/
abbrev Program.rawSubroutineOk {S α : Type} [ToBaseSpec S α] (prog : Program) (fnName : String)
    (spec : S) : Prop :=
  raw_subroutine_ok prog (prog.fnAddr fnName) (ToBaseSpec.toSpec spec prog.base)

/-- Zero-step introduction rule for `reaches_outcome`. -/
theorem reaches_outcome.of_outcome {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {R : SepProp} {s0 s : State}
    (hout : SubroutineOutcome spec x R s0 s) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_iff.mpr fun _ => ⟨s, Steps.refl s, hout⟩

/-- Introduces `prog.CodeLoaded s.mem` when proving `reaches_outcome`. -/
theorem reaches_outcome.of_codeLoaded {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {R : SepProp} {s0 s : State}
    (h : prog.CodeLoaded s.mem → reaches_outcome prog spec x R s0 s) :
    reaches_outcome prog spec x R s0 s :=
  reaches_outcome_iff.mpr fun hL => reaches_outcome_iff.mp (h hL) hL

/-- Consequence rule on `reaches_outcome` mapping `SubroutineOutcome` pointwise. -/
theorem reaches_outcome.mono_outcome {α β : Type} {prog : Program}
    {spec₁ : Spec α} {spec₂ : Spec β} {x : α} {y : β} {R₁ R₂ : SepProp} {s0 s : State}
    (h : reaches_outcome prog spec₁ x R₁ s0 s)
    (hm : ∀ sf, SubroutineOutcome spec₁ x R₁ s0 sf → SubroutineOutcome spec₂ y R₂ s0 sf) :
    reaches_outcome prog spec₂ y R₂ s0 s := by
  refine reaches_outcome_iff.mpr fun hL => ?_
  rcases reaches_outcome_iff.mp h hL with ⟨sf, hsteps, hout⟩
  exact ⟨sf, hsteps, hm sf hout⟩

/-- Introduces `subroutine_ok` with access to `prog.CodeLoaded s0.mem`. -/
theorem subroutine_ok.of_codeLoaded {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      prog.CodeLoaded s0.mem →
      reaches_outcome prog spec x R s0 s0) :
    subroutine_ok prog entry_pc spec :=
  subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre hsp =>
    reaches_outcome.of_codeLoaded (h x R s0 hpc hrun hpre hsp)

theorem subroutine_ok.to_outcome {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry_pc spec) :
    ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      reaches_outcome prog spec x R s0 s0 := subroutine_ok_iff.mp h

theorem raw_subroutine_ok.to_outcome {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : raw_subroutine_ok prog entry_pc spec) :
    ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      reaches_outcome prog spec x R s0 s0 := h

/-- Eliminates `subroutine_ok` and transforms its `SubroutineOutcome` pointwise. -/
theorem subroutine_ok.mono_outcome {α β : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec₁ : Spec α} {spec₂ : Spec β} {y : β} {R₂ : SepProp}
    (h : subroutine_ok prog entry_pc spec₁) (x : α) (R₁ : SepProp) (s0 : State)
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec₁.pre x s0 ∗ R₁)
    (hsp : s0.spAligned = true)
    (hm : ∀ sf, SubroutineOutcome spec₁ x R₁ s0 sf → SubroutineOutcome spec₂ y R₂ s0 sf) :
    reaches_outcome prog spec₂ y R₂ s0 s0 :=
  (subroutine_ok_iff.mp h x R₁ s0 hpc hrun hpre hsp).mono_outcome hm

/-- Consequence rule on `reaches_outcome` absorbing an intermediate frame `F` across non-exiting
    return, panic, and OOM outcomes. -/
theorem reaches_outcome_drop_frame_oom {α β : Type} {prog : Program}
    {spec : Spec α} {spec' : Spec β} {x : α} {y : β} {F R : SepProp} {s0 s : State}
    (h : reaches_outcome prog spec x (F ∗ R) s0 s)
    (hpost : ∀ sf, Returned s0 sf → CallingConventionPreserved s0 sf →
      (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (hpan : ∀ sf, sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R))
    (hoom : ∀ sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R))
    (h_no_exit : ∀ code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ (F ∗ R)) := by
        rintro _ _ _ ⟨_, ⟨_, _, _, _, ⟨_, hf⟩, _⟩, _⟩; exact hf) :
    reaches_outcome prog spec' y R s0 s :=
  h.mono_outcome fun sf hout => by
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
    · exact Or.inl ⟨hret, hcc, hpost sf hret hcc hq⟩
    · exact Or.inr (Or.inl ⟨hp_st, hpan sf hp_st hq⟩)
    · exact False.elim (h_no_exit code sf hex_st hq)
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hoom sf ho_st hq⟩))

end

end Arm64
