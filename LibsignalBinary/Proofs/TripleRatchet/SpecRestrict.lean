/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs

/-!
# Pure Precondition Restriction on Specifications (`Spec.restrictPre`)

Defines `Spec.restrictPre spec P` (prepending `⌜P x⌝` to `spec.pre`) and `Spec.withVRegs`, with
weakening lemmas for `subroutine_ok` and `region_ok` used to specialize general post-quantum ratchet
contracts to empty-state contracts (`spqrRecvEmptySpec`, `TryDecryptEmptyRunStmt`, `RecordDecryptEmptyRunStmt`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib

/-- A `⌜True⌝` conjunct in front of a contract's precondition changes nothing. -/
theorem spec_pre_true {α : Type} (spec : Spec α) :
    { spec with pre := fun x s => ⌜True⌝ ∗ spec.pre x s } = spec := by
  cases spec
  simp only [pure_true, emp_sepConj]

end CryptoVerification.LibsignalTripleRatchet

namespace Arm64.Spec

open ProofLib

/-- `spec` with the pure fact `P x` added to its precondition. -/
def restrictPre {α : Type} (spec : Spec α) (P : α → Prop) : Spec α :=
  { spec with pre := fun x s => ⌜P x⌝ ∗ spec.pre x s }

theorem restrictPre_true {α : Type} (spec : Spec α) : spec.restrictPre (fun _ => True) = spec :=
  CryptoVerification.LibsignalTripleRatchet.spec_pre_true spec

theorem satisfies_restrictPre {α : Type} {spec : Spec α} {P : α → Prop} {x : α} {s : State}
    {R : SepProp} {m : Memory} :
    (m ⊨ (spec.restrictPre P).pre x s ∗ R) ↔ (P x ∧ (m ⊨ spec.pre x s ∗ R)) := by
  show (m ⊨ (⌜P x⌝ ∗ spec.pre x s) ∗ R) ↔ _
  rw [sepConj_assoc, satisfies_pure_sepConj]

/-- A `subroutine_ok` for `spec.restrictPre P` from one for `spec` that may use `P x`. -/
theorem subroutine_ok_restrictPre_of {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {P : α → Prop}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), P x → s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true → reaches_outcome prog spec x R s0 s0) :
    subroutine_ok prog entry (spec.restrictPre P) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hP, hpre⟩ := satisfies_restrictPre.mp hpre
  exact (h x R s0 hP hpc hrun hpre hsp).mono_outcome fun _ hout => hout

/-- Restricting the precondition weakens a `subroutine_ok`. -/
theorem subroutine_ok_restrictPre {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (P : α → Prop) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.restrictPre P) :=
  subroutine_ok_restrictPre_of fun x R _ _ hpc hrun hpre hsp =>
    subroutine_ok_apply_outcome h x R hpc hrun hpre hsp

/-- A `region_ok` for `spec.restrictPre P` from one for `spec` that may use `P x`. -/
theorem region_ok_restrictPre_of {α : Type} {prog : Program} {entry exit : BitVec 64}
    {spec : Spec α} {P : α → Prop}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), P x → s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → prog.CodeLoaded s0.mem →
      ∃ sf, Steps prog s0 sf ∧
        ((sf.pc = exit ∧ sf.status = .Running ∧ (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∨
         (sf.status = .Panicked ∧ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R)))) :
    CryptoVerification.LibsignalTripleRatchet.region_ok prog entry exit (spec.restrictPre P) := by
  intro x R s0 hpc hrun hpre hL
  obtain ⟨hP, hpre⟩ := satisfies_restrictPre.mp hpre
  exact h x R s0 hP hpc hrun hpre hL

/-- Restricting the precondition weakens a `region_ok`. -/
theorem region_ok_restrictPre {α : Type} {prog : Program} {entry exit : BitVec 64}
    {spec : Spec α} (P : α → Prop)
    (h : CryptoVerification.LibsignalTripleRatchet.region_ok prog entry exit spec) :
    CryptoVerification.LibsignalTripleRatchet.region_ok prog entry exit (spec.restrictPre P) :=
  region_ok_restrictPre_of fun x R s0 _ hpc hrun hpre hL => h x R s0 hpc hrun hpre hL

/-- `spec` with `calleeSavedVRegs sf = calleeSavedVRegs s0` conjoined to its postcondition. -/
def withVRegs {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜calleeSavedVRegs sf = calleeSavedVRegs s0⌝ ∗ spec.post x s0 sf }

end Arm64.Spec

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr

/-- The trusted `spqrRecvEmptySpec` is `spqrRecvSpec` restricted to an empty state. -/
theorem spqrRecvEmptySpec_eq (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) :
    spqrRecvEmptySpec A S img = (spqrRecvSpec A S img).restrictPre (·.1.bytes = []) :=
  rfl

-- `TryDecryptEmptyRunStmt` is `tryDecryptSpec` restricted to an empty PQ state.
example (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    { tryDecryptSpec C A ctl uuidTryParse S img with
      pre := fun x s =>
        ⌜x.st.pqRatchetState = []⌝ ∗ (tryDecryptSpec C A ctl uuidTryParse S img).pre x s } =
      (tryDecryptSpec C A ctl uuidTryParse S img).restrictPre (·.st.pqRatchetState = []) :=
  rfl

-- `RecordDecryptEmptyRunStmt` is `recordDecryptSpec` restricted to an empty PQ state.
example (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    { recordDecryptSpec C A ctl uuidTryParse S img with
      pre := fun x s =>
        ⌜x.st.pqRatchetState = []⌝ ∗ (recordDecryptSpec C A ctl uuidTryParse S img).pre x s } =
      (recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (·.st.pqRatchetState = []) :=
  rfl

end CryptoVerification.LibsignalTripleRatchet
