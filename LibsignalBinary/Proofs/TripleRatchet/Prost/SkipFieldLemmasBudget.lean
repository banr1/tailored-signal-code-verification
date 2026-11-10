/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas

/-!
# Budget-Threaded `skip_field` Induction Combinators

Depth- and predicate-specialized `skipFieldSpecAtX` contract, relocatable disjunction/implication
combinators on `withLsCodeLoaded`, and the `StartGroup` loop invariant precondition `skipGroupLoopPreX`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoVerification (withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec (skipField)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SkipFieldGhost skipFieldStackX sliceCursorAt sliceCursorAfter skipBelowX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv)

/-- Depth- and predicate-specialized budget-threaded `skip_field` contract at `skipFieldStackX`. -/
def skipFieldSpecAtX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (depth : Nat) (P : SkipFieldGhost → Prop) :
    Spec (SkipFieldGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜P x ∧ x.depth = depth ∧
      (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth ∧ depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipFieldEnv x)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (skipFieldStackX depth)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipFieldEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (skipFieldStackX depth) ∗
      match skipField (2 * x.bs.length + 2) depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem subroutine_ok_skipFieldX_or_lscl {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A lim depth P)))
    (h2 : subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A lim depth Q))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (skipFieldSpecAtX A lim depth (fun x => P x ∨ Q x))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipFieldX_imp_lscl {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A lim depth Q))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (skipFieldSpecAtX A lim depth P)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipFieldSpecAtX, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

/-- Budget-threaded `StartGroup` loop invariant precondition (`A.pool lim st s` at current `s`). -/
abbrev skipGroupLoopPreX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (d : Nat)
    (bufRef slot ptr : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool lim st s ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelowX s0.sp (d + 1)

end LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget
