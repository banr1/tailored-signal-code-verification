/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome

/-!
# Budget-Threaded Handshake `skip_field` Leaf Specifications

Total-correctness (`RustCliAllocBudget M`) contracts (`skipField3Spec`, `skipField3SpecAt` under
`FitsEnv M lim st (SkipFieldEnv x)`), depth-induction combinators, and the `.startGroup` loop
invariant precondition `skipGroupLoopPre3` for `prost::encoding::skip_field::<&mut &[u8]> [local#5]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec (skipField)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  SkipFieldGhost decodeErrorHookStackX sliceCursorAfter sliceCursorAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  HighCalleeSaved3 growOneMessageKeyName skipBelow3 skipErrRest3 skipField3Stack skipField6Name
  skipLeafRest3
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv skipFieldSpecGen)

/-- Budget-threaded contract of `prost::encoding::skip_field::<&mut &[u8]>` in terms of
`LibsignalProtoCodec.skipField` under Regime A (`skipField3Stack`). -/
def skipField3Spec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SkipFieldGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipFieldEnv x)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (skipField3Stack x.depth)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipFieldEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (skipField3Stack x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem skipField3Spec_eq_gen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    skipField3Spec A lim = skipFieldSpecGen A lim (48 + decodeErrorHookStackX) :=
  rfl

/-- Depth- and predicate-specialized budget-threaded `skip_field` contract at `skipField3Stack`. -/
def skipField3SpecAt {M : AllocCostModel} (A : RustCliAllocBudget M)
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
      A.pool lim st s ∗ stackAt s.sp (skipField3Stack depth)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipFieldEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (skipField3Stack depth) ∗
      match skipField (2 * x.bs.length + 2) depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-! ## Plain `subroutine_ok` Combinators -/

theorem subroutine_ok_skipField3_or {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (skipField3SpecAt A lim depth P))
    (h2 : subroutine_ok prog entry (skipField3SpecAt A lim depth Q)) :
    subroutine_ok prog entry (skipField3SpecAt A lim depth (fun x => P x ∨ Q x)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipField3_imp {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (skipField3SpecAt A lim depth Q)) :
    subroutine_ok prog entry (skipField3SpecAt A lim depth P) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem skipField3SpecAt_reaches_outcome_eq {M : AllocCostModel}
    (prog : Program) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    reaches_outcome prog (skipField3SpecAt A lim x.depth P) (x, st) R s0 s0 =
      reaches_outcome prog (skipField3Spec A lim) (x, st) R s0 s0 :=
  reaches_outcome_eq_of_parts_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

theorem subroutine_ok_skipField3Spec_of_at_depth {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry (skipField3SpecAt A lim depth (fun _ => True))) :
    subroutine_ok prog entry (skipField3Spec A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

/-! ## `withLsCodeLoaded` (`_lscl`) Combinators -/

theorem subroutine_ok_skipField3_or_lscl {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (withLsCodeLoaded pl (skipField3SpecAt A lim depth P)))
    (h2 : subroutine_ok prog entry (withLsCodeLoaded pl (skipField3SpecAt A lim depth Q))) :
    subroutine_ok prog entry
      (withLsCodeLoaded pl (skipField3SpecAt A lim depth (fun x => P x ∨ Q x))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipField3_imp_lscl {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (skipField3SpecAt A lim depth Q))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (skipField3SpecAt A lim depth P)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem skipField3SpecAt_reaches_outcome_lscl_eq {M : AllocCostModel}
    (pl : Obj.MultiPlacement) (prog : Program)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCodeLoaded pl (skipField3SpecAt A lim x.depth P)) (x, st) R s0 s0 =
      reaches_outcome prog (withLsCodeLoaded pl (skipField3Spec A lim)) (x, st) R s0 s0 :=
  reaches_outcome_eq_of_parts_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

theorem subroutine_ok_skipField3Spec_of_at_depth_lscl {M : AllocCostModel}
    {pl : Obj.MultiPlacement} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry (withLsCodeLoaded pl (skipField3SpecAt A lim depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (skipField3Spec A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

/-! ## `withLsCl lsmpl` (`_placed`) Combinators -/

theorem subroutine_ok_skipField3_or_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A lim depth P)))
    (h2 : subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A lim depth Q))) :
    subroutine_ok prog entry
      (withLsCl lsmpl (skipField3SpecAt A lim depth (fun x => P x ∨ Q x))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipField3_imp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A lim depth Q))) :
    subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A lim depth P)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem skipField3SpecAt_reaches_outcome_placed_eq [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCl lsmpl (skipField3SpecAt A lim x.depth P)) (x, st) R s0 s0 =
      reaches_outcome prog (withLsCl lsmpl (skipField3Spec A lim)) (x, st) R s0 s0 :=
  reaches_outcome_eq_of_parts_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

theorem subroutine_ok_skipField3Spec_of_at_depth_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry (withLsCl lsmpl (skipField3SpecAt A lim depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCl lsmpl (skipField3Spec A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome (x, st) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

/-! ## `StartGroup` Loop Invariant Precondition -/

/-- Budget-threaded `StartGroup` loop invariant precondition (`A.pool lim st s` at current `s`). -/
abbrev skipGroupLoopPre3 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (d : Nat)
    (bufRef slot ptr v_pad : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool lim st s ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ v_pad) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelow3 s0.sp (d + 1)

theorem skipGroupLoopPre3_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (d : Nat)
    (bufRef slot ptr v_pad : BitVec 64) (bs cur : List (BitVec 8)) :
    skipGroupLoopPre3 A lim st s0 s d bufRef slot ptr v_pad bs cur =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.skipGroupLoopPre3
        (A.atState lim st s) s0 d bufRef slot ptr v_pad bs cur :=
  rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget
