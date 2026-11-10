/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `stringCloneBudgetSpec` Lift to `withFds`

Lifts `HookOk` and `HookSat` on `stringCloneBudgetSpec M A lim` to `withFds A` whenever the hook
preserves `FdsGe3Closed` (or `State.fs`), or from a `withFdsGe3Closed (stringCloneBudgetSpec M A lim)`
contract when `lim.enforced = true`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone

open Arm64 ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed hookOk_withFdsGe3Closed hookOk_withFdsGe3Closed_of_fs_eq withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_pool_unenforced withFds_repAlloc)

private theorem hookOk_of_pre_post {α : Type} {f : State → State} {spec1 spec2 : Spec α}
    {Q : α → State → Prop}
    (hok : HookOk f spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    HookOk f spec2 := by
  intro x R s0 hrun hpre2 hsp
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre1 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 (f s0) hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem hookSat_of_hookOk_lift {α : Type} {hooks : String → Option (State → State)}
    {sym : String} {spec1 spec2 : Spec α}
    (hlift : ∀ f, HookOk f spec1 → HookOk f spec2)
    (hsat : HookSat hooks sym spec1) :
    HookSat hooks sym spec2 := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hlift f hok⟩

private theorem strClone_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 P3 Tail R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (P1 ∗ P2 ∗ P3 ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ R) :
    s0.mem ⊨ (⌜FdsGe3Closed s0.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ Tail)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ R =
      (⌜FdsGe3Closed s0.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ Tail)) ∗ R := by
    sep_ac_rfl
  rwa [hEq] at h

private theorem strClone_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 Tail R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail)) ∗ R) :
    sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h ⊢
  rcases h with ⟨evs, h⟩
  refine ⟨evs, ?_⟩
  rw [withFds_pool_enforced A henf]
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗
        ((P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosedF, h⟩

theorem hookOk_stringCloneBudget_withFds_of_enforced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {fn : State → State}
    (hokFd : HookOk fn (withFdsGe3Closed (stringCloneBudgetSpec M A lim))) :
    HookOk fn (stringCloneBudgetSpec M (withFds A) lim) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hokFd rfl rfl rfl ?_ ?_
  · rintro ⟨p, ret, g, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, stringCloneBudgetSpec, withFds_repAlloc] at hpre ⊢
    exact ⟨trivial, strClone_pre_enforced henf hpre⟩
  · rintro ⟨p, ret, g, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, stringCloneBudgetSpec, withFds_repAlloc] at hpost ⊢
    exact strClone_post_enforced henf hpost

theorem hookSat_stringCloneBudget_withFds_of_enforced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym (withFdsGe3Closed (stringCloneBudgetSpec M A lim))) :
    HookSat hooks sym (stringCloneBudgetSpec M (withFds A) lim) :=
  hookSat_of_hookOk_lift (fun _ => hookOk_stringCloneBudget_withFds_of_enforced henf) hsat

theorem hookOk_stringCloneBudget_withFds_of_unenforced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = false) {fn : State → State}
    (hok : HookOk fn (stringCloneBudgetSpec M A lim)) :
    HookOk fn (stringCloneBudgetSpec M (withFds A) lim) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨p, ret, g, st⟩ R s0 hpre
    dsimp only [stringCloneBudgetSpec, withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_unenforced A henf] at hpre
    exact ⟨trivial, hpre⟩
  · rintro ⟨p, ret, g, st⟩ R s0 sf _ hpost
    dsimp only [stringCloneBudgetSpec, withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rwa [withFds_pool_unenforced A henf]

theorem hookOk_stringCloneBudget_withFds_of_hokFd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn (stringCloneBudgetSpec M A lim))
    (hokFd : lim.enforced = true → HookOk fn (withFdsGe3Closed (stringCloneBudgetSpec M A lim))) :
    HookOk fn (stringCloneBudgetSpec M (withFds A) lim) := by
  cases henf : lim.enforced
  · exact hookOk_stringCloneBudget_withFds_of_unenforced henf hok
  · exact hookOk_stringCloneBudget_withFds_of_enforced henf (hokFd henf)

theorem hookSat_stringCloneBudget_withFds_of_hsatFd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym (stringCloneBudgetSpec M A lim))
    (hsatFd : lim.enforced = true →
      HookSat hooks sym (withFdsGe3Closed (stringCloneBudgetSpec M A lim))) :
    HookSat hooks sym (stringCloneBudgetSpec M (withFds A) lim) := by
  rcases hsat with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, hookOk_stringCloneBudget_withFds_of_hokFd hok (fun henf => ?_)⟩
  rcases hsatFd henf with ⟨fn', hfn', hokFd⟩
  have hEq : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
  exact hEq ▸ hokFd

theorem hookOk_stringCloneBudget_withFds_of_preserves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn (stringCloneBudgetSpec M A lim))
    (hpres : ∀ s0 : State, FdsGe3Closed s0.fs → FdsGe3Closed (fn s0).fs) :
    HookOk fn (stringCloneBudgetSpec M (withFds A) lim) :=
  hookOk_stringCloneBudget_withFds_of_hokFd hok (fun _ => hookOk_withFdsGe3Closed hpres hok)

/-- Lift `HookOk fn (stringCloneBudgetSpec M A lim)` to `withFds A` when `∀ s0, (fn s0).fs = s0.fs`. -/
theorem hookOk_stringCloneBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn (stringCloneBudgetSpec M A lim))
    (h_fs : ∀ s0 : State, (fn s0).fs = s0.fs) :
    HookOk fn (stringCloneBudgetSpec M (withFds A) lim) :=
  hookOk_stringCloneBudget_withFds_of_hokFd hok (fun _ => hookOk_withFdsGe3Closed_of_fs_eq h_fs hok)

theorem hookSat_stringCloneBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym (stringCloneBudgetSpec M A lim))
    (h_fs : ∀ fn, hooks sym = some fn → ∀ s0 : State, (fn s0).fs = s0.fs) :
    HookSat hooks sym (stringCloneBudgetSpec M (withFds A) lim) := by
  rcases hsat with ⟨fn, hfn, hok⟩
  exact ⟨fn, hfn, hookOk_stringCloneBudget_withFds hok (h_fs fn hfn)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
