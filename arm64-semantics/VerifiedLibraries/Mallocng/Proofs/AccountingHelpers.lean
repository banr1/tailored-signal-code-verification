/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cells
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses
public import VerifiedLibraries.Mallocng.Proofs.GhostToken
public import VerifiedLibraries.Mallocng.Proofs.Defs
public import VerifiedLibraries.Mallocng.Proofs.Common

/-!
# Nesting-Forest and Group-Count Accounting Helpers

Duplicate-free fiber-sum combinators, nesting-forest depth (`≤ 7`) descent lemmas, and global group
and `meta_area` page-count bounds (`emptyGroups_length_le`, `groups_length_le`,
`metaAreas_length_succ_le`) for mallocng.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## `Nodup` and Fiber-Sum Combinators -/

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
    have ⟨hxNotMem, hndRest⟩ := List.nodup_cons.mp hnd
    have ⟨ys1, ys2, hysEq⟩ := List.append_of_mem (hsub x List.mem_cons_self)
    have hsubRest : ∀ y ∈ rest, y ∈ ys1 ++ ys2 := by
      intro y hy
      have hyMem := hsub y (List.mem_cons_of_mem x hy)
      rw [hysEq, List.mem_append, List.mem_cons] at hyMem
      rcases hyMem with h1 | rfl | h2
      · exact List.mem_append_left _ h1
      · exact False.elim (hxNotMem hy)
      · exact List.mem_append_right _ h2
    have hle := ih hndRest hsubRest
    rw [hysEq]
    simp only [List.length_append, List.length_cons] at hle ⊢
    omega

private theorem sum_ite_beq_le_of_nodup {β : Type} [DecidableEq β] (b0 : β) (v : Nat)
    {ys : List β} (hnd : ys.Nodup) :
    (ys.map fun y => if b0 == y then v else 0).sum ≤ v := by
  induction ys with
  | nil => exact Nat.zero_le v
  | cons y rest ih =>
    have ⟨hyNotMem, hndRest⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hEq : b0 = y
    · subst hEq
      have hZero : (rest.map fun y' => if b0 == y' then v else 0).sum = 0 := by
        clear ih hnd hndRest
        induction rest with
        | nil => rfl
        | cons z zs ihz =>
          have hzNe : b0 ≠ z := fun h => hyNotMem (h ▸ List.mem_cons_self)
          have hzRest : b0 ∉ zs := fun h => hyNotMem (List.mem_cons_of_mem z h)
          simp only [List.map_cons, List.sum_cons, beq_false_of_ne hzNe, Bool.false_eq_true,
            ↓reduceIte, Nat.zero_add]
          exact ihz hzRest
      simp only [beq_self_eq_true, ↓reduceIte, hZero, Nat.add_zero]
      exact Nat.le_refl v
    · simp only [beq_false_of_ne hEq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih hndRest

theorem accounting_le_sum_of_mem {x : Nat} {xs : List Nat} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | htl
    · omega
    · have h := ih htl; omega

private theorem exists_of_all_eq_false {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.all p = false) : ∃ x ∈ xs, p x = false := by
  induction xs with
  | nil => simp at h
  | cons x rest ih =>
    simp only [List.all_cons, Bool.and_eq_false_iff] at h
    rcases h with hx | hrest
    · exact ⟨x, List.mem_cons_self, hx⟩
    · obtain ⟨y, hy, hyf⟩ := ih hrest
      exact ⟨y, List.mem_cons_of_mem x hy, hyf⟩

theorem accounting_length_filter_partition {α : Type} (p : α → Bool) (xs : List α) :
    xs.length = (xs.filter p).length + (xs.filter (fun x => !p x)).length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hp : p x = true
    · simp [List.filter, hp, ih]; omega
    · have hf : p x = false := Bool.eq_false_iff.mpr hp
      simp [List.filter, hf, ih]; omega

theorem accounting_sum_filter_partition {α : Type} (p : α → Bool) (f : α → Nat) (xs : List α) :
    (xs.map f).sum =
      ((xs.filter p).map f).sum + ((xs.filter (fun x => !p x)).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hp : p x = true
    · simp [List.filter, hp, ih]; omega
    · have hf : p x = false := Bool.eq_false_iff.mpr hp
      simp [List.filter, hf, ih]; omega

private theorem sum_map_add {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem accounting_sum_map_le {α : Type} {f g : α → Nat} {xs : List α}
    (hle : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle x List.mem_cons_self
    have h2 := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

theorem sum_filter_beq_le_of_nodup {α β : Type} [DecidableEq β]
    (f : α → β) (w : α → Nat) (xs : List α) {ys : List β} (hnd : ys.Nodup) :
    (ys.map fun y => ((xs.filter fun x => f x == y).map w).sum).sum ≤ (xs.map w).sum := by
  induction xs with
  | nil =>
    have hZ : ∀ y ∈ ys, ((([] : List α).filter fun x => f x == y).map w).sum ≤ 0 := by
      intro _ _; simp
    have hLe := accounting_sum_map_le hZ
    have hZeroSum : (ys.map fun _ => 0).sum = 0 := by
      clear hZ hLe hnd
      induction ys with
      | nil => rfl
      | cons _ tl ihy => simp only [List.map_cons, List.sum_cons, ihy, Nat.add_zero]
    rw [hZeroSum] at hLe
    exact Nat.le_trans hLe (Nat.zero_le _)
  | cons x rest ih =>
    have hSplit :
        (ys.map fun y => (((x :: rest).filter fun z => f z == y).map w).sum) =
        (ys.map fun y => (if f x == y then w x else 0) +
          ((rest.filter fun z => f z == y).map w).sum) := by
      refine List.map_congr_left fun y _ => ?_
      by_cases h : (f x == y) = true
      · simp [List.filter, h]
      · have hf : (f x == y) = false := Bool.eq_false_iff.mpr h
        simp [List.filter, hf]
    rw [hSplit, sum_map_add]
    have hHead := sum_ite_beq_le_of_nodup (f x) (w x) hnd
    have hTail := ih
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## Group Lookup Uniqueness and Nesting-Forest Depth (`≤ 7`) -/

theorem GroupWf.slot_wf {st : MallocngSt} {g : GroupDesc} (h : GroupWf st g) :
    ∀ idx : Nat, (hIdx : idx < g.slots.length) → SlotWf st g idx (g.slots[idx]'hIdx) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem mem_groups_eq_of_metaPtr {gs : List GroupDesc} (hnd : (gs.map (·.metaPtr)).Nodup)
    {g₁ g₂ : GroupDesc} (h₁ : g₁ ∈ gs) (h₂ : g₂ ∈ gs) (hm : g₁.metaPtr = g₂.metaPtr) :
    g₁ = g₂ := by
  induction gs with
  | nil => cases h₁
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact False.elim (hnd.1 (hm ▸ List.mem_map_of_mem h₂'))
    · exact False.elim (hnd.1 (hm.symm ▸ List.mem_map_of_mem h₁'))
    · exact ih hnd.2 h₁' h₂'

private theorem find?_metaPtr_of_mem {gs : List GroupDesc} (hnd : (gs.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ gs) :
    gs.find? (·.metaPtr == g.metaPtr) = some g := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hg with rfl | htl
    · simp [List.find?]
    · have hNe : (hd.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne (fun hEq => hnd.1 (hEq ▸ List.mem_map_of_mem htl))
      simp [List.find?, hNe, ih hnd.2 htl]

theorem findGroupByMeta_of_mem {st : MallocngSt} (hnd : (st.groups.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    findGroupByMeta st g.metaPtr = some g :=
  find?_metaPtr_of_mem hnd hg

/-- True iff `g` directly contains at least one `.liveUser` or `.claimed` slot. -/
def GroupDesc.hasDirectLeaf (g : GroupDesc) : Bool :=
  g.slots.any fun s =>
    match s with
    | .liveUser _ _ _ | .claimed => true
    | _ => false

/-- Step from a group's `metaPtr` to its `parentMeta` (fixed point on root groups `parentMeta = none`). -/
def parentMetaStep (st : MallocngSt) (m : BitVec 64) : BitVec 64 :=
  match findGroupByMeta st m with
  | some g => g.parentMeta.getD m
  | none => m

/-- Iterate `parentMetaStep` `k` times. -/
def iterParentMeta (st : MallocngSt) : Nat → BitVec 64 → BitVec 64
  | 0, m => m
  | k + 1, m => iterParentMeta st k (parentMetaStep st m)

theorem iterParentMeta_fixed {st : MallocngSt} {m : BitVec 64}
    (hFix : parentMetaStep st m = m) (k : Nat) :
    iterParentMeta st k m = m := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterParentMeta, hFix, ih]

theorem iterParentMeta_add (st : MallocngSt) (a b : Nat) (m : BitVec 64) :
    iterParentMeta st (a + b) m = iterParentMeta st b (iterParentMeta st a m) := by
  induction a generalizing m with
  | zero => simp [iterParentMeta]
  | succ a ih => simp [Nat.succ_add, iterParentMeta, ih]

private theorem nested_group_sizeClass_step {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {cg : GroupDesc} (hcg : cg ∈ st.groups) (hMap0 : cg.maplen = 0) :
    cg.isEmpty = false ∧ cg.sc < 48 ∧ sizeClass cg.sc ≤ 72 ∧
    ∃ pg ∈ st.groups, cg.parentMeta = some pg.metaPtr ∧
      pg.sc ≤ 24 ∧ 2 * sizeClass cg.sc + 1 ≤ sizeClass pg.sc := by
  have hEmptyFalse : cg.isEmpty = false := by
    cases hE : cg.isEmpty
    · rfl
    · have hPos := (hwf.empty_groups_bound cg hcg hE).1
      omega
  have hGWf := hwf.groups_wf cg hcg
  have ⟨hLastGe1, pg, hpg, _, _, hPar, hPgSc48, hCgLtPg, hPgLe24, _, _, _, hCapEq⟩ :=
    hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
  have hCgSc48 : cg.sc < 48 := Nat.lt_trans hCgLtPg hPgSc48
  have hFit : 12 + cg.cnt * cg.stride ≤ cg.totalBytes := hGWf.2.2.2.2.2.2.2.1
  have hStride : cg.stride = 16 * sizeClass cg.sc := by
    simp [GroupDesc.stride, hMap0, slotStride]
  have hTot : cg.totalBytes = 16 * sizeClass pg.sc - 4 := by
    simp [GroupDesc.totalBytes, hMap0, hCapEq, slotStride]
  have hPgLe146 : sizeClass pg.sc ≤ 146 := by
    by_cases hEq24 : pg.sc = 24
    · rw [hEq24]; decide
    · have hLt24 : pg.sc < 24 := by omega
      have hMono := sizeClass_strictMono hLt24 (by decide)
      have h24 : sizeClass 24 = 146 := by decide
      omega
  have hCntGe2 : 2 ≤ cg.cnt := by unfold GroupDesc.cnt; omega
  have hMulGe : 2 * (16 * sizeClass cg.sc) ≤ cg.cnt * cg.stride := by
    rw [hStride]
    exact Nat.mul_le_mul_right _ hCntGe2
  have hStep : 2 * sizeClass cg.sc + 1 ≤ sizeClass pg.sc := by omega
  exact ⟨hEmptyFalse, hCgSc48, by omega, pg, hpg, hPar, hPgLe24, hStep⟩

private theorem descend_nested_aux {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ (fuel : Nat) {g : GroupDesc}, g ∈ st.groups → g.maplen = 0 → sizeClass g.sc < 2 ^ fuel →
      ∃ leaf ∈ st.groups, ∃ d : Nat,
        d < fuel ∧ leaf.hasDirectLeaf = true ∧ iterParentMeta st d leaf.metaPtr = g.metaPtr
  | 0, g, hg, hMap0, hBound => by
    have ⟨_, hSc48, _, _⟩ := nested_group_sizeClass_step hwf hg hMap0
    have hGe1 := (sizeClass_bounds hSc48).1
    simp at hBound; omega
  | fuel + 1, g, hg, hMap0, hBound => by
    by_cases hDir : g.hasDirectLeaf = true
    · exact ⟨g, hg, 0, Nat.zero_lt_succ fuel, hDir, rfl⟩
    · have ⟨hNotEmpty, hSc48, _, _⟩ := nested_group_sizeClass_step hwf hg hMap0
      have hExNested : ∃ idx : Nat, ∃ hIdx : idx < g.slots.length, ∃ cm : BitVec 64,
          g.slots[idx]'hIdx = .liveNested cm := by
        obtain ⟨s, hsMem, hsNotFree⟩ := exists_of_all_eq_false hNotEmpty
        obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
        cases hS : s with
        | freeAvail | freeInactive => simp [hS, SlotState.isFree] at hsNotFree
        | claimed | liveUser _ _ _ =>
          have hD : g.hasDirectLeaf = true := by
            unfold GroupDesc.hasDirectLeaf
            rw [List.any_eq_true]
            exact ⟨s, hsMem, by simp [hS]⟩
          exact False.elim (hDir hD)
        | liveNested cm => exact ⟨idx, hIdx, cm, hEqS.trans hS⟩
      obtain ⟨idx, hIdx, cm, hSlotEq⟩ := hExNested
      have hSWf := (hwf.groups_wf g hg).slot_wf idx hIdx
      rw [hSlotEq] at hSWf
      obtain ⟨_, cg, hcg, hCmEq, hCgPar, _⟩ := hSWf.2.2.2.2
      have hCgMap0 : cg.maplen = 0 := by
        have hIff := (hwf.groups_wf cg hcg).2.2.2.2.2.2.2.2.2.2.1
        by_cases hPos : 0 < cg.maplen
        · have hNone := hIff.mp hPos
          rw [hCgPar] at hNone; cases hNone
        · omega
      have ⟨_, _, _, pg, hpg, hPgPar, _, hStep⟩ := nested_group_sizeClass_step hwf hcg hCgMap0
      have hPgEqG : pg = g := by
        rw [hCgPar] at hPgPar
        exact mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg (Option.some.inj hPgPar).symm
      rw [hPgEqG] at hStep
      have hPow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by omega
      have hCgBound : sizeClass cg.sc < 2 ^ fuel := by omega
      obtain ⟨leaf, hleaf, d, hdLt, hLeafDir, hIter⟩ :=
        descend_nested_aux hwf fuel hcg hCgMap0 hCgBound
      have hStepParent : parentMetaStep st cg.metaPtr = g.metaPtr := by
        simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hcg, hCgPar]
      refine ⟨leaf, hleaf, d + 1, Nat.succ_lt_succ hdLt, hLeafDir, ?_⟩
      rw [iterParentMeta_add st d 1 leaf.metaPtr, hIter]
      simp [iterParentMeta, hStepParent]

/-- Every non-empty group `g ∈ st.groups` (`g.isEmpty = false`) has a `hasDirectLeaf = true`
    descendant `leaf ∈ st.groups` within `d < 8` `parentMetaStep` hops (`d = 0` when `g` itself
    has a direct `.liveUser` or `.claimed` slot, and `d = 0` whenever `25 ≤ g.sc`). -/
theorem descend_nonempty_group {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hNotEmpty : g.isEmpty = false) :
    ∃ leaf ∈ st.groups, ∃ d : Nat,
      d < 8 ∧ leaf.hasDirectLeaf = true ∧
      iterParentMeta st d leaf.metaPtr = g.metaPtr ∧
      (25 ≤ g.sc → d = 0 ∧ leaf = g) := by
  by_cases hDir : g.hasDirectLeaf = true
  · exact ⟨g, hg, 0, by decide, hDir, rfl, fun _ => ⟨rfl, rfl⟩⟩
  · obtain ⟨s, hsMem, hsNotFree⟩ := exists_of_all_eq_false hNotEmpty
    obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
    cases hS : s with
    | freeAvail | freeInactive => simp [hS, SlotState.isFree] at hsNotFree
    | claimed | liveUser _ _ _ =>
      have hD : g.hasDirectLeaf = true := by
        unfold GroupDesc.hasDirectLeaf; rw [List.any_eq_true]; exact ⟨s, hsMem, by simp [hS]⟩
      exact False.elim (hDir hD)
    | liveNested cm =>
      have hSlotEq : g.slots[idx]'hIdx = .liveNested cm := hEqS.trans hS
      have hSWf := (hwf.groups_wf g hg).slot_wf idx hIdx
      rw [hSlotEq] at hSWf
      obtain ⟨_, cg, hcg, _, hCgPar, _⟩ := hSWf.2.2.2.2
      have hCgMap0 : cg.maplen = 0 := by
        have hIff := (hwf.groups_wf cg hcg).2.2.2.2.2.2.2.2.2.2.1
        by_cases hPos : 0 < cg.maplen
        · have hNone := hIff.mp hPos; rw [hCgPar] at hNone; cases hNone
        · omega
      have ⟨_, _, hCgLe72, pg, hpg, hPgPar, hPgLe24, _⟩ := nested_group_sizeClass_step hwf hcg hCgMap0
      have hPgEqG : pg = g := by
        rw [hCgPar] at hPgPar
        exact mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg (Option.some.inj hPgPar).symm
      subst hPgEqG
      obtain ⟨leaf, hleaf, d, hdLt7, hLeafDir, hIter⟩ :=
        descend_nested_aux hwf 7 hcg hCgMap0 (by omega)
      have hStepParent : parentMetaStep st cg.metaPtr = pg.metaPtr := by
        simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hcg, hCgPar]
      refine ⟨leaf, hleaf, d + 1, by omega, hLeafDir, ?_, fun hGe25 => by omega⟩
      rw [iterParentMeta_add st d 1 leaf.metaPtr, hIter]
      simp [iterParentMeta, hStepParent]

/-! ## Global Group-Count and `meta_area` Page-Count Bounds -/

theorem empGs_sc_nodup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (gs : List GroupDesc)
    (hMetaNd : (gs.map (·.metaPtr)).Nodup)
    (hAllEmp : ∀ g ∈ gs, g ∈ st.groups ∧ g.isEmpty = true) :
    (gs.map (·.sc)).Nodup := by
  induction gs with
  | nil => exact List.nodup_nil
  | cons g rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hMetaNd ⊢
    refine ⟨?_, ih hMetaNd.2 (fun x hx => hAllEmp x (List.mem_cons_of_mem g hx))⟩
    intro hMemSc
    obtain ⟨g', hg'Rest, hScEq⟩ := List.mem_map.mp hMemSc
    have ⟨hgMem, hgE⟩ := hAllEmp g List.mem_cons_self
    have ⟨hg'Mem, hg'E⟩ := hAllEmp g' (List.mem_cons_of_mem g hg'Rest)
    have hMetaEq := (hwf.empty_groups_bound g hgMem hgE).2.2.2.2.2.1 g' hg'Mem hg'E hScEq
    exact hMetaNd.1 (hMetaEq.symm ▸ List.mem_map_of_mem hg'Rest)

theorem empGs_range_length_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (gs : List GroupDesc) (lo k : Nat)
    (hMetaNd : (gs.map (·.metaPtr)).Nodup)
    (hAllEmp : ∀ g ∈ gs, g ∈ st.groups ∧ g.isEmpty = true)
    (hRange : ∀ g ∈ gs, lo ≤ g.sc ∧ g.sc < lo + k) :
    gs.length ≤ k := by
  have hScNd := empGs_sc_nodup hwf gs hMetaNd hAllEmp
  have hSub : ∀ sc ∈ gs.map (·.sc), sc ∈ (List.range k).map (· + lo) := by
    intro sc hsc
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hsc
    have ⟨hGe, hLt⟩ := hRange g hg
    exact List.mem_map.mpr ⟨g.sc - lo, List.mem_range.mpr (by omega), by omega⟩
  have hLen := nodup_length_le_of_subset hScNd hSub
  simp only [List.length_map, List.length_range] at hLen
  exact hLen

/-- At most `32` empty groups exist in `st.groups` (`7 ≤ g.sc ≤ 38`, unique per `sc`). -/
theorem emptyGroups_length_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    (st.groups.filter (·.isEmpty)).length ≤ 32 := by
  let empGs := st.groups.filter (·.isEmpty)
  have hMetaNd : (empGs.map (·.metaPtr)).Nodup :=
    ((List.filter_sublist).map _).nodup hwf.groups_nodup.1
  exact empGs_range_length_le hwf empGs 7 32 hMetaNd (fun g hg => List.mem_filter.mp hg)
    (fun g hg => by
      have ⟨hgIn, hE⟩ := List.mem_filter.mp hg
      have ⟨_, hGe7, hLe38, _⟩ := hwf.empty_groups_bound g hgIn hE
      omega)

private theorem directLeaf_weight_ge_16 {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hDir : g.hasDirectLeaf = true) :
    65536 ≤ (g.slots.map slotEffCost).sum + 65536 * (g.slots.filter SlotState.isClaimed).length := by
  unfold GroupDesc.hasDirectLeaf at hDir
  obtain ⟨s, hsMem, hsDir⟩ := List.any_eq_true.mp hDir
  obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
  cases hS : s with
  | freeAvail | freeInactive | liveNested _ => simp [hS] at hsDir
  | claimed =>
    have hMemF : s ∈ g.slots.filter SlotState.isClaimed :=
      List.mem_filter.mpr ⟨hsMem, by simp [hS, SlotState.isClaimed]⟩
    have hLenPos : 1 ≤ (g.slots.filter SlotState.isClaimed).length :=
      List.length_pos_of_mem hMemF
    omega
  | liveUser userPtr reqSize effCost =>
    have hSlotEq : g.slots[idx]'hIdx = .liveUser userPtr reqSize effCost := hEqS.trans hS
    have hSWf := (hwf.groups_wf g hg).slot_wf idx hIdx
    rw [hSlotEq] at hSWf
    have hGe16 : 65536 ≤ effCost := by
      have hMax := hSWf.2.2.2.2.2.2.2.1
      unfold MallocngMinBlockCost at hMax
      omega
    have hMemCost : effCost ∈ g.slots.map slotEffCost := by
      rw [hS] at hsMem
      exact List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩
    have hGeSum : effCost ≤ (g.slots.map slotEffCost).sum := accounting_le_sum_of_mem hMemCost
    omega

/-- Total active groups in `st.groups` is bounded by `32 + 8 * (liveCost / 65536 + totalClaimedSlots st)`. -/
theorem groups_length_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    st.groups.length ≤ 32 + 8 * (liveCost / 65536 + totalClaimedSlots st) := by
  let empGs := st.groups.filter (·.isEmpty)
  let nonEmpGs := st.groups.filter (fun g => !g.isEmpty)
  have hPartLen : st.groups.length = empGs.length + nonEmpGs.length :=
    accounting_length_filter_partition (·.isEmpty) st.groups
  have hEmpLe : empGs.length ≤ 32 := emptyGroups_length_le hwf
  let directLeaves := st.groups.filter (·.hasDirectLeaf)
  have hDirWeight :
      65536 * directLeaves.length ≤ totalLiveEffCost st + 65536 * totalClaimedSlots st := by
    let w : GroupDesc → Nat := fun g =>
      (g.slots.map slotEffCost).sum + 65536 * (g.slots.filter SlotState.isClaimed).length
    have hGe16 : (directLeaves.map fun _ => 65536).sum ≤ (directLeaves.map w).sum :=
      accounting_sum_map_le fun g hg =>
        directLeaf_weight_ge_16 hwf (List.mem_filter.mp hg).1 (List.mem_filter.mp hg).2
    have hConst16 : (directLeaves.map fun _ => 65536).sum = 65536 * directLeaves.length := by
      clear hGe16
      induction directLeaves with
      | nil => rfl
      | cons _ rest ih => simp [ih]; omega
    have hSubSum : (directLeaves.map w).sum ≤ (st.groups.map w).sum := by
      have hPart := accounting_sum_filter_partition (·.hasDirectLeaf) w st.groups
      dsimp only [directLeaves]
      omega
    have hTotalW : (st.groups.map w).sum = totalLiveEffCost st + 65536 * totalClaimedSlots st := by
      rw [sum_map_add]
      congr 1
      unfold totalClaimedSlots
      clear empGs nonEmpGs directLeaves hPartLen hEmpLe hGe16 hConst16 hSubSum
      induction st.groups with
      | nil => rfl
      | cons g gs ih => simp [ih]; omega
    omega
  have hEffLe : totalLiveEffCost st ≤ liveCost := hwf.effCost_le_live
  have hDirLe : directLeaves.length ≤ liveCost / 65536 + totalClaimedSlots st := by omega
  let ancestors := directLeaves.flatMap fun leaf =>
    (List.range 8).map fun d => iterParentMeta st d leaf.metaPtr
  have hAncLen : ancestors.length = 8 * directLeaves.length := by
    dsimp only [ancestors]
    clear hDirLe hDirWeight
    induction directLeaves with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
        List.length_cons]
      omega
  have hNonEmpMetaNd : (nonEmpGs.map (·.metaPtr)).Nodup :=
    ((List.filter_sublist).map _).nodup hwf.groups_nodup.1
  have hNonEmpSub : ∀ m ∈ nonEmpGs.map (·.metaPtr), m ∈ ancestors := by
    intro m hm
    obtain ⟨g, hgMem, rfl⟩ := List.mem_map.mp hm
    have ⟨hgIn, hgNotE⟩ := List.mem_filter.mp hgMem
    have hEFalse : g.isEmpty = false := by simpa using hgNotE
    obtain ⟨leaf, hleaf, d, hdLt8, hLeafDir, hIter, _⟩ := descend_nonempty_group hwf hgIn hEFalse
    refine List.mem_flatMap.mpr ⟨leaf, List.mem_filter.mpr ⟨hleaf, hLeafDir⟩, ?_⟩
    exact List.mem_map.mpr ⟨d, List.mem_range.mpr hdLt8, hIter⟩
  have hNonEmpLe : nonEmpGs.length ≤ ancestors.length := by
    have h := nodup_length_le_of_subset hNonEmpMetaNd hNonEmpSub
    simpa using h
  omega

private theorem nodup_map_of_inj_on {α β : Type} {f : α → β} {xs : List α}
    (hnd : xs.Nodup) (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [List.nodup_cons, List.map_cons] at hnd ⊢
    refine ⟨?_, ih hnd.2 (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    intro hMem
    obtain ⟨y, hyRest, hfy⟩ := List.mem_map.mp hMem
    have hxy := hinj y (List.mem_cons_of_mem x hyRest) x List.mem_cons_self hfy
    exact hnd.1 (hxy ▸ hyRest)

private theorem slotAddr_toNat_eq (ma : MetaAreaDesc) (k : Nat)
    (hBound : ma.base.toNat + 4096 ≤ 2 ^ 48) (hk : k < 101) :
    (ma.slotAddr k).toNat = ma.base.toNat + (24 + 40 * k) := by
  have h24 : 24 + 40 * k < 2 ^ 64 := by omega
  have hSum : ma.base.toNat + (24 + 40 * k) < 2 ^ 64 := by omega
  simp only [MetaAreaDesc.slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h24, Nat.mod_eq_of_lt hSum]

private theorem metaAreaSlots_nodup_gen (n : Nat) (hn : n ≤ 101) (mas : List MetaAreaDesc)
    (hMaNd : (mas.map (·.base)).Nodup)
    (hMaBounds : ∀ ma ∈ mas, 4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧
      ma.base.toNat + 4096 ≤ 2 ^ 48) :
    (mas.flatMap fun ma => (List.range n).map ma.slotAddr).Nodup := by
  induction mas with
  | nil => exact List.nodup_nil
  | cons ma rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hMaNd
    simp only [List.flatMap_cons]
    have hMaB := hMaBounds ma List.mem_cons_self
    have hRestB : ∀ m' ∈ rest, 4096 ≤ m'.base.toNat ∧ m'.base.toNat % 4096 = 0 ∧
        m'.base.toNat + 4096 ≤ 2 ^ 48 :=
      fun m' hm' => hMaBounds m' (List.mem_cons_of_mem ma hm')
    have hHeadNd : ((List.range n).map ma.slotAddr).Nodup := by
      refine nodup_map_of_inj_on (xs := List.range n) List.nodup_range ?_
      intro k1 hk1 k2 hk2 hEq
      have hk1Lt : k1 < 101 := Nat.lt_of_lt_of_le (List.mem_range.mp hk1) hn
      have hk2Lt : k2 < 101 := Nat.lt_of_lt_of_le (List.mem_range.mp hk2) hn
      have hToNat := congrArg BitVec.toNat hEq
      rw [slotAddr_toNat_eq ma k1 hMaB.2.2 hk1Lt, slotAddr_toNat_eq ma k2 hMaB.2.2 hk2Lt] at hToNat
      omega
    have hTailNd := ih hMaNd.2 hRestB
    refine (List.nodup_append (l₁ := (List.range n).map ma.slotAddr)
      (l₂ := rest.flatMap fun ma => (List.range n).map ma.slotAddr)).mpr
      ⟨hHeadNd, hTailNd, fun a ha1 b hb2 hAb => ?_⟩
    subst hAb
    obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp ha1
    obtain ⟨ma2, hma2, ha2'⟩ := List.mem_flatMap.mp hb2
    obtain ⟨k2, hk2, hEq⟩ := List.mem_map.mp ha2'
    have hk1Lt : k1 < 101 := Nat.lt_of_lt_of_le (List.mem_range.mp hk1) hn
    have hk2Lt : k2 < 101 := Nat.lt_of_lt_of_le (List.mem_range.mp hk2) hn
    have hMa2B := hRestB ma2 hma2
    have hToNat := congrArg BitVec.toNat hEq
    rw [slotAddr_toNat_eq ma k1 hMaB.2.2 hk1Lt, slotAddr_toNat_eq ma2 k2 hMa2B.2.2 hk2Lt] at hToNat
    have hBaseNatEq : ma.base.toNat = ma2.base.toNat := by omega
    exact hMaNd.1 ((BitVec.eq_of_toNat_eq hBaseNatEq) ▸ List.mem_map_of_mem hma2)

private theorem metaAreaSlots_nodup (mas : List MetaAreaDesc)
    (hMaNd : (mas.map (·.base)).Nodup)
    (hMaBounds : ∀ ma ∈ mas, 4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧
      ma.base.toNat + 4096 ≤ 2 ^ 48) :
    (mas.flatMap fun ma => (List.range 101).map ma.slotAddr).Nodup :=
  metaAreaSlots_nodup_gen 101 (Nat.le_refl 101) mas hMaNd hMaBounds

/-- When `freeMetas = []` and `bumpMetas = []` at recursion depth `inflight ≤ 7`, activating one new
    `meta_area` page maintains `metaAreas.length + 1 ≤ 2 + peakCost / 655360`. -/
theorem metaAreas_length_succ_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7)
    (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) :
    st.metaAreas.length + 1 ≤ 2 + peakCost / 655360 := by
  let usedAndFree :=
    st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
  have ⟨hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hAllSlotsLen : (allMetaSlots st).length = 101 * st.metaAreas.length := by
    unfold allMetaSlots
    induction st.metaAreas with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
        List.length_cons]
      omega
  have hSlotNd : (allMetaSlots st).Nodup :=
    metaAreaSlots_nodup st.metaAreas hwf.metaAreas_wf.1
      (fun ma hma => ⟨(hwf.metaAreas_wf.2.1 ma hma).1, (hwf.metaAreas_wf.2.1 ma hma).2.1,
        (hwf.metaAreas_wf.2.1 ma hma).2.2.1⟩)
  have hSlotsLeUf : (allMetaSlots st).length ≤ usedAndFree.length :=
    nodup_length_le_of_subset hSlotNd (fun m hm => (hUfIff m).mpr hm)
  have hGsLe := groups_length_le hwf
  have hInflightBound := hwf.inflight_wf
  have hLiveLePeak := hwf.live_le_peak
  have hUfLen : usedAndFree.length = st.groups.length + st.reservedMetas.length := by
    simp [usedAndFree, hNoFree, hNoBump]
  omega

end VerifiedLibraries.Mallocng.Proofs
