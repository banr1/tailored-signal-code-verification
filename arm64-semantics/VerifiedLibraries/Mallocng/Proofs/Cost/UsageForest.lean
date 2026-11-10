/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.AccountingHelpers

/-!
# Nesting-Forest Descendant Weights

Defines slot and group occupancy weights, the reflexive descendant relation `IsDescOf` on the
`parentMeta` forest, its leaf weight `descW`, and descendant-set disjointness for distinct
same-class groups and sibling child metas.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Slot and group weights -/

/-- `1` iff `s` is not free (`.claimed`, `.liveNested`, or `.liveUser`). -/
def slotNonFree : SlotState → Nat
  | .freeAvail | .freeInactive => 0
  | _ => 1

/-- `1` iff `s` is a leaf (`.claimed` or `.liveUser`). -/
def slotLeaf : SlotState → Nat
  | .claimed | .liveUser _ _ _ => 1
  | _ => 0

/-- Child `struct meta *` of a `.liveNested` slot. -/
def slotChild : SlotState → Option (BitVec 64)
  | .liveNested cm => some cm
  | _ => none

/-- Number of non-free slots of `g`. -/
def groupNonFree (g : GroupDesc) : Nat := (g.slots.map slotNonFree).sum

/-- Number of leaf slots of `g`. -/
def groupLeaf (g : GroupDesc) : Nat := (g.slots.map slotLeaf).sum

/-- Child metas of `g` (one per `.liveNested` slot, in slot order). -/
def childMetas (g : GroupDesc) : List (BitVec 64) := g.slots.filterMap slotChild

/-- Number of non-free slots (`.claimed` / `.liveNested` / `.liveUser`) over all groups of class `sc`. -/
def nonFreeSlots (st : MallocngSt) (sc : Nat) : Nat :=
  ((st.groups.filter (·.sc == sc)).map groupNonFree).sum

/-- `x` is a (reflexive) descendant of `m` in the nesting forest. -/
def IsDescOf (st : MallocngSt) (m : BitVec 64) (x : GroupDesc) : Prop :=
  ∃ k, iterParentMeta st k x.metaPtr = m

/-- Boolean form of `IsDescOf` (classical). -/
noncomputable def descB (st : MallocngSt) (m : BitVec 64) (x : GroupDesc) : Bool :=
  @decide (IsDescOf st m x) (Classical.propDecidable _)

theorem descB_iff {st : MallocngSt} {m : BitVec 64} {x : GroupDesc} :
    descB st m x = true ↔ IsDescOf st m x := by
  unfold descB; exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- Total leaf weight of all descendants of `m`. -/
noncomputable def descW (st : MallocngSt) (m : BitVec 64) : Nat :=
  ((st.groups.filter (descB st m)).map groupLeaf).sum

/-! ## List and slot-weight lemmas -/

private theorem sum_map_add' {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem length_le_one_of_nodup_eq {β : Type} {zs : List β} (hnd : zs.Nodup)
    (heq : ∀ a ∈ zs, ∀ b ∈ zs, a = b) : zs.length ≤ 1 := by
  match zs, hnd, heq with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: rest, hnd, heq =>
    exfalso
    have hab := heq a List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self)
    exact (List.nodup_cons.mp hnd).1 (hab ▸ List.mem_cons_self)

/-- Fiber sums over a duplicate-free index list with pairwise-disjoint fibers, all inside `Q`. -/
theorem sum_fibers_le {α β : Type} (P : β → α → Bool) (Q : α → Bool) (w : α → Nat)
    (xs : List α) {ys : List β} (hnd : ys.Nodup)
    (hdisj : ∀ y₁ ∈ ys, ∀ y₂ ∈ ys, ∀ x, P y₁ x = true → P y₂ x = true → y₁ = y₂)
    (hsub : ∀ y ∈ ys, ∀ x, P y x = true → Q x = true) :
    (ys.map fun y => ((xs.filter (P y)).map w).sum).sum ≤ ((xs.filter Q).map w).sum := by
  induction xs with
  | nil =>
    clear hdisj hsub hnd
    induction ys with
    | nil => simp
    | cons _ _ ih => simpa using ih
  | cons x rest ih =>
    have hSplit : (ys.map fun y => (((x :: rest).filter (P y)).map w).sum) =
        (ys.map fun y => (if P y x then w x else 0) + ((rest.filter (P y)).map w).sum) := by
      refine List.map_congr_left fun y _ => ?_
      by_cases h : P y x = true
      · simp [h]
      · simp [h]
    rw [hSplit, sum_map_add']
    have hHead : (ys.map fun y => if P y x then w x else 0).sum =
        (ys.filter fun y => P y x).length * w x := by
      clear hSplit ih hdisj hsub hnd
      induction ys with
      | nil => simp
      | cons y ys ihy =>
        by_cases h : P y x = true
        · simp [h, ihy, Nat.succ_mul]; omega
        · simp [h, ihy]
    have hLen : (ys.filter fun y => P y x).length ≤ 1 :=
      length_le_one_of_nodup_eq (hnd.filter _) (fun a ha b hb => by
        have ⟨ha1, ha2⟩ := List.mem_filter.mp ha
        have ⟨hb1, hb2⟩ := List.mem_filter.mp hb
        exact hdisj a ha1 b hb1 x ha2 hb2)
    rw [hHead]
    by_cases hQ : Q x = true
    · simp only [List.filter_cons, hQ, ↓reduceIte, List.map_cons, List.sum_cons]
      have : (ys.filter fun y => P y x).length * w x ≤ w x := by
        calc _ ≤ 1 * w x := Nat.mul_le_mul_right _ hLen
          _ = w x := Nat.one_mul _
      omega
    · have hZero : (ys.filter fun y => P y x).length = 0 := by
        rcases hL : (ys.filter fun y => P y x) with _ | ⟨y, _⟩
        · rfl
        · have hy : y ∈ ys.filter fun y => P y x := hL ▸ List.mem_cons_self
          have ⟨hy1, hy2⟩ := List.mem_filter.mp hy
          exact absurd (hsub y hy1 x hy2) hQ
      have hQf : Q x = false := Bool.eq_false_iff.mpr hQ
      simp only [List.filter_cons, hQf, Bool.false_eq_true, ↓reduceIte, hZero, Nat.zero_mul,
        Nat.zero_add]
      exact ih

/-- `filterMap` is duplicate-free when equal outputs only come from equal indices. -/
theorem nodup_filterMap_of_idx {α β : Type} (f : α → Option β) :
    ∀ (xs : List α),
      (∀ i j (hi : i < xs.length) (hj : j < xs.length) (b : β),
        f (xs[i]'hi) = some b → f (xs[j]'hj) = some b → i = j) →
      (xs.filterMap f).Nodup
  | [], _ => List.nodup_nil
  | x :: rest, hinj => by
    have hRest : (rest.filterMap f).Nodup :=
      nodup_filterMap_of_idx f rest (fun i j hi hj b h1 h2 => by
        have := hinj (i + 1) (j + 1) (by simp; omega) (by simp; omega) b
          (by simpa using h1) (by simpa using h2)
        omega)
    rcases hx : f x with _ | b
    · simp [hx, hRest]
    · simp only [List.filterMap_cons, hx]
      refine List.nodup_cons.mpr ⟨fun hMem => ?_, hRest⟩
      obtain ⟨a, haMem, haEq⟩ := List.mem_filterMap.mp hMem
      obtain ⟨j, hj, hjEq⟩ := List.getElem_of_mem haMem
      have := hinj 0 (j + 1) (by simp) (by simp; omega) b (by simpa using hx)
        (by simpa [hjEq] using haEq)
      omega

private theorem sum_groupLeaf (gs : List GroupDesc) :
    (gs.map groupLeaf).sum =
      (gs.map fun g => (g.slots.map slotLiveCount).sum).sum +
      (gs.map fun g => (g.slots.filter SlotState.isClaimed).length).sum := by
  have hG : ∀ g : GroupDesc, groupLeaf g =
      (g.slots.map slotLiveCount).sum + (g.slots.filter SlotState.isClaimed).length := by
    intro g
    unfold groupLeaf
    induction g.slots with
    | nil => rfl
    | cons s rest ih =>
      cases s <;> simp [slotLeaf, slotLiveCount, SlotState.isClaimed, List.filter_cons, ih] <;> omega
  rw [← sum_map_add']
  exact congrArg List.sum (List.map_congr_left fun g _ => hG g)

theorem sum_groupLeaf_eq (st : MallocngSt) :
    (st.groups.map groupLeaf).sum = totalLiveCount st + totalClaimedSlots st :=
  sum_groupLeaf st.groups

theorem groupNonFree_eq (g : GroupDesc) :
    groupNonFree g = groupLeaf g + (childMetas g).length := by
  unfold groupNonFree groupLeaf childMetas
  induction g.slots with
  | nil => rfl
  | cons s rest ih =>
    cases s <;> simp [slotNonFree, slotLeaf, slotChild, List.filterMap_cons, ih] <;> omega

/-! ## Nesting-forest ancestry -/

section Forest

variable {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}

private theorem parentStep_anc
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {a : GroupDesc} (ha : a ∈ st.groups) :
    ∃ p ∈ st.groups, parentMetaStep st a.metaPtr = p.metaPtr ∧ (p = a ∨ a.sc < p.sc) := by
  have hFind := findGroupByMeta_of_mem hwf.groups_nodup.1 ha
  rcases hPar : a.parentMeta with _ | pm
  · exact ⟨a, ha, by simp [parentMetaStep, hFind, hPar], Or.inl rfl⟩
  · have hGWf := hwf.groups_wf a ha
    have hMap0 : a.maplen = 0 := by
      by_cases hPos : 0 < a.maplen
      · have := hGWf.2.2.2.2.2.2.2.2.2.2.1.mp hPos; rw [hPar] at this; cases this
      · omega
    obtain ⟨_, pg, hpg, _, _, hPar', _, hLt, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
    rw [hPar] at hPar'
    refine ⟨pg, hpg, ?_, Or.inr hLt⟩
    simp [parentMetaStep, hFind, hPar, Option.some.inj hPar']

/-- Iterated ancestors of a group are the group itself or strictly larger-class groups. -/
theorem iter_anc
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ (j : Nat) {a : GroupDesc}, a ∈ st.groups →
      ∃ c ∈ st.groups, iterParentMeta st j a.metaPtr = c.metaPtr ∧ (c = a ∨ a.sc < c.sc)
  | 0, a, ha => ⟨a, ha, rfl, Or.inl rfl⟩
  | j + 1, a, ha => by
    obtain ⟨p, hp, hpEq, hpOr⟩ := parentStep_anc hwf ha
    obtain ⟨c, hc, hcEq, hcOr⟩ := iter_anc hwf j hp
    refine ⟨c, hc, ?_, ?_⟩
    · show iterParentMeta st j (parentMetaStep st a.metaPtr) = c.metaPtr
      rw [hpEq, hcEq]
    · rcases hpOr with rfl | hap
      · exact hcOr
      · rcases hcOr with rfl | hpc
        · exact Or.inr hap
        · exact Or.inr (Nat.lt_trans hap hpc)

/-- Two ancestors of the same group are comparable. -/
theorem desc_cmp {m₁ m₂ x : BitVec 64} {k₁ k₂ : Nat}
    (h₁ : iterParentMeta st k₁ x = m₁) (h₂ : iterParentMeta st k₂ x = m₂) :
    (∃ j, iterParentMeta st j m₁ = m₂) ∨ (∃ j, iterParentMeta st j m₂ = m₁) := by
  by_cases hle : k₁ ≤ k₂
  · refine Or.inl ⟨k₂ - k₁, ?_⟩
    rw [← h₁, ← iterParentMeta_add, Nat.add_sub_cancel' hle, h₂]
  · refine Or.inr ⟨k₁ - k₂, ?_⟩
    rw [← h₂, ← iterParentMeta_add, Nat.add_sub_cancel' (by omega), h₁]

/-- Distinct groups of the same class have disjoint descendant sets. -/
theorem same_sc_desc_eq
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {a b : GroupDesc} (ha : a ∈ st.groups) (hb : b ∈ st.groups) (hsc : a.sc = b.sc)
    {x : GroupDesc} (hxa : IsDescOf st a.metaPtr x) (hxb : IsDescOf st b.metaPtr x) :
    a.metaPtr = b.metaPtr := by
  obtain ⟨k₁, h₁⟩ := hxa
  obtain ⟨k₂, h₂⟩ := hxb
  rcases desc_cmp h₁ h₂ with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨c, hc, hcEq, hcOr⟩ := iter_anc hwf j ha
    have hcb : c = b := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc hb (hcEq.symm.trans hj)
    subst hcb
    rcases hcOr with rfl | hlt
    · rfl
    · omega
  · obtain ⟨c, hc, hcEq, hcOr⟩ := iter_anc hwf j hb
    have hca : c = a := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc ha (hcEq.symm.trans hj)
    subst hca
    rcases hcOr with rfl | hlt
    · rfl
    · omega

/-- Facts about a child meta of `g`: the child group exists, is nested in `g`, has smaller class,
    and is non-empty. -/
theorem child_info
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {cm : BitVec 64} (hcm : cm ∈ childMetas g) :
    ∃ cg ∈ st.groups, cg.metaPtr = cm ∧ cg.parentMeta = some g.metaPtr ∧ cg.sc < g.sc ∧
      cg.isEmpty = false := by
  obtain ⟨s, hsMem, hsEq⟩ := List.mem_filterMap.mp hcm
  obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
  have hSWf := (hwf.groups_wf g hg).slot_wf idx hIdx
  rw [hEqS] at hSWf
  cases s with
  | liveNested c =>
    simp only [slotChild, Option.some.injEq] at hsEq
    subst hsEq
    obtain ⟨_, cg, hcg, hcgM, hcgPar, _⟩ := hSWf.2.2.2.2
    have hGWf := hwf.groups_wf cg hcg
    have hMap0 : cg.maplen = 0 := by
      by_cases hPos : 0 < cg.maplen
      · have := hGWf.2.2.2.2.2.2.2.2.2.2.1.mp hPos; rw [hcgPar] at this; cases this
      · omega
    obtain ⟨_, pg, hpg, _, _, hPar', _, hLt, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
    rw [hcgPar] at hPar'
    have hpgEq : pg = g :=
      mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg (Option.some.inj hPar').symm
    subst hpgEq
    have hNE : cg.isEmpty = false := by
      cases hE : cg.isEmpty
      · rfl
      · have := (hwf.empty_groups_bound cg hcg hE).1; omega
    exact ⟨cg, hcg, hcgM, hcgPar, hLt, hNE⟩
  | _ => simp [slotChild] at hsEq

private theorem tag_inj {i j : Nat} (hi : i < 32) (hj : j < 32)
    (h : BitVec.ofNat 8 ((6 <<< 5) ||| i) = BitVec.ofNat 8 ((6 <<< 5) ||| j)) : i = j := by
  have key : ∀ i, i < 32 → (BitVec.ofNat 8 ((6 <<< 5) ||| i)).toNat % 32 = i := by decide
  have := congrArg (fun v : BitVec 8 => v.toNat % 32) h
  rw [key i hi, key j hj] at this
  exact this

/-- Child metas of `g` are pairwise distinct (each child header stores its parent slot index). -/
theorem childMetas_nodup
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) : (childMetas g).Nodup := by
  have hGWf := hwf.groups_wf g hg
  have key : ∀ k (hk : k < g.slots.length) (b : BitVec 64), slotChild (g.slots[k]'hk) = some b →
      ∃ cg ∈ st.groups, cg.metaPtr = b ∧
        st.byteVal (cg.mem - 3#64) = BitVec.ofNat 8 ((6 <<< 5) ||| k) := by
    intro k hk b hb
    have hSWf := hGWf.slot_wf k hk
    revert hSWf hb
    cases g.slots[k]'hk with
    | liveNested c =>
      intro hb hSWf
      simp only [slotChild, Option.some.injEq] at hb
      subst hb
      obtain ⟨_, cg, hcg, hcgM, _, _, _, _, _, _, _, hb3, _⟩ := hSWf.2.2.2.2
      exact ⟨cg, hcg, hcgM, hb3⟩
    | _ => intro hb; simp [slotChild] at hb
  apply nodup_filterMap_of_idx
  intro i j hi hj b h1 h2
  obtain ⟨c1, hc1, hc1M, hb1⟩ := key i hi b h1
  obtain ⟨c2, hc2, hc2M, hb2⟩ := key j hj b h2
  have hc : c1 = c2 := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc1 hc2 (hc1M.trans hc2M.symm)
  subst hc
  have hLen : g.slots.length ≤ 32 := by
    have h1 : g.slots.length = g.cnt := hGWf.2.2.1
    have h2 : g.lastIdx ≤ 31 := hGWf.2.1
    simp only [GroupDesc.cnt] at h1; omega
  exact tag_inj (by omega) (by omega) (hb1.symm.trans hb2)

/-- Distinct children of `g` have disjoint descendant sets. -/
theorem child_desc_eq
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {cm₁ cm₂ : BitVec 64}
    (h₁ : cm₁ ∈ childMetas g) (h₂ : cm₂ ∈ childMetas g)
    {x : GroupDesc} (hx₁ : IsDescOf st cm₁ x) (hx₂ : IsDescOf st cm₂ x) : cm₁ = cm₂ := by
  obtain ⟨cg₁, hcg₁, hM₁, hP₁, hLt₁, _⟩ := child_info hwf hg h₁
  obtain ⟨cg₂, hcg₂, hM₂, hP₂, hLt₂, _⟩ := child_info hwf hg h₂
  have hStep : ∀ {cg : GroupDesc}, cg ∈ st.groups → cg.parentMeta = some g.metaPtr →
      parentMetaStep st cg.metaPtr = g.metaPtr := fun hcg hP => by
    simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hcg, hP]
  have hReach : ∀ {cgA cgB : GroupDesc}, cgA ∈ st.groups → cgB ∈ st.groups →
      cgA.parentMeta = some g.metaPtr → cgB.sc < g.sc →
      ∀ j, iterParentMeta st j cgA.metaPtr = cgB.metaPtr → cgA.metaPtr = cgB.metaPtr := by
    intro cgA cgB hA hB hPA hLtB j hj
    cases j with
    | zero => exact hj
    | succ j =>
      exfalso
      have hj' : iterParentMeta st j g.metaPtr = cgB.metaPtr := by
        have : iterParentMeta st (j + 1) cgA.metaPtr =
            iterParentMeta st j (parentMetaStep st cgA.metaPtr) := rfl
        rw [this, hStep hA hPA] at hj; exact hj
      obtain ⟨c, hc, hcEq, hcOr⟩ := iter_anc hwf j hg
      have hcB : c = cgB := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc hB (hcEq.symm.trans hj')
      subst hcB
      rcases hcOr with rfl | hlt <;> omega
  obtain ⟨k₁, hk₁⟩ := hx₁
  obtain ⟨k₂, hk₂⟩ := hx₂
  subst hM₁ hM₂
  rcases desc_cmp hk₁ hk₂ with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact hReach hcg₁ hcg₂ hP₁ hLt₂ j hj
  · exact (hReach hcg₂ hcg₁ hP₂ hLt₁ j hj).symm

/-- Descendants of a child of `g` are descendants of `g`, and differ from `g`. -/
theorem child_desc_sub
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {cm : BitVec 64} (hcm : cm ∈ childMetas g)
    {x : GroupDesc} (hx : IsDescOf st cm x) :
    IsDescOf st g.metaPtr x ∧ x.metaPtr ≠ g.metaPtr := by
  obtain ⟨cg, hcg, hM, hP, hLt, _⟩ := child_info hwf hg hcm
  obtain ⟨k, hk⟩ := hx
  have hStep : parentMetaStep st cg.metaPtr = g.metaPtr := by
    simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hcg, hP]
  have hDesc : iterParentMeta st (k + 1) x.metaPtr = g.metaPtr := by
    rw [iterParentMeta_add, hk, ← hM]; simp [iterParentMeta, hStep]
  refine ⟨⟨k + 1, hDesc⟩, fun hxg => ?_⟩
  rw [hxg, ← hM] at hk
  obtain ⟨c, hc, hcEq, hcOr⟩ := iter_anc hwf k hg
  have hcc : c = cg := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc hcg (hcEq.symm.trans hk)
  subst hcc
  rcases hcOr with rfl | hlt <;> omega

end Forest

end VerifiedLibraries.Mallocng.Proofs.Cost
