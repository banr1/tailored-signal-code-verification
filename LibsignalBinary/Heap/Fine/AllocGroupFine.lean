/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.List.Forall2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotHelpers2
public import LibsignalBinary.Heap.Fine.Footprint

/-!
# Fine-Grained `alloc_group` and `alloc_slot` Invariant Preservation

Preservation of `MallocngFineInv` and per-class occupancy bounds across `alloc_slot` and
`alloc_group` transitions (`pop`, `rootGroup`, and `nestedGroup`), using ring-empty occupancy bounds
(`active_zero_occ_bounds`) and size-class DAG monotonicity (`sc < pSc`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine

open Arm64
open VerifiedLibraries.Mallocng
open VerifiedLibraries.Mallocng.Proofs

/-! ## Group Geometry Equivalence -/

/-- Exact equality of group geometry fields across intra-`alloc_slot` metadata transitions. -/
def FineGroupSameGeom (g' g : GroupDesc) : Prop :=
  g'.metaPtr = g.metaPtr ∧ g'.sc = g.sc ∧ g'.maplen = g.maplen ∧
  g'.nestedCap = g.nestedCap ∧ g'.lastIdx = g.lastIdx

/-- Group-list equivalence preserving `FineGroupSameGeom` and per-slot `SlotSameKind`. -/
def FineSameGroupsSlotKind (gs' gs : List GroupDesc) : Prop :=
  List.Forall₂ (fun g' g => FineGroupSameGeom g' g ∧ List.Forall₂ SlotSameKind g'.slots g.slots) gs' gs

def isLiveUserSlot : SlotState → Bool
  | .liveUser _ _ _ => true
  | _ => false

theorem groupLiveUserCount_eq_filter (g : GroupDesc) :
    groupLiveUserCount g = (g.slots.filter isLiveUserSlot).length :=
  rfl

theorem FineGroupSameGeom.refl (g : GroupDesc) : FineGroupSameGeom g g :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem FineGroupSameGeom.symm {g1 g2 : GroupDesc} (h : FineGroupSameGeom g1 g2) :
    FineGroupSameGeom g2 g1 :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem FineGroupSameGeom.trans {g1 g2 g3 : GroupDesc}
    (h12 : FineGroupSameGeom g1 g2) (h23 : FineGroupSameGeom g2 g3) :
    FineGroupSameGeom g1 g3 :=
  ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, h12.2.2.1.trans h23.2.2.1,
   h12.2.2.2.1.trans h23.2.2.2.1, h12.2.2.2.2.trans h23.2.2.2.2⟩

theorem FineGroupSameGeom.cnt_eq {g' g : GroupDesc} (h : FineGroupSameGeom g' g) :
    g'.cnt = g.cnt := by
  unfold GroupDesc.cnt
  rw [h.2.2.2.2]

theorem FineGroupSameGeom.stride_eq {g' g : GroupDesc} (h : FineGroupSameGeom g' g) :
    g'.stride = g.stride := by
  unfold GroupDesc.stride
  rw [h.2.1, h.2.2.1, h.2.2.2.2]

theorem FineGroupSameGeom.groupFineGeom_iff {g' g : GroupDesc} (h : FineGroupSameGeom g' g) :
    GroupFineGeom g' ↔ GroupFineGeom g := by
  unfold GroupFineGeom
  rw [h.2.1, h.2.2.1, h.2.2.2.1, h.cnt_eq]

private theorem forall2_slotSameKind_refl : ∀ xs : List SlotState, List.Forall₂ SlotSameKind xs xs
  | [] => .nil
  | _ :: rest => .cons (Or.inl rfl) (forall2_slotSameKind_refl rest)

theorem FineSameGroupsSlotKind.refl : ∀ gs : List GroupDesc, FineSameGroupsSlotKind gs gs
  | [] => .nil
  | g :: rest => .cons ⟨FineGroupSameGeom.refl g, forall2_slotSameKind_refl g.slots⟩ (refl rest)

theorem slotSameKind_fine_props {s1 s2 : SlotState} (h : SlotSameKind s1 s2) :
    isLiveUserSlot s1 = isLiveUserSlot s2 ∧
    slotIs63Large s1 = slotIs63Large s2 ∧
    (∀ alignMap, slotDecl63 alignMap s1 = slotDecl63 alignMap s2) ∧
    (∀ p req eff, s1 = .liveUser p req eff ↔ s2 = .liveUser p req eff) := by
  rcases h with rfl | ⟨hf1, hf2⟩
  · exact ⟨rfl, rfl, fun _ => rfl, fun _ _ _ => Iff.rfl⟩
  · cases s1 <;> cases s2 <;>
      simp_all [SlotState.isFree, isLiveUserSlot, slotIs63Large, slotDecl63]

theorem forall2_slotSameKind_props {xs ys : List SlotState} (h : List.Forall₂ SlotSameKind xs ys) :
    (xs.filter isLiveUserSlot).length = (ys.filter isLiveUserSlot).length ∧
    xs.any slotIs63Large = ys.any slotIs63Large ∧
    (∀ alignMap, (xs.map (slotDecl63 alignMap)).sum = (ys.map (slotDecl63 alignMap)).sum) ∧
    (∀ p req eff, (∃ (i : Nat) (hi : i < xs.length), xs[i]'hi = .liveUser p req eff) ↔
                  (∃ (j : Nat) (hj : j < ys.length), ys[j]'hj = .liveUser p req eff)) := by
  induction h with
  | nil =>
    refine ⟨rfl, rfl, fun _ => rfl, fun _ _ _ => ?_⟩
    constructor <;> rintro ⟨i, hi, _⟩ <;> exact False.elim (Nat.not_lt_zero i hi)
  | @cons a b l1 l2 hab _ ih =>
    have ⟨hLiveEq, hLargeEq, hDeclEq, hUserIff⟩ := slotSameKind_fine_props hab
    obtain ⟨ihLen, ihAny, ihSum, ihEx⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.filter_cons, hLiveEq]
      cases isLiveUserSlot b <;> simp [ihLen]
    · simp only [List.any_cons, hLargeEq, ihAny]
    · intro alignMap
      simp only [List.map_cons, List.sum_cons, hDeclEq alignMap, ihSum alignMap]
    · intro p req eff
      constructor
      · rintro ⟨i, hi, hEq⟩
        cases i with
        | zero =>
          exact ⟨0, Nat.zero_lt_succ _, (hUserIff p req eff).mp hEq⟩
        | succ i' =>
          have hi' : i' < l1.length := Nat.lt_of_succ_lt_succ hi
          obtain ⟨j, hj, hjEq⟩ := (ihEx p req eff).mp ⟨i', hi', hEq⟩
          exact ⟨j + 1, Nat.succ_lt_succ hj, hjEq⟩
      · rintro ⟨j, hj, hEq⟩
        cases j with
        | zero =>
          exact ⟨0, Nat.zero_lt_succ _, (hUserIff p req eff).mpr hEq⟩
        | succ j' =>
          have hj' : j' < l2.length := Nat.lt_of_succ_lt_succ hj
          obtain ⟨i, hi, hiEq⟩ := (ihEx p req eff).mpr ⟨j', hj', hEq⟩
          exact ⟨i + 1, Nat.succ_lt_succ hi, hiEq⟩

private theorem forall2_map_eq {α β : Type} {R : α → α → Prop} {f : α → β} {xs ys : List α}
    (h : List.Forall₂ R xs ys) (hf : ∀ x y, R x y → f x = f y) :
    xs.map f = ys.map f := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [hf _ _ hr, ih]

private theorem forall2_filter {α : Type} {R : α → α → Prop} {p : α → Bool} {xs ys : List α}
    (h : List.Forall₂ R xs ys) (hp : ∀ x y, R x y → p x = p y) :
    List.Forall₂ R (xs.filter p) (ys.filter p) := by
  induction h with
  | nil => exact .nil
  | @cons a b _ _ hr _ ih =>
    simp only [List.filter_cons, hp a b hr]
    cases p b
    · exact ih
    · exact .cons hr ih

private theorem forall2_filter_length_eq {α : Type} {R : α → α → Prop} {p : α → Bool} {xs ys : List α}
    (h : List.Forall₂ R xs ys) (hp : ∀ x y, R x y → p x = p y) :
    (xs.filter p).length = (ys.filter p).length :=
  (forall2_filter h hp).length_eq

private theorem forall2_filter_map_sum_eq {α : Type} {R : α → α → Prop}
    {p : α → Bool} {f : α → Nat} {xs ys : List α}
    (h : List.Forall₂ R xs ys)
    (hp : ∀ x y, R x y → p x = p y)
    (hf : ∀ x y, R x y → f x = f y) :
    ((xs.filter p).map f).sum = ((ys.filter p).map f).sum := by
  rw [forall2_map_eq (forall2_filter h hp) hf]

private theorem forall2_mem_geom {gs' gs : List GroupDesc}
    (h : FineSameGroupsSlotKind gs' gs)
    (hGeom : ∀ g ∈ gs, GroupFineGeom g) :
    ∀ g' ∈ gs', GroupFineGeom g' := by
  induction h with
  | nil => intro _ hMem; cases hMem
  | @cons g' g _ _ hhd _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hTail
    · exact (hhd.1.groupFineGeom_iff).mpr (hGeom g List.mem_cons_self)
    · exact ih (fun y hy => hGeom y (List.mem_cons_of_mem _ hy)) x hTail

private theorem forall2_liveUser_slot {gs' gs : List GroupDesc}
    (h : FineSameGroupsSlotKind gs' gs)
    {g' : GroupDesc} (hg' : g' ∈ gs') {idx : Nat} (hIdx : idx < g'.slots.length)
    {p : BitVec 64} {req eff : Nat}
    (hSlot : g'.slots[idx]'hIdx = .liveUser p req eff) :
    ∃ g ∈ gs, g'.sc = g.sc ∧ g'.maplen = g.maplen ∧
      ∃ (j : Nat) (hj : j < g.slots.length), g.slots[j]'hj = .liveUser p req eff := by
  induction h with
  | nil => cases hg'
  | @cons a b _ _ hhd _ ih =>
    rcases List.mem_cons.mp hg' with rfl | hTail
    · obtain ⟨_, _, _, hExIff⟩ := forall2_slotSameKind_props hhd.2
      obtain ⟨j, hj, hjEq⟩ := (hExIff p req eff).mp ⟨idx, hIdx, hSlot⟩
      exact ⟨b, List.mem_cons_self, hhd.1.2.1, hhd.1.2.2.1, j, hj, hjEq⟩
    · obtain ⟨g, hg, hsc, hml, j, hj, hjEq⟩ := ih hTail
      exact ⟨g, List.mem_cons_of_mem _ hg, hsc, hml, j, hj, hjEq⟩

theorem fineSameGroupsSlotKind_metaPtrs_eq {gs' gs : List GroupDesc}
    (h : FineSameGroupsSlotKind gs' gs) :
    gs'.map GroupDesc.metaPtr = gs.map GroupDesc.metaPtr :=
  forall2_map_eq h fun _ _ hr => hr.1.1

/-- Complete fine-projection invariance across `FineSameGroupsSlotKind`. -/
theorem fineSameGroupsSlotKind_preserves_all {st' st : MallocngSt}
    {alignMap : BitVec 64 → Option Nat}
    (hSame : FineSameGroupsSlotKind st'.groups st.groups) :
    ((∀ g ∈ st.groups, GroupFineGeom g) → ∀ g' ∈ st'.groups, GroupFineGeom g') ∧
    ((∀ g ∈ st.groups, ∀ idx (hIdx : idx < g.slots.length) p req eff,
        g.slots[idx]'hIdx = .liveUser p req eff →
        ∃ al, alignMap p = some al ∧
          (g.sc = 63 →
            eff - max req MallocngMinBlockCost ≤ al - 16 ∧
            g.maplen * 4096 ≤ declCost63 req al)) →
      (∀ g' ∈ st'.groups, ∀ idx (hIdx : idx < g'.slots.length) p req eff,
        g'.slots[idx]'hIdx = .liveUser p req eff →
        ∃ al, alignMap p = some al ∧
          (g'.sc = 63 →
            eff - max req MallocngMinBlockCost ≤ al - 16 ∧
            g'.maplen * 4096 ≤ declCost63 req al))) ∧
    (∀ k, liveSlotsInClass st' k = liveSlotsInClass st k) ∧
    (∀ k, (allGroups st' k).length = (allGroups st k).length) ∧
    (∀ ch pSc, (nestedEdge st' ch pSc).length = (nestedEdge st ch pSc).length) ∧
    (∀ k, rootBytes st' k = rootBytes st k) ∧
    large63DeclBytes st' alignMap = large63DeclBytes st alignMap ∧
    (large63Groups st').length = (large63Groups st).length ∧
    (straddle63Groups st').length = (straddle63Groups st).length ∧
    straddle63Bytes st' = straddle63Bytes st := by
  have hScPred : ∀ k (x y : GroupDesc),
      (FineGroupSameGeom x y ∧ List.Forall₂ SlotSameKind x.slots y.slots) →
      (x.sc == k) = (y.sc == k) := by
    intro k x y hr; rw [hr.1.2.1]
  have h63Groups : FineSameGroupsSlotKind (groups63 st') (groups63 st) :=
    forall2_filter hSame (hScPred 63)
  have hIsLargeEq : ∀ (x y : GroupDesc),
      (FineGroupSameGeom x y ∧ List.Forall₂ SlotSameKind x.slots y.slots) →
      isLarge63Group x = isLarge63Group y := by
    intro x y hr
    unfold isLarge63Group
    exact (forall2_slotSameKind_props hr.2).2.1
  refine ⟨forall2_mem_geom hSame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hUser g' hg' idx hIdx p req eff hSlot
    obtain ⟨g, hg, hsc, hml, j, hj, hjEq⟩ := forall2_liveUser_slot hSame hg' hIdx hSlot
    obtain ⟨al, hAl, hBnd⟩ := hUser g hg j hj p req eff hjEq
    refine ⟨al, hAl, fun h63 => ?_⟩
    have hB := hBnd (hsc ▸ h63)
    exact ⟨hB.1, hml ▸ hB.2⟩
  · intro k
    unfold liveSlotsInClass allGroups
    refine forall2_filter_map_sum_eq hSame (hScPred k) ?_
    intro x y hr
    rw [groupLiveUserCount_eq_filter, groupLiveUserCount_eq_filter]
    exact (forall2_slotSameKind_props hr.2).1
  · intro k
    unfold allGroups
    exact forall2_filter_length_eq hSame (hScPred k)
  · intro ch pSc
    unfold nestedEdge
    refine forall2_filter_length_eq hSame fun x y hr => ?_
    rw [hr.1.2.1, hr.1.2.2.1, hr.1.2.2.2.1]
  · intro k
    unfold rootBytes
    refine forall2_filter_map_sum_eq hSame
      (fun x y hr => by rw [hr.1.2.1, hr.1.2.2.1])
      (fun x y hr => by rw [hr.1.2.2.1])
  · unfold large63DeclBytes large63Groups
    refine forall2_filter_map_sum_eq h63Groups hIsLargeEq fun x y hr => ?_
    exact (forall2_slotSameKind_props hr.2).2.2.1 alignMap
  · unfold large63Groups
    exact forall2_filter_length_eq h63Groups hIsLargeEq
  · unfold straddle63Groups
    exact forall2_filter_length_eq h63Groups fun x y hr => by rw [hIsLargeEq x y hr]
  · unfold straddle63Bytes straddle63Groups
    exact forall2_filter_map_sum_eq h63Groups
      (fun x y hr => by rw [hIsLargeEq x y hr])
      (fun x y hr => by rw [hr.1.2.2.1])

/-! ## Non-`liveUser` Slot Updates -/

private theorem replicate_no_liveUser (n : Nat) (s : SlotState)
    (hs : ∀ p req eff, s ≠ .liveUser p req eff) :
    (List.replicate n s).filter isLiveUserSlot = [] ∧
    (List.replicate n s).any slotIs63Large = false ∧
    (∀ alignMap, ((List.replicate n s).map (slotDecl63 alignMap)).sum = 0) ∧
    (∀ x ∈ List.replicate n s, ∀ p req eff, x ≠ .liveUser p req eff) := by
  have hL : isLiveUserSlot s = false := by
    cases s with
    | liveUser p req eff => exact False.elim (hs p req eff rfl)
    | _ => rfl
  have h63 : slotIs63Large s = false := by
    cases s with
    | liveUser p req eff => exact False.elim (hs p req eff rfl)
    | _ => rfl
  have hD : ∀ alignMap, slotDecl63 alignMap s = 0 := by
    intro alignMap
    cases s with
    | liveUser p req eff => exact False.elim (hs p req eff rfl)
    | _ => rfl
  induction n with
  | zero =>
    exact ⟨rfl, rfl, fun _ => rfl, fun _ hMem => False.elim (List.not_mem_nil hMem)⟩
  | succ k ih =>
    obtain ⟨ihF, ihA, ihS, ihM⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [List.replicate_succ, hL, ihF]
    · simp [List.replicate_succ, h63, ihA]
    · intro alignMap
      simp [List.replicate_succ, hD alignMap]
    · intro x hx p req eff
      rcases List.mem_cons.mp hx with rfl | hTail
      · exact hs p req eff
      · exact ihM x hTail p req eff

theorem newGroupSlots_fine_zero (cg : GroupDesc) (lastIdx activeIdx : Nat)
    (hSlots : cg.slots = newGroupSlots lastIdx activeIdx) :
    groupLiveUserCount cg = 0 ∧
    isLarge63Group cg = false ∧
    (∀ alignMap, (cg.slots.map (slotDecl63 alignMap)).sum = 0) ∧
    (∀ idx (hIdx : idx < cg.slots.length) p req eff, cg.slots[idx]'hIdx ≠ .liveUser p req eff) := by
  have h1 := replicate_no_liveUser activeIdx .freeAvail (by intro _ _ _ h; cases h)
  have h2 := replicate_no_liveUser (lastIdx - activeIdx) .freeInactive (by intro _ _ _ h; cases h)
  rw [groupLiveUserCount_eq_filter]
  unfold isLarge63Group
  rw [hSlots]
  unfold newGroupSlots
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [isLiveUserSlot, List.filter_append, h1.1, h2.1]
  · simp [slotIs63Large, List.any_append, h1.2.1, h2.2.1]
  · intro alignMap
    simp [slotDecl63, List.map_append]
  · intro idx hIdx p req eff hEq
    have hMem : SlotState.liveUser p req eff ∈
        (.claimed :: (List.replicate activeIdx .freeAvail ++ List.replicate (lastIdx - activeIdx) .freeInactive)) := by
      rw [← hEq]
      exact List.getElem_mem hIdx
    rcases List.mem_cons.mp hMem with hHd | hTl
    · cases hHd
    · rcases List.mem_append.mp hTl with hA | hI
      · exact h1.2.2.2 _ hA p req eff rfl
      · exact h2.2.2.2 _ hI p req eff rfl

theorem list_set_nonLiveUser {xs : List SlotState} {idx : Nat} {newS : SlotState}
    (hIdx : idx < xs.length)
    (hOld : ∀ p req eff, xs[idx]'hIdx ≠ .liveUser p req eff)
    (hNew : ∀ p req eff, newS ≠ .liveUser p req eff) :
    ((xs.set idx newS).filter isLiveUserSlot).length = (xs.filter isLiveUserSlot).length ∧
    (xs.set idx newS).any slotIs63Large = xs.any slotIs63Large ∧
    (∀ alignMap, ((xs.set idx newS).map (slotDecl63 alignMap)).sum = (xs.map (slotDecl63 alignMap)).sum) ∧
    (∀ j (hj : j < (xs.set idx newS).length) p req eff,
      (xs.set idx newS)[j]'hj = .liveUser p req eff →
      ∃ hj0 : j < xs.length, xs[j]'hj0 = .liveUser p req eff) := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hIdx)
  | cons hd tl ih =>
    cases idx with
    | zero =>
      have hOldL : isLiveUserSlot hd = false := by
        cases hd with
        | liveUser p req eff => exact False.elim (hOld p req eff rfl)
        | _ => rfl
      have hNewL : isLiveUserSlot newS = false := by
        cases newS with
        | liveUser p req eff => exact False.elim (hNew p req eff rfl)
        | _ => rfl
      have hOld63 : slotIs63Large hd = false := by
        cases hd with
        | liveUser p req eff => exact False.elim (hOld p req eff rfl)
        | _ => rfl
      have hNew63 : slotIs63Large newS = false := by
        cases newS with
        | liveUser p req eff => exact False.elim (hNew p req eff rfl)
        | _ => rfl
      have hOldD : ∀ alignMap, slotDecl63 alignMap hd = 0 := by
        intro alignMap
        cases hd with
        | liveUser p req eff => exact False.elim (hOld p req eff rfl)
        | _ => rfl
      have hNewD : ∀ alignMap, slotDecl63 alignMap newS = 0 := by
        intro alignMap
        cases newS with
        | liveUser p req eff => exact False.elim (hNew p req eff rfl)
        | _ => rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hOldL, hNewL]
      · simp [hOld63, hNew63]
      · intro alignMap
        simp [hOldD alignMap, hNewD alignMap]
      · intro j hj p req eff hEq
        cases j with
        | zero => exact False.elim (hNew p req eff hEq)
        | succ j' =>
          have hj0 : j' + 1 < (hd :: tl).length := by simpa [List.length_set] using hj
          exact ⟨hj0, hEq⟩
    | succ idx' =>
      have hIdx' : idx' < tl.length := Nat.lt_of_succ_lt_succ hIdx
      obtain ⟨ihF, ihA, ihS, ihU⟩ := ih hIdx' hOld
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.set_cons_succ, List.filter_cons]
        cases isLiveUserSlot hd <;> simp [ihF]
      · simp only [List.set_cons_succ, List.any_cons, ihA]
      · intro alignMap
        simp only [List.set_cons_succ, List.map_cons, List.sum_cons, ihS alignMap]
      · intro j hj p req eff hEq
        cases j with
        | zero =>
          exact ⟨Nat.zero_lt_succ _, hEq⟩
        | succ j' =>
          have hj' : j' < (tl.set idx' newS).length := Nat.lt_of_succ_lt_succ hj
          obtain ⟨hj0', hEq0⟩ := ihU j' hj' p req eff hEq
          exact ⟨Nat.succ_lt_succ hj0', hEq0⟩

theorem nodup_metaPtr_eq {gs : List GroupDesc} (hnd : (gs.map GroupDesc.metaPtr).Nodup)
    {g1 g2 : GroupDesc} (h1 : g1 ∈ gs) (h2 : g2 ∈ gs) (hm : g1.metaPtr = g2.metaPtr) :
    g1 = g2 := by
  induction gs with
  | nil => cases h1
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1Tl
    · rcases List.mem_cons.mp h2 with rfl | h2Tl
      · rfl
      · exfalso
        exact hnd.1 (hm ▸ List.mem_map_of_mem h2Tl)
    · rcases List.mem_cons.mp h2 with rfl | h2Tl
      · exfalso
        exact hnd.1 (hm.symm ▸ List.mem_map_of_mem h1Tl)
      · exact ih hnd.2 h1Tl h2Tl

private theorem forall2_of_forall_mem {α : Type} {R : α → α → Prop} {f : α → α} :
    ∀ {gs : List α}, (∀ g ∈ gs, R (f g) g) → List.Forall₂ R (gs.map f) gs
  | [], _ => .nil
  | a :: _, h => .cons (h a List.mem_cons_self)
      (forall2_of_forall_mem fun g hg => h g (List.mem_cons_of_mem _ hg))

private theorem forall2_mem_left {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hm => False.elim (List.not_mem_nil hm)
  | _, _, .cons hr htl, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hTl
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hry⟩ := forall2_mem_left htl _ hTl
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

/-- Updating a single non-`.liveUser` slot in a unique `metaPtr` group preserves all fine
    invariants and group projections. -/
theorem map_set_nonLiveUser_preserves_all {gs : List GroupDesc}
    {g0 : GroupDesc} {idx : Nat} {newS : SlotState} {alignMap : BitVec 64 → Option Nat}
    (hIdx : idx < g0.slots.length)
    (hOld : ∀ p req eff, g0.slots[idx]'hIdx ≠ .liveUser p req eff)
    (hNew : ∀ p req eff, newS ≠ .liveUser p req eff) :
    let gs' := gs.map fun g =>
      if g.metaPtr == g0.metaPtr then { g0 with slots := g0.slots.set idx newS } else g
    gs'.map GroupDesc.metaPtr = gs.map GroupDesc.metaPtr ∧
    ((gs.map GroupDesc.metaPtr).Nodup → g0 ∈ gs →
      let st0 : MallocngSt := { emptyMallocngSt 0#64 with groups := gs }
      let st' : MallocngSt := { emptyMallocngSt 0#64 with groups := gs' }
      ((∀ g ∈ gs, GroupFineGeom g) → ∀ g' ∈ gs', GroupFineGeom g') ∧
      ((∀ g ∈ gs, ∀ j (hj : j < g.slots.length) p req eff,
          g.slots[j]'hj = .liveUser p req eff →
          ∃ al, alignMap p = some al ∧
            (g.sc = 63 →
              eff - max req MallocngMinBlockCost ≤ al - 16 ∧
              g.maplen * 4096 ≤ declCost63 req al)) →
        (∀ g' ∈ gs', ∀ j (hj : j < g'.slots.length) p req eff,
          g'.slots[j]'hj = .liveUser p req eff →
          ∃ al, alignMap p = some al ∧
            (g'.sc = 63 →
              eff - max req MallocngMinBlockCost ≤ al - 16 ∧
              g'.maplen * 4096 ≤ declCost63 req al))) ∧
      (∀ k, liveSlotsInClass st' k = liveSlotsInClass st0 k) ∧
      (∀ k, (allGroups st' k).length = (allGroups st0 k).length) ∧
      (∀ ch pSc, (nestedEdge st' ch pSc).length = (nestedEdge st0 ch pSc).length) ∧
      (∀ k, rootBytes st' k = rootBytes st0 k) ∧
      large63DeclBytes st' alignMap = large63DeclBytes st0 alignMap ∧
      (large63Groups st').length = (large63Groups st0).length ∧
      (straddle63Groups st').length = (straddle63Groups st0).length ∧
      straddle63Bytes st' = straddle63Bytes st0) := by
  intro gs'
  have hMetaEq : gs'.map GroupDesc.metaPtr = gs.map GroupDesc.metaPtr := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply]
    cases hEq : g.metaPtr == g0.metaPtr
    · rfl
    · exact (beq_iff_eq.mp hEq).symm
  refine ⟨hMetaEq, fun hnd hg0 => ?_⟩
  intro st0 st'
  have hSetProps := list_set_nonLiveUser hIdx hOld hNew
  let R (x y : GroupDesc) : Prop :=
    FineGroupSameGeom x y ∧
    groupLiveUserCount x = groupLiveUserCount y ∧
    isLarge63Group x = isLarge63Group y ∧
    (x.slots.map (slotDecl63 alignMap)).sum = (y.slots.map (slotDecl63 alignMap)).sum ∧
    (∀ j (hj : j < x.slots.length) p req eff,
      x.slots[j]'hj = .liveUser p req eff →
      ∃ hj0 : j < y.slots.length, y.slots[j]'hj0 = .liveUser p req eff)
  have hRel : List.Forall₂ R gs' gs := by
    refine forall2_of_forall_mem fun g hg => ?_
    by_cases hBeq : (g.metaPtr == g0.metaPtr) = true
    · have hgEq : g = g0 := nodup_metaPtr_eq hnd hg hg0 (beq_iff_eq.mp hBeq)
      subst hgEq
      simp only [hBeq, ↓reduceIte]
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, hSetProps.2.2.1 alignMap, hSetProps.2.2.2⟩
      · rw [groupLiveUserCount_eq_filter, groupLiveUserCount_eq_filter]
        exact hSetProps.1
      · unfold isLarge63Group
        exact hSetProps.2.1
    · simp only [Bool.not_eq_true] at hBeq
      simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
      exact ⟨FineGroupSameGeom.refl g, rfl, rfl, rfl, fun j hj _ _ _ h => ⟨hj, h⟩⟩
  have hScPred : ∀ k (x y : GroupDesc), R x y → (x.sc == k) = (y.sc == k) := by
    intro k x y hr; rw [hr.1.2.1]
  have h63Rel : List.Forall₂ R (groups63 st') (groups63 st0) :=
    forall2_filter hRel (hScPred 63)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hGeom z hz
    obtain ⟨y, hy, hr⟩ := forall2_mem_left hRel z hz
    exact (hr.1.groupFineGeom_iff).mpr (hGeom y hy)
  · intro hUser z hz j hj p req eff hSlot
    obtain ⟨y, hy, hr⟩ := forall2_mem_left hRel z hz
    obtain ⟨hj0, hSlot0⟩ := hr.2.2.2.2 j hj p req eff hSlot
    obtain ⟨al, hAl, hBnd⟩ := hUser y hy j hj0 p req eff hSlot0
    refine ⟨al, hAl, fun h63 => ?_⟩
    have hB := hBnd (hr.1.2.1 ▸ h63)
    exact ⟨hB.1, hr.1.2.2.1 ▸ hB.2⟩
  · intro k; unfold liveSlotsInClass allGroups
    exact forall2_filter_map_sum_eq hRel (hScPred k) fun _ _ hr => hr.2.1
  · intro k; unfold allGroups
    exact forall2_filter_length_eq hRel (hScPred k)
  · intro ch pSc; unfold nestedEdge
    exact forall2_filter_length_eq hRel fun _ _ hr => by rw [hr.1.2.1, hr.1.2.2.1, hr.1.2.2.2.1]
  · intro k; unfold rootBytes
    exact forall2_filter_map_sum_eq hRel
      (fun _ _ hr => by rw [hr.1.2.1, hr.1.2.2.1])
      (fun _ _ hr => by rw [hr.1.2.2.1])
  · unfold large63DeclBytes large63Groups
    exact forall2_filter_map_sum_eq h63Rel (fun _ _ hr => hr.2.2.1) (fun _ _ hr => hr.2.2.2.1)
  · unfold large63Groups
    exact forall2_filter_length_eq h63Rel (fun _ _ hr => hr.2.2.1)
  · unfold straddle63Groups
    exact forall2_filter_length_eq h63Rel (fun _ _ hr => by rw [hr.2.2.1])
  · unfold straddle63Bytes straddle63Groups
    exact forall2_filter_map_sum_eq h63Rel
      (fun _ _ hr => by rw [hr.2.2.1])
      (fun _ _ hr => by rw [hr.1.2.2.1])

/-! ## Root and Nested `GroupFineGeom` Creation -/

private def checkRootParamsHelper : Bool :=
  (List.range 48).all fun sc =>
    (if 24 ≤ sc then validRootCntDec sc 1 else true) &&
    (if 7 ≤ sc then
      (List.range 33).all fun cnt =>
        if decide (2 ≤ cnt) && decide (cnt * slotStride sc + 13 ≤ 1048576) &&
           (if sc ≤ 25 then decide (cnt * slotStride sc + 13 ≤ 65536) else true) then
          validRootCntDec sc cnt
        else true
     else true)

private theorem checkRootParamsHelper_true : checkRootParamsHelper = true := by
  decide +kernel

theorem validRootCnt_of_rootMmapParams {sc cnt len : Nat}
    (hsc7 : 7 ≤ sc) (hsc48 : sc < 48)
    (hOk : RootMmapParamsOk sc cnt len)
    (hCnt1 : cnt = 1 → 24 ≤ sc) :
    ValidRootCnt sc cnt := by
  have hRow := List.all_eq_true.mp checkRootParamsHelper_true sc (List.mem_range.mpr hsc48)
  rw [Bool.and_eq_true] at hRow
  have hCntLo : 1 ≤ cnt := hOk.1
  have hCntHi : cnt ≤ 32 := hOk.2.1
  by_cases hc1 : cnt = 1
  · subst hc1
    have h24 : 24 ≤ sc := hCnt1 rfl
    have hL := hRow.1
    simp only [h24, ↓reduceIte] at hL
    exact validRootCnt_iff_dec.mpr hL
  · have hc2 : 2 ≤ cnt := by omega
    have hNeZero : (cnt - 1 == 0) = false := by
      rw [beq_eq_false_iff_ne]; omega
    have hStrict : 12 + cnt * slotStride sc < len := by
      have h8 := hOk.2.2.2.2.2.2.2
      simp only [hNeZero] at h8
      exact h8
    have hLenMax : len ≤ 1048576 := hOk.2.2.2.2.1
    have hProdMax : cnt * slotStride sc + 13 ≤ 1048576 := by omega
    have h25Cond : (if sc ≤ 25 then decide (cnt * slotStride sc + 13 ≤ 65536) else true) = true := by
      by_cases h25 : sc ≤ 25
      · have hLen25 : len ≤ 65536 := hOk.2.2.2.2.2.1 h25
        simp only [h25, ↓reduceIte, decide_eq_true_eq]
        omega
      · simp [h25]
    have hR := hRow.2
    simp only [hsc7, ↓reduceIte] at hR
    have hCell := List.all_eq_true.mp hR cnt (List.mem_range.mpr (by omega))
    have hCond : (decide (2 ≤ cnt) && decide (cnt * slotStride sc + 13 ≤ 1048576) &&
        (if sc ≤ 25 then decide (cnt * slotStride sc + 13 ≤ 65536) else true)) = true := by
      simp only [decide_eq_true hc2, decide_eq_true hProdMax, h25Cond, Bool.true_and]
    rw [hCond] at hCell
    simp only [↓reduceIte] at hCell
    exact validRootCnt_iff_dec.mpr hCell

theorem groupFineGeom_of_rootGroup {sc cnt' : Nat} {cg : GroupDesc}
    (hsc : sc < 48)
    (hSm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt' = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hGt2048 : 2048 < cnt' * slotStride sc + 16)
    (hMapPos : 0 < cg.maplen) (hCgSc : cg.sc = sc)
    (hOk : RootMmapParamsOk sc cg.cnt (cg.maplen * 4096))
    (hCnt1 : cg.cnt = 1 → 24 ≤ sc)
    (hPageLe : cg.maplen * 4096 ≤ pageAlignUp (cg.cnt * slotStride sc + 16))
    (hGrpMax : cg.maplen * 4096 ≤ Cost.grpMax sc 128) :
    GroupFineGeom cg ∧ cg.maplen * 4096 ≤ maxRootBytes sc := by
  have hsc7 : 7 ≤ sc := root_sc_ge_seven_of_gt2048 hSm hGt2048
  have hValid : ValidRootCnt sc cg.cnt :=
    validRootCnt_of_rootMmapParams hsc7 hsc hOk hCnt1
  have ⟨hMaxB, hCeilB⟩ := validRootCnt_bounds hValid
  have hLenMax : cg.maplen * 4096 ≤ maxRootBytes sc := Nat.le_trans hPageLe hMaxB
  have hLenCeil : cg.maplen * 4096 ≤ ceilRootPerSlot sc * cg.cnt := Nat.le_trans hPageLe hCeilB
  refine ⟨?_, hLenMax⟩
  unfold GroupFineGeom
  rw [hCgSc]
  refine ⟨fun _ => hValid.2.2.1, fun _ _ => ⟨hValid, hLenMax, hLenCeil, hGrpMax⟩, fun _ hZero => ?_⟩
  omega

private def checkNestedDepthDec : Bool :=
  (List.range 48).all fun sc =>
    (List.range 33).all fun cnt =>
      if validNestedCntDec sc cnt then
        let pSc := sizeToClassUnits (cnt * sizeClass sc)
        decide (allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc)
      else true

private theorem checkNestedDepthDec_true : checkNestedDepthDec = true := by
  decide +kernel

theorem allocSlotDepthBound_nested_lt {sc cnt' : Nat}
    (hsc : sc < 48) (hv : ValidNestedCnt sc cnt') :
    allocSlotDepthBound (sizeToClassUnits (cnt' * sizeClass sc)) + 1 ≤ allocSlotDepthBound sc := by
  have hcnt : cnt' < 33 := by have := hv.2.1; omega
  have hDec : validNestedCntDec sc cnt' = true := validNestedCnt_iff_dec.mp hv
  have hRow := List.all_eq_true.mp checkNestedDepthDec_true sc (List.mem_range.mpr hsc)
  have hCell := List.all_eq_true.mp hRow cnt' (List.mem_range.mpr hcnt)
  simp only [hDec, ↓reduceIte, decide_eq_true_eq] at hCell
  exact hCell

theorem groupFineGeom_of_nestedGroup {sc cnt' : Nat} {cg : GroupDesc}
    (hsc : sc < 48) (hv : ValidNestedCnt sc cnt')
    (hCgSc : cg.sc = sc) (hCgMap0 : cg.maplen = 0)
    (hCgCap : cg.nestedCap = slotStride (sizeToClassUnits (cnt' * sizeClass sc)) - 4)
    (hCgLast : cg.lastIdx = cnt' - 1) :
    GroupFineGeom cg := by
  have hBnd := validNestedCnt_bounds hsc hv
  have hCntEq : cg.cnt = cnt' := by
    unfold GroupDesc.cnt
    have h2 : 2 ≤ cnt' := hv.1
    omega
  unfold GroupFineGeom
  rw [hCgSc, hCgMap0, hCntEq]
  refine ⟨fun _ => hBnd.1, fun _ hPos => by omega, fun _ _ q hq hCapEq => ?_⟩
  rw [hCgCap] at hCapEq
  have hqEq : sizeToClassUnits (cnt' * sizeClass sc) = q :=
    slotStride_sub4_inj hBnd.2.1 hq hCapEq
  rw [← hqEq]
  exact ⟨hBnd.2.2.2.1, hBnd.2.2.2.2⟩

/-! ## `AllocSlotInvPres` and Trace-Step Combinators -/

/-- Fine-invariant preservation relation across `alloc_slot(sc, req)` (`sc < 48`) from `st0` to `st'`:
    all `.liveUser` / `sc = 63` metrics are preserved verbatim, classes `< sc` have unchanged
    group counts/edges/root bytes, and all classes `< 48` stay within `(gBound, edgeBound, rBound)`
    for the witness `pk`. -/
structure AllocSlotInvPres (sc : Nat) (pk : List Nat)
    (alignMap : BitVec 64 → Option Nat) (st0 st' : MallocngSt) : Prop where
  groups_geom : ∀ g ∈ st'.groups, GroupFineGeom g
  user_slots_wf :
    ∀ g ∈ st'.groups, ∀ idx (hIdx : idx < g.slots.length) p req eff,
      g.slots[idx]'hIdx = .liveUser p req eff →
      ∃ al, alignMap p = some al ∧
        (g.sc = 63 →
          eff - max req MallocngMinBlockCost ≤ al - 16 ∧
          g.maplen * 4096 ≤ declCost63 req al)
  live_eq : ∀ k, liveSlotsInClass st' k = liveSlotsInClass st0 k
  below_sc_eq :
    ∀ k < sc,
      (allGroups st' k).length = (allGroups st0 k).length ∧
      (∀ q, (nestedEdge st' k q).length = (nestedEdge st0 k q).length) ∧
      rootBytes st' k = rootBytes st0 k
  groups_le : ∀ k < 48, (allGroups st' k).length ≤ gBound pk k
  edges_le : ∀ ch < 48, ∀ pSc < 48, (nestedEdge st' ch pSc).length ≤ edgeBound pk ch pSc
  roots_le : ∀ k < 48, rootBytes st' k ≤ rBound pk k
  large63_eq :
    large63DeclBytes st' alignMap = large63DeclBytes st0 alignMap ∧
    (large63Groups st').length = (large63Groups st0).length
  straddle63_eq :
    (straddle63Groups st').length = (straddle63Groups st0).length ∧
    straddle63Bytes st' = straddle63Bytes st0

theorem AllocSlotInvPres.refl {sc : Nat} {pk : List Nat}
    {alignMap : BitVec 64 → Option Nat} {st0 : MallocngSt}
    (hGeom : ∀ g ∈ st0.groups, GroupFineGeom g)
    (hUser : ∀ g ∈ st0.groups, ∀ idx (hIdx : idx < g.slots.length) p req eff,
      g.slots[idx]'hIdx = .liveUser p req eff →
      ∃ al, alignMap p = some al ∧
        (g.sc = 63 →
          eff - max req MallocngMinBlockCost ≤ al - 16 ∧
          g.maplen * 4096 ≤ declCost63 req al))
    (hGrp : ∀ k < 48, (allGroups st0 k).length ≤ gBound pk k)
    (hEdge : ∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc)
    (hRoot : ∀ k < 48, rootBytes st0 k ≤ rBound pk k) :
    AllocSlotInvPres sc pk alignMap st0 st0 where
  groups_geom := hGeom
  user_slots_wf := hUser
  live_eq := fun _ => rfl
  below_sc_eq := fun _ _ => ⟨rfl, fun _ => rfl, rfl⟩
  groups_le := hGrp
  edges_le := hEdge
  roots_le := hRoot
  large63_eq := ⟨rfl, rfl⟩
  straddle63_eq := ⟨rfl, rfl⟩

/-- `pop` case of `AllocSlotFineTrace`: claiming a free slot in `sc` preserves `AllocSlotInvPres`
    verbatim for any output state `st'` with `(st'.groups.map GroupDesc.metaPtr).Nodup`. -/
theorem allocSlotInvPres_pop {sc idx : Nat} {pk : List Nat}
    {alignMap : BitVec 64 → Option Nat} {st0 st_f st' : MallocngSt} {g_f : GroupDesc}
    (hInit : AllocSlotInvPres sc pk alignMap st0 st0)
    (hPre : FineSameGroupsSlotKind st_f.groups st0.groups)
    (hgf : g_f ∈ st_f.groups)
    (hIdx : idx < g_f.slots.length)
    (hFree : (g_f.slots[idx]'hIdx).isFree = true)
    (hClaim : FineSameGroupsSlotKind st'.groups
      (st_f.groups.map fun g =>
        if g.metaPtr == g_f.metaPtr then { g with slots := g.slots.set idx .claimed } else g))
    (hNodup' : (st'.groups.map GroupDesc.metaPtr).Nodup) :
    AllocSlotInvPres sc pk alignMap st0 st' := by
  have hOldNotUser : ∀ p req eff, g_f.slots[idx]'hIdx ≠ .liveUser p req eff := by
    intro p req eff hEq
    rw [hEq] at hFree
    cases hFree
  have hNewNotUser : ∀ p req eff, SlotState.claimed ≠ .liveUser p req eff := by
    intro _ _ _ h; cases h
  let gsA := st_f.groups.map fun g =>
    if g.metaPtr == g_f.metaPtr then { g with slots := g.slots.set idx .claimed } else g
  let gsB := st_f.groups.map fun g =>
    if g.metaPtr == g_f.metaPtr then { g_f with slots := g_f.slots.set idx .claimed } else g
  have hMetaClaim : st'.groups.map GroupDesc.metaPtr = gsA.map GroupDesc.metaPtr :=
    fineSameGroupsSlotKind_metaPtrs_eq hClaim
  have hMetaA : gsA.map GroupDesc.metaPtr = st_f.groups.map GroupDesc.metaPtr := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply]
    cases g.metaPtr == g_f.metaPtr <;> rfl
  have hNodupF : (st_f.groups.map GroupDesc.metaPtr).Nodup := by
    rwa [hMetaClaim, hMetaA] at hNodup'
  have hAB : gsA = gsB := by
    refine List.map_congr_left fun g hg => ?_
    by_cases hEq : (g.metaPtr == g_f.metaPtr) = true
    · have hgEq : g = g_f := nodup_metaPtr_eq hNodupF hg hgf (beq_iff_eq.mp hEq)
      subst hgEq; rfl
    · simp only [Bool.not_eq_true] at hEq
      simp [hEq]
  have hClaimB : FineSameGroupsSlotKind st'.groups gsB := hAB ▸ hClaim
  have hP0 := fineSameGroupsSlotKind_preserves_all (alignMap := alignMap) hPre
  have hSet := map_set_nonLiveUser_preserves_all (gs := st_f.groups) (alignMap := alignMap)
    hIdx hOldNotUser hNewNotUser
  have hPSet := hSet.2 hNodupF hgf
  let stMid : MallocngSt := { emptyMallocngSt 0#64 with groups := gsB }
  have hPClaim := fineSameGroupsSlotKind_preserves_all (st' := st') (st := stMid) (alignMap := alignMap) hClaimB
  have hStF_eq : ∀ k,
      liveSlotsInClass { emptyMallocngSt 0#64 with groups := st_f.groups } k = liveSlotsInClass st_f k ∧
      allGroups { emptyMallocngSt 0#64 with groups := st_f.groups } k = allGroups st_f k ∧
      (∀ q, nestedEdge { emptyMallocngSt 0#64 with groups := st_f.groups } k q = nestedEdge st_f k q) ∧
      rootBytes { emptyMallocngSt 0#64 with groups := st_f.groups } k = rootBytes st_f k :=
    fun _ => ⟨rfl, rfl, fun _ => rfl, rfl⟩
  refine {
    groups_geom := hPClaim.1 (hPSet.1 (hP0.1 hInit.groups_geom))
    user_slots_wf := hPClaim.2.1 (hPSet.2.1 (hP0.2.1 hInit.user_slots_wf))
    live_eq := fun k => by rw [hPClaim.2.2.1 k, hPSet.2.2.1 k, (hStF_eq k).1, hP0.2.2.1 k]
    below_sc_eq := fun k hk => ⟨
      by rw [hPClaim.2.2.2.1 k, hPSet.2.2.2.1 k, (hStF_eq k).2.1, hP0.2.2.2.1 k],
      fun q => by rw [hPClaim.2.2.2.2.1 k q, hPSet.2.2.2.2.1 k q, (hStF_eq k).2.2.1 q, hP0.2.2.2.2.1 k q],
      by rw [hPClaim.2.2.2.2.2.1 k, hPSet.2.2.2.2.2.1 k, (hStF_eq k).2.2.2, hP0.2.2.2.2.2.1 k]⟩
    groups_le := fun k hk => by
      rw [hPClaim.2.2.2.1 k, hPSet.2.2.2.1 k, (hStF_eq k).2.1, hP0.2.2.2.1 k]
      exact hInit.groups_le k hk
    edges_le := fun ch hch pSc hpSc => by
      rw [hPClaim.2.2.2.2.1 ch pSc, hPSet.2.2.2.2.1 ch pSc, (hStF_eq ch).2.2.1 pSc, hP0.2.2.2.2.1 ch pSc]
      exact hInit.edges_le ch hch pSc hpSc
    roots_le := fun k hk => by
      rw [hPClaim.2.2.2.2.2.1 k, hPSet.2.2.2.2.2.1 k, (hStF_eq k).2.2.2, hP0.2.2.2.2.2.1 k]
      exact hInit.roots_le k hk
    large63_eq := ⟨
      by rw [hPClaim.2.2.2.2.2.2.1, hPSet.2.2.2.2.2.2.1]; exact hP0.2.2.2.2.2.2.1,
      by rw [hPClaim.2.2.2.2.2.2.2.1, hPSet.2.2.2.2.2.2.2.1]; exact hP0.2.2.2.2.2.2.2.1⟩
    straddle63_eq := ⟨
      by rw [hPClaim.2.2.2.2.2.2.2.2.1, hPSet.2.2.2.2.2.2.2.2.1]; exact hP0.2.2.2.2.2.2.2.2.1,
      by rw [hPClaim.2.2.2.2.2.2.2.2.2, hPSet.2.2.2.2.2.2.2.2.2]; exact hP0.2.2.2.2.2.2.2.2.2⟩
  }

/-- `rootGroup` case of `AllocSlotFineTrace`: `st_ag.ctx.active[sc] = 0#64` yields `+1` group and
    `+maxRootBytes sc` headroom via `active_zero_occ_bounds`. -/
theorem allocSlotInvPres_rootGroup {inflight sc cnt' activeIdx : Nat}
    {base brkStart brk_ag : BitVec 64} {liveCost peakCost : Nat}
    {pk : List Nat} {alignMap : BitVec 64 → Option Nat}
    {st0 st_ag st' : MallocngSt} {cg : GroupDesc}
    (hsc : sc < 48) (hInflight : inflight ≤ 4)
    (hInit : AllocSlotInvPres sc pk alignMap st0 st0)
    (hLiveSc : liveSlotsInClass st0 sc ≤ pk.getD sc 0)
    (hPre : FineSameGroupsSlotKind st_ag.groups st0.groups)
    (hwfAg : MallocngWFInflight inflight base brkStart brk_ag liveCost peakCost st_ag)
    (hAct0 : ∀ h : sc < st_ag.ctx.active.length, st_ag.ctx.active[sc]'h = 0#64)
    (hSm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt' = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hGt2048 : 2048 < cnt' * slotStride sc + 16)
    (hOk : RootMmapParamsOk sc cg.cnt (cg.maplen * 4096))
    (hCnt1 : cg.cnt = 1 → 24 ≤ sc)
    (hPageLe : cg.maplen * 4096 ≤ pageAlignUp (cg.cnt * slotStride sc + 16))
    (hGrpMax : cg.maplen * 4096 ≤ Cost.grpMax sc 128)
    (hCgProps : 0 < cg.maplen ∧ cg.sc = sc ∧ cg.nestedCap = 0 ∧
      cg.slots = newGroupSlots cg.lastIdx activeIdx)
    (hGroups' : st'.groups = cg :: st_ag.groups) :
    AllocSlotInvPres sc pk alignMap st0 st' := by
  have hP0 := fineSameGroupsSlotKind_preserves_all (alignMap := alignMap) hPre
  have hGeomAg : ∀ g ∈ st_ag.groups, GroupFineGeom g := hP0.1 hInit.groups_geom
  have hActLen : sc < st_ag.ctx.active.length := by have := hwfAg.ctx_lens.1; omega
  have hLiveAg : liveSlotsInClass st_ag sc ≤ pk.getD sc 0 := by
    rw [hP0.2.2.1 sc]; exact hLiveSc
  have hEdgeAg : ∀ ch < sc, (nestedEdge st_ag ch sc).length ≤ edgeBound pk ch sc := by
    intro ch hch
    rw [hP0.2.2.2.2.1 ch sc]
    exact hInit.edges_le ch (Nat.lt_trans hch hsc) sc hsc
  have hOcc := active_zero_occ_bounds hwfAg hInflight hGeomAg hsc hActLen (hAct0 hActLen) hLiveAg hEdgeAg
  have ⟨hCgGeom, hCgMaxB⟩ := groupFineGeom_of_rootGroup hsc hSm hGt2048 hCgProps.1 hCgProps.2.1
    hOk hCnt1 hPageLe hGrpMax
  have hCgZero := newGroupSlots_fine_zero cg cg.lastIdx activeIdx hCgProps.2.2.2
  have hCgNot63 : (cg.sc == 63) = false := by
    rw [beq_eq_false_iff_ne, hCgProps.2.1]; omega
  have hGroups63Eq : groups63 st' = groups63 st_ag := by
    unfold groups63; rw [hGroups', List.filter_cons, hCgNot63]; rfl
  refine {
    groups_geom := by
      intro g hg; rw [hGroups'] at hg
      rcases List.mem_cons.mp hg with rfl | hTl
      · exact hCgGeom
      · exact hGeomAg g hTl
    user_slots_wf := by
      intro g hg idx hIdx p req eff hSlot; rw [hGroups'] at hg
      rcases List.mem_cons.mp hg with rfl | hTl
      · exact False.elim (hCgZero.2.2.2 idx hIdx p req eff hSlot)
      · exact (hP0.2.1 hInit.user_slots_wf) g hTl idx hIdx p req eff hSlot
    live_eq := by
      intro k; unfold liveSlotsInClass allGroups
      rw [hGroups', List.filter_cons]
      by_cases hk : (cg.sc == k) = true
      · simp only [hk, ↓reduceIte, List.map_cons, List.sum_cons, hCgZero.1, Nat.zero_add]
        exact hP0.2.2.1 k
      · simp only [Bool.not_eq_true] at hk
        simp only [hk, Bool.false_eq_true, ↓reduceIte]
        exact hP0.2.2.1 k
    below_sc_eq := by
      intro k hk
      have hNe : (cg.sc == k) = false := by rw [beq_eq_false_iff_ne, hCgProps.2.1]; omega
      refine ⟨?_, ?_, ?_⟩
      · unfold allGroups; rw [hGroups', List.filter_cons, hNe]; exact hP0.2.2.2.1 k
      · intro q; unfold nestedEdge
        have hF : decide (cg.sc = k ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride q - 4) = false := by
          rw [decide_eq_false_iff_not, hCgProps.2.1]; omega
        rw [hGroups', List.filter_cons]; simp only [hF, Bool.false_eq_true, ↓reduceIte]
        exact hP0.2.2.2.2.1 k q
      · unfold rootBytes
        have hF : decide (cg.sc = k ∧ 0 < cg.maplen) = false := by
          rw [decide_eq_false_iff_not, hCgProps.2.1]; omega
        rw [hGroups', List.filter_cons]; simp only [hF, Bool.false_eq_true, ↓reduceIte]
        exact hP0.2.2.2.2.2.1 k
    groups_le := by
      intro k hk; unfold allGroups; rw [hGroups', List.filter_cons]
      by_cases hEq : k = sc
      · subst hEq
        have hTrue : (cg.sc == k) = true := beq_iff_eq.mpr hCgProps.2.1
        simp only [hTrue, ↓reduceIte, List.length_cons]
        exact hOcc.2.1
      · have hFalse : (cg.sc == k) = false := by rw [beq_eq_false_iff_ne, hCgProps.2.1]; omega
        simp only [hFalse, Bool.false_eq_true, ↓reduceIte]
        change (allGroups st_ag k).length ≤ gBound pk k
        rw [hP0.2.2.2.1 k]; exact hInit.groups_le k hk
    edges_le := by
      intro ch hch pSc hpSc
      unfold nestedEdge
      have hF : decide (cg.sc = ch ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride pSc - 4) = false := by
        rw [decide_eq_false_iff_not]; have := hCgProps.1; omega
      rw [hGroups', List.filter_cons]
      simp only [hF, Bool.false_eq_true, ↓reduceIte]
      change (nestedEdge st_ag ch pSc).length ≤ edgeBound pk ch pSc
      rw [hP0.2.2.2.2.1 ch pSc]; exact hInit.edges_le ch hch pSc hpSc
    roots_le := by
      intro k hk
      unfold rootBytes
      rw [hGroups', List.filter_cons]
      by_cases hEq : k = sc
      · subst hEq
        have hT : decide (cg.sc = k ∧ 0 < cg.maplen) = true :=
          decide_eq_true ⟨hCgProps.2.1, hCgProps.1⟩
        simp only [hT, ↓reduceIte, List.map_cons, List.sum_cons]
        change cg.maplen * 4096 + rootBytes st_ag k ≤ rBound pk k
        rw [Nat.add_comm]
        exact hOcc.2.2.2 (cg.maplen * 4096) hCgMaxB
      · have hF : decide (cg.sc = k ∧ 0 < cg.maplen) = false := by
          rw [decide_eq_false_iff_not, hCgProps.2.1]; omega
        simp only [hF, Bool.false_eq_true, ↓reduceIte]
        change rootBytes st_ag k ≤ rBound pk k
        rw [hP0.2.2.2.2.2.1 k]; exact hInit.roots_le k hk
    large63_eq := by
      unfold large63DeclBytes large63Groups
      rw [hGroups63Eq]
      exact ⟨hP0.2.2.2.2.2.2.1, hP0.2.2.2.2.2.2.2.1⟩
    straddle63_eq := by
      unfold straddle63Bytes straddle63Groups
      rw [hGroups63Eq]
      exact ⟨hP0.2.2.2.2.2.2.2.2.1, hP0.2.2.2.2.2.2.2.2.2⟩
  }

theorem nestedGroup_parent_nodup {st2 st' : MallocngSt} {pg cg : GroupDesc} {pIdx : Nat}
    (hGroups' : st'.groups = cg :: st2.groups.map (fun g =>
      if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested cg.metaPtr) }
      else g))
    (hNodup' : (st'.groups.map GroupDesc.metaPtr).Nodup) :
    (st2.groups.map GroupDesc.metaPtr).Nodup := by
  rw [hGroups', List.map_cons, List.nodup_cons] at hNodup'
  have hMapEq : (st2.groups.map fun g =>
      if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested cg.metaPtr) }
      else g).map GroupDesc.metaPtr = st2.groups.map GroupDesc.metaPtr := by
    rw [List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply]
    cases hEq : g.metaPtr == pg.metaPtr
    · rfl
    · exact (beq_iff_eq.mp hEq).symm
  have hTl := hNodup'.2
  rwa [hMapEq] at hTl

/-- `nestedGroup` case of `AllocSlotFineTrace`: combines `active_zero_occ_bounds` on `st_ag` at
    `sc` with parent `AllocSlotInvPres pSc` (`sc < pSc`) on `st2`. -/
theorem allocSlotInvPres_nestedGroup {inflight sc cnt' pIdx : Nat}
    {base brkStart brk_ag : BitVec 64} {liveCost peakCost : Nat}
    {pk : List Nat} {alignMap : BitVec 64 → Option Nat}
    {st0 st_ag st2 st' : MallocngSt} {pg cg : GroupDesc}
    (hsc : sc < 48) (hInflight : inflight ≤ 4)
    (hInit : AllocSlotInvPres sc pk alignMap st0 st0)
    (hLiveSc : liveSlotsInClass st0 sc ≤ pk.getD sc 0)
    (hPre : FineSameGroupsSlotKind st_ag.groups st0.groups)
    (hwfAg : MallocngWFInflight inflight base brkStart brk_ag liveCost peakCost st_ag)
    (hAct0 : ∀ h : sc < st_ag.ctx.active.length, st_ag.ctx.active[sc]'h = 0#64)
    (hv : ValidNestedCnt sc cnt')
    (hParentPres : AllocSlotInvPres (sizeToClassUnits (cnt' * sizeClass sc)) pk alignMap st_ag st2)
    (hPgMem : pg ∈ st2.groups)
    (hPgSc : pg.sc = sizeToClassUnits (cnt' * sizeClass sc))
    (hpIdx : pIdx < pg.slots.length)
    (hClaimed : pg.slots[pIdx]'hpIdx = .claimed)
    (hCgProps : cg.sc = sc ∧ cg.maplen = 0 ∧
      cg.nestedCap = slotStride pg.sc - 4 ∧ cg.lastIdx = cnt' - 1 ∧
      cg.slots = newGroupSlots (cnt' - 1) (cnt' - 1))
    (hGroups' : st'.groups = cg :: st2.groups.map (fun g =>
      if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested cg.metaPtr) }
      else g))
    (hNodup' : (st'.groups.map GroupDesc.metaPtr).Nodup) :
    AllocSlotInvPres sc pk alignMap st0 st' := by
  let pSc := sizeToClassUnits (cnt' * sizeClass sc)
  have hBnd := validNestedCnt_bounds hsc hv
  have hpScLt48 : pSc < 48 := hBnd.2.1
  have hScLtPsc : sc < pSc := hBnd.2.2.1
  have hMinPos : 0 < minCntEdge sc pSc := hBnd.2.2.2.1
  have hP0 := fineSameGroupsSlotKind_preserves_all (alignMap := alignMap) hPre
  have hGeomAg : ∀ g ∈ st_ag.groups, GroupFineGeom g := hP0.1 hInit.groups_geom
  have hActLen : sc < st_ag.ctx.active.length := by have := hwfAg.ctx_lens.1; omega
  have hLiveAg : liveSlotsInClass st_ag sc ≤ pk.getD sc 0 := by
    rw [hP0.2.2.1 sc]; exact hLiveSc
  have hEdgeAg : ∀ ch < sc, (nestedEdge st_ag ch sc).length ≤ edgeBound pk ch sc := by
    intro ch hch
    rw [hP0.2.2.2.2.1 ch sc]
    exact hInit.edges_le ch (Nat.lt_trans hch hsc) sc hsc
  have hOcc := active_zero_occ_bounds hwfAg hInflight hGeomAg hsc hActLen (hAct0 hActLen) hLiveAg hEdgeAg
  have hNodup2 : (st2.groups.map GroupDesc.metaPtr).Nodup :=
    nestedGroup_parent_nodup hGroups' hNodup'
  have hOldNotUser : ∀ p req eff, pg.slots[pIdx]'hpIdx ≠ .liveUser p req eff := by
    intro _ _ _ hEq; rw [hClaimed] at hEq; cases hEq
  have hNewNotUser : ∀ p req eff, SlotState.liveNested cg.metaPtr ≠ .liveUser p req eff := by
    intro _ _ _ hEq; cases hEq
  have hSet := map_set_nonLiveUser_preserves_all (gs := st2.groups) (g0 := pg)
    (idx := pIdx) (newS := .liveNested cg.metaPtr) (alignMap := alignMap)
    hpIdx hOldNotUser hNewNotUser
  have hPSet := hSet.2 hNodup2 hPgMem
  let gsMid := st2.groups.map fun g =>
    if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested cg.metaPtr) }
    else g
  let stMid : MallocngSt := { emptyMallocngSt 0#64 with groups := gsMid }
  have hCgCapPsc : cg.nestedCap = slotStride pSc - 4 := by
    rw [hCgProps.2.2.1, hPgSc]
  have hCgGeom : GroupFineGeom cg :=
    groupFineGeom_of_nestedGroup hsc hv hCgProps.1 hCgProps.2.1 hCgCapPsc hCgProps.2.2.2.1
  have hCgZero := newGroupSlots_fine_zero cg (cnt' - 1) (cnt' - 1) hCgProps.2.2.2.2
  have hCgNot63 : (cg.sc == 63) = false := by
    rw [beq_eq_false_iff_ne, hCgProps.1]; omega
  have hGroups63Eq : groups63 st' = groups63 stMid := by
    unfold groups63; rw [hGroups', List.filter_cons, hCgNot63]; rfl
  have hSt2_eq : ∀ k,
      liveSlotsInClass { emptyMallocngSt 0#64 with groups := st2.groups } k = liveSlotsInClass st2 k ∧
      allGroups { emptyMallocngSt 0#64 with groups := st2.groups } k = allGroups st2 k ∧
      (∀ q, nestedEdge { emptyMallocngSt 0#64 with groups := st2.groups } k q = nestedEdge st2 k q) ∧
      rootBytes { emptyMallocngSt 0#64 with groups := st2.groups } k = rootBytes st2 k :=
    fun _ => ⟨rfl, rfl, fun _ => rfl, rfl⟩
  have hBelowSc := hParentPres.below_sc_eq sc hScLtPsc
  refine {
    groups_geom := by
      intro g hg; rw [hGroups'] at hg
      rcases List.mem_cons.mp hg with rfl | hTl
      · exact hCgGeom
      · exact (hPSet.1 hParentPres.groups_geom) g hTl
    user_slots_wf := by
      intro g hg idx hIdx p req eff hSlot; rw [hGroups'] at hg
      rcases List.mem_cons.mp hg with rfl | hTl
      · exact False.elim (hCgZero.2.2.2 idx hIdx p req eff hSlot)
      · exact (hPSet.2.1 hParentPres.user_slots_wf) g hTl idx hIdx p req eff hSlot
    live_eq := by
      intro k
      have hMidLive : liveSlotsInClass stMid k = liveSlotsInClass st0 k := by
        rw [hPSet.2.2.1 k, (hSt2_eq k).1, hParentPres.live_eq k, hP0.2.2.1 k]
      unfold liveSlotsInClass allGroups at hMidLive ⊢
      rw [hGroups', List.filter_cons]
      by_cases hk : (cg.sc == k) = true
      · simp only [hk, ↓reduceIte, List.map_cons, List.sum_cons, hCgZero.1, Nat.zero_add]
        exact hMidLive
      · simp only [Bool.not_eq_true] at hk
        simp only [hk, Bool.false_eq_true, ↓reduceIte]
        exact hMidLive
    below_sc_eq := by
      intro k hk
      have hkPsc : k < pSc := Nat.lt_trans hk hScLtPsc
      have hBelowK := hParentPres.below_sc_eq k hkPsc
      have hNe : (cg.sc == k) = false := by rw [beq_eq_false_iff_ne, hCgProps.1]; omega
      refine ⟨?_, ?_, ?_⟩
      · have hMidG : (allGroups stMid k).length = (allGroups st0 k).length := by
          rw [hPSet.2.2.2.1 k, (hSt2_eq k).2.1, hBelowK.1, hP0.2.2.2.1 k]
        unfold allGroups at hMidG ⊢; rw [hGroups', List.filter_cons, hNe]; exact hMidG
      · intro q
        have hMidE : (nestedEdge stMid k q).length = (nestedEdge st0 k q).length := by
          rw [hPSet.2.2.2.2.1 k q, (hSt2_eq k).2.2.1 q, hBelowK.2.1 q, hP0.2.2.2.2.1 k q]
        unfold nestedEdge at hMidE ⊢
        have hF : decide (cg.sc = k ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride q - 4) = false := by
          rw [decide_eq_false_iff_not, hCgProps.1]; omega
        rw [hGroups', List.filter_cons]; simp only [hF, Bool.false_eq_true, ↓reduceIte]; exact hMidE
      · have hMidR : rootBytes stMid k = rootBytes st0 k := by
          rw [hPSet.2.2.2.2.2.1 k, (hSt2_eq k).2.2.2, hBelowK.2.2, hP0.2.2.2.2.2.1 k]
        unfold rootBytes at hMidR ⊢
        have hF : decide (cg.sc = k ∧ 0 < cg.maplen) = false := by
          rw [decide_eq_false_iff_not, hCgProps.1]; omega
        rw [hGroups', List.filter_cons]; simp only [hF, Bool.false_eq_true, ↓reduceIte]; exact hMidR
    groups_le := by
      intro k hk
      by_cases hEq : k = sc
      · subst hEq
        have hMidG : (allGroups stMid k).length = (allGroups st_ag k).length := by
          rw [hPSet.2.2.2.1 k, (hSt2_eq k).2.1, hBelowSc.1]
        have hTrue : (cg.sc == k) = true := beq_iff_eq.mpr hCgProps.1
        unfold allGroups
        rw [hGroups', List.filter_cons]
        simp only [hTrue, ↓reduceIte, List.length_cons]
        change (allGroups stMid k).length + 1 ≤ gBound pk k
        rw [hMidG]
        exact hOcc.2.1
      · have hMidG : (allGroups stMid k).length ≤ gBound pk k := by
          rw [hPSet.2.2.2.1 k, (hSt2_eq k).2.1]; exact hParentPres.groups_le k hk
        unfold allGroups at hMidG ⊢
        rw [hGroups', List.filter_cons]
        have hFalse : (cg.sc == k) = false := by rw [beq_eq_false_iff_ne, hCgProps.1]; omega
        simp only [hFalse, Bool.false_eq_true, ↓reduceIte]
        exact hMidG
    edges_le := by
      intro ch hch q hq
      by_cases hChEq : ch = sc
      · subst hChEq
        have hMidE : (nestedEdge stMid ch q).length = (nestedEdge st_ag ch q).length := by
          rw [hPSet.2.2.2.2.1 ch q, (hSt2_eq ch).2.2.1 q, hBelowSc.2.1 q]
        unfold nestedEdge
        rw [hGroups', List.filter_cons]
        by_cases hCap : cg.nestedCap = slotStride q - 4
        · have hCapEq : slotStride pSc - 4 = slotStride q - 4 := hCgCapPsc.symm.trans hCap
          have hqEq : pSc = q := slotStride_sub4_inj hpScLt48 hq hCapEq
          subst hqEq
          have hT : decide (cg.sc = ch ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride pSc - 4) = true :=
            decide_eq_true ⟨hCgProps.1, hCgProps.2.1, hCap⟩
          simp only [hT, ↓reduceIte, List.length_cons]
          change (nestedEdge stMid ch pSc).length + 1 ≤ edgeBound pk ch pSc
          rw [hMidE]
          exact hOcc.2.2.1 pSc hpScLt48 hMinPos
        · have hF : decide (cg.sc = ch ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride q - 4) = false := by
            rw [decide_eq_false_iff_not]; intro h; exact hCap h.2.2
          simp only [hF, Bool.false_eq_true, ↓reduceIte]
          change (nestedEdge stMid ch q).length ≤ edgeBound pk ch q
          rw [hMidE, hP0.2.2.2.2.1 ch q]; exact hInit.edges_le ch hsc q hq
      · have hMidE : (nestedEdge stMid ch q).length ≤ edgeBound pk ch q := by
          rw [hPSet.2.2.2.2.1 ch q, (hSt2_eq ch).2.2.1 q]; exact hParentPres.edges_le ch hch q hq
        unfold nestedEdge at hMidE ⊢
        have hF : decide (cg.sc = ch ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride q - 4) = false := by
          rw [decide_eq_false_iff_not, hCgProps.1]; omega
        rw [hGroups', List.filter_cons]
        simp only [hF, Bool.false_eq_true, ↓reduceIte]
        exact hMidE
    roots_le := by
      intro k hk
      have hMidR : rootBytes stMid k ≤ rBound pk k := by
        rw [hPSet.2.2.2.2.2.1 k, (hSt2_eq k).2.2.2]; exact hParentPres.roots_le k hk
      unfold rootBytes at hMidR ⊢
      have hF : decide (cg.sc = k ∧ 0 < cg.maplen) = false := by
        rw [decide_eq_false_iff_not, hCgProps.2.1]; omega
      rw [hGroups', List.filter_cons]
      simp only [hF, Bool.false_eq_true, ↓reduceIte]
      exact hMidR
    large63_eq := by
      have h1 : large63DeclBytes stMid alignMap = large63DeclBytes st0 alignMap := by
        rw [hPSet.2.2.2.2.2.2.1]; exact hParentPres.large63_eq.1.trans hP0.2.2.2.2.2.2.1
      have h2 : (large63Groups stMid).length = (large63Groups st0).length := by
        rw [hPSet.2.2.2.2.2.2.2.1]; exact hParentPres.large63_eq.2.trans hP0.2.2.2.2.2.2.2.1
      unfold large63DeclBytes large63Groups at h1 h2 ⊢
      rw [hGroups63Eq]
      exact ⟨h1, h2⟩
    straddle63_eq := by
      have h1 : (straddle63Groups stMid).length = (straddle63Groups st0).length := by
        rw [hPSet.2.2.2.2.2.2.2.2.1]; exact hParentPres.straddle63_eq.1.trans hP0.2.2.2.2.2.2.2.2.1
      have h2 : straddle63Bytes stMid = straddle63Bytes st0 := by
        rw [hPSet.2.2.2.2.2.2.2.2.2]; exact hParentPres.straddle63_eq.2.trans hP0.2.2.2.2.2.2.2.2.2
      unfold straddle63Bytes straddle63Groups at h1 h2 ⊢
      rw [hGroups63Eq]
      exact ⟨h1, h2⟩
  }

end LibsignalBinary.Heap.Fine
