/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers6c

/-!
# Multi-Group Active-List Dequeue Helpers

Pure invariant-transition helpers (`mkActivatedGroup` and `dequeue_multi`) for unlinking a group
from a multi-element `ctx.active[g.sc]` circular doubly linked list and optionally activating the
new head group during `nontrivial_free`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

@[expose] public section

private theorem list_filterMap_congr {α β : Type} {f g : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem nodup_eraseIdx_props {α : Type} {xs : List α} (hNd : xs.Nodup) {k : Nat}
    (hk : k < xs.length) :
    (xs.eraseIdx k).Nodup ∧
    (xs.eraseIdx k).length + 1 = xs.length ∧
    (∀ x, x ∈ xs.eraseIdx k ↔ (x ∈ xs ∧ x ≠ xs[k]'hk)) ∧
    (∀ (i : Nat) (hi : i < (xs.eraseIdx k).length),
      (i < k ∧ ∃ hi0 : i < xs.length, (xs.eraseIdx k)[i]'hi = xs[i]'hi0) ∨
      (k ≤ i ∧ ∃ hi1 : i + 1 < xs.length, (xs.eraseIdx k)[i]'hi = xs[i + 1]'hi1)) := by
  induction xs generalizing k with
  | nil => nomatch hk
  | cons x xs ih =>
    obtain ⟨hxNotIn, hNdXs⟩ := List.nodup_cons.mp hNd
    cases k with
    | zero =>
      refine ⟨hNdXs, by simp, fun y => ?_, fun i hi => Or.inr ⟨Nat.zero_le _, Nat.succ_lt_succ hi, rfl⟩⟩
      simp only [List.eraseIdx_zero, List.getElem_cons_zero, List.mem_cons]
      exact ⟨fun hy => ⟨Or.inr hy, fun hEq => hxNotIn (hEq ▸ hy)⟩,
        fun ⟨hOr, hNe⟩ => hOr.elim (fun hEq => False.elim (hNe hEq)) id⟩
    | succ k =>
      have hk' : k < xs.length := Nat.lt_of_succ_lt_succ hk
      obtain ⟨hNdE, hLenE, hMemE, hIdxE⟩ := ih hNdXs hk'
      have hxNotInE : x ∉ xs.eraseIdx k := fun hxE => hxNotIn ((hMemE x).mp hxE).1
      refine ⟨List.nodup_cons.mpr ⟨hxNotInE, hNdE⟩, by simp [hLenE], fun y => ?_, fun i hi => ?_⟩
      · simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, List.mem_cons, hMemE y]
        constructor
        · rintro (rfl | ⟨hy, hNe⟩)
          · exact ⟨Or.inl rfl, fun hEq => hxNotIn (hEq ▸ List.getElem_mem hk')⟩
          · exact ⟨Or.inr hy, hNe⟩
        · rintro ⟨rfl | hy, hNe⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hy, hNe⟩
      · cases i with
        | zero => exact Or.inl ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, rfl⟩
        | succ i' =>
          have hi' : i' < (xs.eraseIdx k).length := Nat.lt_of_succ_lt_succ hi
          rcases hIdxE i' hi' with ⟨hLt, hi0, hEq⟩ | ⟨hLe, hi1, hEq⟩
          · exact Or.inl ⟨Nat.succ_lt_succ hLt, Nat.succ_lt_succ hi0, hEq⟩
          · exact Or.inr ⟨Nat.succ_le_succ hLe, Nat.succ_lt_succ hi1, hEq⟩

private theorem eraseIdx_filterMap_eq {α β : Type} (xs : List α) (f : α → Option β) (k : Nat)
    (hk : k < xs.length) (hSome : ∀ x ∈ xs, (f x).isSome) :
    (xs.eraseIdx k).filterMap f = (xs.filterMap f).eraseIdx k := by
  induction xs generalizing k with
  | nil => nomatch hk
  | cons x xs ih =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hSome x List.mem_cons_self)
    cases k with
    | zero => simp [hv]
    | succ k =>
      simp only [List.eraseIdx_cons_succ, List.filterMap_cons, hv]
      exact congrArg (v :: ·) (ih k (Nat.lt_of_succ_lt_succ hk)
        fun y hy => hSome y (List.mem_cons_of_mem _ hy))

def mkActivatedGroup (h : GroupDesc) : GroupDesc :=
  let cntMask := (2#32 <<< h.activeIdx) - 1#32
  { h with
    availMask := cntMask &&& h.freedMask
    freedMask := h.freedMask &&& (-(2#32 <<< h.activeIdx))
    slots     := (List.range h.slots.length).map fun j =>
      if hj : j < h.slots.length then
        if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then
          .freeAvail
        else
          h.slots[j]'hj
      else
        .freeInactive }

theorem mkActivatedGroup_props {h : GroupDesc}
    (hActLe : h.activeIdx ≤ h.lastIdx) (hLast : h.lastIdx ≤ 31)
    (hLenCnt : h.slots.length = h.cnt)
    (hAv0 : h.availMask = 0#32) (hFrNe0 : h.freedMask ≠ 0#32)
    (hBound : h.freedMask.toNat < 2 ^ h.cnt)
    (hSlots : ∀ j (hj : j < h.slots.length),
      (h.availMask.getLsbD j = true ↔ h.slots[j]'hj = .freeAvail) ∧
      (h.freedMask.getLsbD j = true ↔ h.slots[j]'hj = .freeInactive) ∧
      (h.activeIdx < j → h.slots[j]'hj = .freeInactive)) :
    let h' := mkActivatedGroup h
    h'.slots.length = h.slots.length ∧
    h'.isEmpty = h.isEmpty ∧
    (h'.slots.filter SlotState.isClaimed).length = (h.slots.filter SlotState.isClaimed).length ∧
    (h'.slots.map slotLiveCount).sum = (h.slots.map slotLiveCount).sum ∧
    (h'.slots.map slotEffCost).sum = (h.slots.map slotEffCost).sum ∧
    ¬ (h'.availMask = 0#32 ∧ h'.freedMask = 0#32) ∧
    h'.availMask &&& h'.freedMask = 0#32 ∧
    (h'.availMask ||| h'.freedMask).toNat < 2 ^ h'.cnt ∧
    (∀ j (hj' : j < h'.slots.length) (hj : j < h.slots.length),
      (h'.availMask.getLsbD j = true ↔ h'.slots[j]'hj' = .freeAvail) ∧
      (h'.freedMask.getLsbD j = true ↔ h'.slots[j]'hj' = .freeInactive) ∧
      (h'.activeIdx < j → h'.slots[j]'hj' = .freeInactive) ∧
      (∀ cm, h'.slots[j]'hj' = .liveNested cm ↔ h.slots[j]'hj = .liveNested cm) ∧
      (∀ p n ec, h'.slots[j]'hj' = .liveUser p n ec ↔ h.slots[j]'hj = .liveUser p n ec)) := by
  dsimp only [mkActivatedGroup]
  obtain ⟨_, hDisj, hOr, hOrBound, hBits⟩ := activateGroup_mask_props hActLe hLast hBound
  have hLen' :
      ((List.range h.slots.length).map fun j =>
        if hj : j < h.slots.length then
          if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj
        else .freeInactive).length = h.slots.length := by simp
  have hGet' : ∀ j (hj : j < h.slots.length),
      ((List.range h.slots.length).map fun j =>
        if hj : j < h.slots.length then
          if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj
        else .freeInactive)[j]'(by simp [hj]) =
        (if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj) := by
    intro j hj
    simp [hj]
  have hMapEq :
      ((List.range h.slots.length).map fun j =>
        if hj : j < h.slots.length then
          if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj
        else .freeInactive) =
      List.ofFn (fun i : Fin h.slots.length =>
        if h.slots[i.val] == .freeInactive && decide (i.val ≤ h.activeIdx) then .freeAvail else h.slots[i.val]) := by
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    have hj : j < h.slots.length := by simpa using hj1
    simp [hj]
  have hIsEmptyEq :
      (GroupDesc.isEmpty
        { h with
          availMask := ((2#32 <<< h.activeIdx) - 1#32) &&& h.freedMask
          freedMask := h.freedMask &&& -(2#32 <<< h.activeIdx)
          slots := (List.range h.slots.length).map fun j =>
            if hj : j < h.slots.length then
              if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj
            else .freeInactive }) = h.isEmpty := by
    unfold GroupDesc.isEmpty
    dsimp only []
    rw [hMapEq]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_iff_getElem, List.length_ofFn, List.getElem_ofFn]
    constructor
    · intro hAll s ⟨i, hi, hEq⟩
      subst hEq
      have hSpec := hAll _ ⟨i, hi, rfl⟩
      split at hSpec
      · rename_i hCond
        have hFi : h.slots[i]'hi = .freeInactive := of_decide_eq_true (Bool.and_eq_true_iff.mp hCond).1
        rw [hFi]; rfl
      · exact hSpec
    · intro hAll s ⟨i, hi, hEq⟩
      subst hEq
      split
      · rfl
      · exact hAll _ ⟨i, hi, rfl⟩
  have hMapValEq : ∀ (f : SlotState → Nat), f .freeAvail = 0 → f .freeInactive = 0 →
      (((List.range h.slots.length).map fun j =>
        if hj : j < h.slots.length then
          if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj
        else .freeInactive).map f) =
      h.slots.map f := by
    intro f hfA hfI
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    have hj : j < h.slots.length := by simpa using hj2
    simp only [List.getElem_map, hGet' j hj]
    split
    · rename_i hCond
      have hFi : h.slots[j]'hj = .freeInactive := of_decide_eq_true (Bool.and_eq_true_iff.mp hCond).1
      rw [hFi, hfA, hfI]
    · rfl
  have hFiltLen : ∀ (xs : List SlotState),
      (xs.filter SlotState.isClaimed).length =
        (xs.map fun s => if s.isClaimed then 1 else 0).sum := by
    intro xs; induction xs with
    | nil => rfl
    | cons s ss ih => cases s <;> simp [List.filter_cons, SlotState.isClaimed, ih] <;> omega
  have hClaimedLen :
      (((List.range h.slots.length).map fun j =>
        if hj : j < h.slots.length then
          if h.slots[j]'hj == .freeInactive && decide (j ≤ h.activeIdx) then .freeAvail else h.slots[j]'hj
        else .freeInactive).filter SlotState.isClaimed).length =
      (h.slots.filter SlotState.isClaimed).length := by
    rw [hFiltLen, hFiltLen]
    exact congrArg List.sum (hMapValEq (fun s => if s.isClaimed then 1 else 0) rfl rfl)
  refine ⟨hLen', hIsEmptyEq, hClaimedLen,
    congrArg List.sum (hMapValEq slotLiveCount rfl rfl),
    congrArg List.sum (hMapValEq slotEffCost rfl rfl),
    fun ⟨hA0, hF0⟩ => ?_, hDisj, hOrBound,
    fun j hj' hj => ?_⟩
  · rw [hA0, hF0] at hOr
    exact hFrNe0 hOr.symm
  · have hj32 : j < 32 := by unfold GroupDesc.cnt at hLenCnt; omega
    obtain ⟨hBitA, hBitF⟩ := hBits j hj32
    obtain ⟨hOrigA, hOrigF, hOrigGt⟩ := hSlots j hj
    have hNotAvailOrig : h.slots[j]'hj ≠ .freeAvail := by
      intro hEq
      have := hOrigA.mpr hEq
      rw [hAv0] at this; simp at this
    have hSlotJ := hGet' j hj
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hBitA, hSlotJ]
      by_cases hLe : j ≤ h.activeIdx
      · simp only [hLe, decide_true, Bool.true_and, hOrigF]
        cases hSj : h.slots[j]'hj <;> simp_all
      · simp only [hLe, decide_false, Bool.false_and, Bool.and_false]
        exact ⟨(fun hB => nomatch hB), fun hEq => False.elim (hNotAvailOrig hEq)⟩
    · rw [hBitF, hSlotJ]
      by_cases hGt : h.activeIdx < j
      · have hNotLe : ¬ j ≤ h.activeIdx := by omega
        simp [hGt, hNotLe, hOrigF]
      · have hLe : j ≤ h.activeIdx := by omega
        simp only [hGt, decide_false, Bool.false_and, hLe, decide_true, Bool.and_true]
        refine ⟨(fun hB => nomatch hB), fun hEq => ?_⟩
        cases hSj : h.slots[j]'hj <;> simp_all
    · intro hGt
      change h.activeIdx < j at hGt
      have hNotLe : ¬ j ≤ h.activeIdx := by omega
      rw [hSlotJ]
      simp [hNotLe, hOrigGt hGt]
    · intro cm; rw [hSlotJ]; split
      · rename_i hC
        have hFi : h.slots[j]'hj = .freeInactive := of_decide_eq_true (Bool.and_eq_true_iff.mp hC).1
        rw [hFi]; simp
      · rfl
    · intro p n ec; rw [hSlotJ]; split
      · rename_i hC
        have hFi : h.slots[j]'hj = .freeInactive := of_decide_eq_true (Bool.and_eq_true_iff.mp hC).1
        rw [hFi]; simp
      · rfl

def mkDequeuedElem (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) : GroupDesc :=
  let hLinked : GroupDesc :=
    { h with
      prev := if h.metaPtr == g.next then g.prev else h.prev
      next := if h.metaPtr == g.prev then g.next else h.next }
  if g.metaPtr == head && h.metaPtr == g.next then
    mkActivatedGroup hLinked
  else
    hLinked

@[scoped simp] theorem mkDequeuedElem_metaPtr (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).metaPtr = h.metaPtr := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_mem (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).mem = h.mem := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_sc (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).sc = h.sc := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_maplen (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).maplen = h.maplen := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_cnt (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).cnt = h.cnt := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_lastIdx (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).lastIdx = h.lastIdx := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_activeByte (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).activeByte = h.activeByte := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_activeIdx (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).activeIdx = h.activeIdx := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_parentMeta (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).parentMeta = h.parentMeta := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_nestedCap (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).nestedCap = h.nestedCap := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_prev (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).prev = if h.metaPtr == g.next then g.prev else h.prev := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

@[scoped simp] theorem mkDequeuedElem_next (g : GroupDesc) (head : BitVec 64) (h : GroupDesc) :
    (mkDequeuedElem g head h).next = if h.metaPtr == g.prev then g.next else h.next := by
  unfold mkDequeuedElem; dsimp only []; split <;> rfl

theorem mkDequeuedElem_eq_self (g : GroupDesc) (head : BitVec 64) (h : GroupDesc)
    (hNeNx : h.metaPtr ≠ g.next) (hNePv : h.metaPtr ≠ g.prev) :
    mkDequeuedElem g head h = h := by
  unfold mkDequeuedElem
  simp [beq_false_of_ne hNeNx, beq_false_of_ne hNePv]

def updateDequeuedMultiGroups (gs : List GroupDesc) (g : GroupDesc) (head : BitVec 64) :
    List GroupDesc :=
  (filterOutGroup gs g.metaPtr).map (mkDequeuedElem g head)

private theorem updateDequeuedMulti_map_eq {α : Type} (gs : List GroupDesc)
    (g : GroupDesc) (head : BitVec 64) (f : GroupDesc → α)
    (hLink : ∀ (h : GroupDesc) (pv nx : BitVec 64), f { h with prev := pv, next := nx } = f h)
    (hAct : ∀ (h : GroupDesc), f (mkActivatedGroup h) = f h) :
    (updateDequeuedMultiGroups gs g head).map f =
      (filterOutGroup gs g.metaPtr).map f := by
  simp only [updateDequeuedMultiGroups, List.map_map]
  apply List.map_congr_left
  intro h _
  dsimp only [Function.comp, mkDequeuedElem]
  split
  · rw [hAct, hLink]
  · exact hLink h _ _

private theorem updateDequeuedMulti_filter_map_eq {α : Type} (gs : List GroupDesc)
    (g : GroupDesc) (head : BitVec 64)
    (p : GroupDesc → Bool) (f : GroupDesc → α)
    (hpL : ∀ (h : GroupDesc) (pv nx : BitVec 64), p { h with prev := pv, next := nx } = p h)
    (hpA : ∀ (h : GroupDesc), p (mkActivatedGroup h) = p h)
    (hfL : ∀ (h : GroupDesc) (pv nx : BitVec 64), f { h with prev := pv, next := nx } = f h)
    (hfA : ∀ (h : GroupDesc), f (mkActivatedGroup h) = f h) :
    ((updateDequeuedMultiGroups gs g head).filter p).map f =
      ((filterOutGroup gs g.metaPtr).filter p).map f := by
  unfold updateDequeuedMultiGroups
  induction (filterOutGroup gs g.metaPtr) with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    have hPx : p (mkDequeuedElem g head x) = p x := by
      unfold mkDequeuedElem; dsimp only []; split
      · rw [hpA, hpL]
      · exact hpL x _ _
    have hFx : f (mkDequeuedElem g head x) = f x := by
      unfold mkDequeuedElem; dsimp only []; split
      · rw [hfA, hfL]
      · exact hfL x _ _
    rw [hPx]
    split
    · rw [List.map_cons, List.map_cons, hFx, ih]
    · exact ih

set_option maxHeartbeats 400000 in
theorem dequeue_multi {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc48 : g.sc < 48)
    (hNxNe0 : g.next ≠ 0#64) (hNxNeSelf : g.next ≠ g.metaPtr) :
    let hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    let hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
    let hListLt : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
    let head := st.ctx.active[g.sc]'hActLt
    let oldUse := st.ctx.usageByClass[g.sc]'hUseLt
    let ms := st.activeLists[g.sc]'hListLt
    g.prev ≠ g.metaPtr ∧
    g.cnt ≤ oldUse.toNat ∧
    (∀ a, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    ∃ prevG ∈ st.groups, ∃ nextG ∈ st.groups, ∃ k : Nat, ∃ hk : k < ms.length,
      ms[k]'hk = g.metaPtr ∧
      prevG.metaPtr = g.prev ∧ prevG.sc = g.sc ∧
      nextG.metaPtr = g.next ∧ nextG.sc = g.sc ∧
      (∀ a, InRegion prevG.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
      (∀ a, InRegion nextG.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
      let prevUpd : GroupDesc := { prevG with next := g.next }
      let nextPre : GroupDesc :=
        { nextG with next := if nextG.metaPtr == g.prev then g.next else nextG.next }
      let nextMid : GroupDesc := { nextPre with prev := g.prev }
      let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
      let bv_a := writeBytesToMap st.byteVal prevG.metaPtr prevUpd.metaBytes
      let bv_b := writeBytesToMap bv_a nextG.metaPtr nextMid.metaBytes
      let bv_c := writeBytesToMap bv_b g.metaPtr gZero.metaBytes
      let bvDeq :=
        if g.metaPtr == head then
          writeBytesToMap bv_c nextG.metaPtr (mkActivatedGroup nextMid).metaBytes
        else
          bv_c
      let active1 := st.ctx.active.set g.sc (if g.metaPtr == head then g.next else head)
      let usage1 := st.ctx.usageByClass.set g.sc (oldUse - BitVec.ofNat 64 g.cnt)
      let actLists1 := st.activeLists.set g.sc (ms.eraseIdx k)
      let gsDeq := updateDequeuedMultiGroups st.groups g head
      readBytesFromMap bv_a g.metaPtr 40 = g.metaBytes ∧
      readBytesFromMap bv_a nextG.metaPtr 40 = nextPre.metaBytes ∧
      readBytesFromMap bv_b g.metaPtr 40 = g.metaBytes ∧
      (g.metaPtr = head →
        nextG.availMask = 0#32 ∧
        nextG.freedMask ≠ 0#32 ∧
        readBytesFromMap bv_c nextG.metaPtr 40 = nextMid.metaBytes ∧
        bv_c (nextG.mem + 8#64) = nextG.activeByte ∧
        OwnedRwByte st (nextG.mem + 8#64) ∧
        (nextG.mem + 8#64) ∈ st.masterDom) ∧
      DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq := by
  dsimp only []
  have hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  have hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
  have hListLt : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
  let head := st.ctx.active[g.sc]'hActLt
  let ms := st.activeLists[g.sc]'hListLt
  have hProps := activeList_head_and_singleton_props hwf hg hSc48
  have hInMs : g.metaPtr ∈ ms := Classical.byContradiction fun hNot => hNxNe0 (hProps.2.1.mpr hNot)
  have hNotSing : ms ≠ [g.metaPtr] := fun hS => hNxNeSelf (hProps.2.2.2.1.mpr hS)
  obtain ⟨k, hk, hMsK⟩ := List.mem_iff_getElem.mp hInMs
  have hGe2Ms : 2 ≤ ms.length := by
    rcases ms with _ | ⟨m0, _ | ⟨m1, tl⟩⟩
    · nomatch hk
    · simp only [List.length_singleton] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact False.elim (hNotSing (by simpa using congrArg (· :: []) hMsK))
    · simp
  have hAct0 := hwf.active_wf g.sc hActLt hListLt
  obtain ⟨hMem0, hDll0, hLen0, hNotMem0, hTail0, hUniq0, hActMem0⟩ := hAct0
  have hMemW : ∀ m ∈ ms, ∃ u ∈ st.groups, u.metaPtr = m := fun m hm =>
    let ⟨u, hu, hM, _⟩ := hMem0 m hm; ⟨u, hu, hM⟩
  let ns := ms.filterMap fun m => (findGroupByMeta st m).map fun u => (u.metaPtr, u.prev, u.next)
  change CircularDllWf head ns at hDll0
  change ns.length = ms.length at hLen0
  have hMapFst : ns.map Prod.fst = ms := activeList_nodes_eq_map hwf.groups_nodup.1 hMemW
  have hkN : k < ns.length := by rw [hLen0]; exact hk
  have hGe2N : 2 ≤ ns.length := by rw [hLen0]; exact hGe2Ms
  obtain ⟨_, gNode, hgNode, hGNodeM, hNsKEq⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW hk
  have _hGNodeEq : gNode = g :=
    mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgNode hg (hGNodeM.trans hMsK)
  subst gNode
  have hNsK : ns[k]'hkN = (g.metaPtr, g.prev, g.next) := hNsKEq
  have hMsNd : ms.Nodup ∧ head = ms[0]'(by omega) ∧ g.prev ∈ ms ∧ g.next ∈ ms ∧
      ∃ prevG ∈ st.groups, ∃ nextG ∈ st.groups,
        prevG.metaPtr = g.prev ∧ prevG.sc = g.sc ∧
        nextG.metaPtr = g.next ∧ nextG.sc = g.sc ∧
        (g.metaPtr = head → k = 0 ∧ nextG.metaPtr = ms[1]'(by omega)) := by
    rcases hNsEq : ns with _ | ⟨⟨p0, pv0, nx0⟩, _ | ⟨⟨p1, pv1, nx1⟩, tlN⟩⟩
    · simp [hNsEq] at hGe2N
    · simp [hNsEq] at hGe2N
    · have hDllU := hDll0; rw [hNsEq] at hDllU
      obtain ⟨hHeadP0, hNdFst, _, hLinks⟩ := hDllU
      have hNdMs : ms.Nodup := by rw [← hMapFst, hNsEq]; exact hNdFst
      have hHeadMs0 : head = ms[0]'(by omega) := by
        have := congrArg (fun l => l[0]?) hMapFst
        rw [hNsEq] at this
        simp only [List.map_cons, List.getElem?_cons_zero] at this
        rw [List.getElem?_eq_getElem (by omega)] at this
        injection this with hP0Eq
        exact hHeadP0.trans hP0Eq
      have hkL : k < ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN).length := by rw [← hNsEq]; exact hkN
      obtain ⟨hCurNx, hCurPv⟩ := hLinks k hkL
      have hCurEq : ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN)[k]'hkL = (g.metaPtr, g.prev, g.next) := by
        simpa [hNsEq] using hNsK
      let kNx := (k + 1) % ms.length
      let kPv := (k + ms.length - 1) % ms.length
      have hkNxLt : kNx < ms.length := Nat.mod_lt _ (by omega)
      have hkPvLt : kPv < ms.length := Nat.mod_lt _ (by omega)
      have hFstAt : ∀ j (hj : j < ms.length) (hjL : j < ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN).length),
          (((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN)[j]'hjL).1 = ms[j]'hj := by
        intro j hj hjL
        have := congrArg (fun l => l[j]?) hMapFst
        rw [hNsEq, List.getElem?_map, List.getElem?_eq_getElem hjL, List.getElem?_eq_getElem hj] at this
        simpa using this
      have hLenEqL : ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN).length = ms.length := by
        rw [← hNsEq]; exact hLen0
      have hGNxMs : g.next = ms[kNx]'hkNxLt := by
        have h1 : g.next = (((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN)[k]'hkL).2.2 := by
          rw [hCurEq]
        rw [h1, hCurNx]
        refine (hFstAt _ (by rw [← hLenEqL]; exact Nat.mod_lt _ (by omega)) _).trans ?_
        have hIdxEq : (k + 1) % ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN).length = kNx := by
          rw [hLenEqL]
        simp only [hIdxEq]
      have hGPvMs : g.prev = ms[kPv]'hkPvLt := by
        have h1 : g.prev = (((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN)[k]'hkL).2.1 := by
          rw [hCurEq]
        rw [h1, hCurPv]
        refine (hFstAt _ (by rw [← hLenEqL]; exact Nat.mod_lt _ (by omega)) _).trans ?_
        have hIdxEq : (k + ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN).length - 1) %
            ((p0, pv0, nx0) :: (p1, pv1, nx1) :: tlN).length = kPv := by
          rw [hLenEqL]
        simp only [hIdxEq]
      obtain ⟨prevG, hPrevG, hPrevM, hPrevSc⟩ := hMem0 (ms[kPv]'hkPvLt) (List.getElem_mem hkPvLt)
      obtain ⟨nextG, hNextG, hNextM, hNextSc⟩ := hMem0 (ms[kNx]'hkNxLt) (List.getElem_mem hkNxLt)
      refine ⟨hNdMs, hHeadMs0, hGPvMs ▸ List.getElem_mem hkPvLt, hGNxMs ▸ List.getElem_mem hkNxLt,
        prevG, hPrevG, nextG, hNextG,
        hPrevM.trans hGPvMs.symm, hPrevSc, hNextM.trans hGNxMs.symm, hNextSc,
        fun hGHd => ?_⟩
      have hk0 : k = 0 := nodup_idx_eq hNdMs hk (by omega) (hMsK.trans (hGHd.trans hHeadMs0))
      subst hk0
      have hkNx1 : kNx = 1 := Nat.mod_eq_of_lt (by omega)
      refine ⟨rfl, hNextM.trans (by simp [hkNx1])⟩
  obtain ⟨hNdMs, _hHeadMs0, hPvInMs, hNxInMs, prevG, hPrevG, nextG, hNextG, hPrevM, hPrevSc, hNextM, hNextSc, hIfHead⟩ := hMsNd
  have hRem := CircularDllWf.removeAt hkN hGe2N hDll0
  dsimp only [] at hRem
  rw [hNsK] at hRem
  obtain ⟨_, hPvNeSelf, _, hDllAfter⟩ := hRem
  obtain ⟨hCntLe, hUseLen, hUseEqRest⟩ := usage_sub_cnt_props hwf hg hSc48
  have hMetaOwnG := (meta_ownedRw_of_mem_groups hwf hg).2.2.2.2
  have hMetaOwnPv := (meta_ownedRw_of_mem_groups hwf hPrevG).2.2.2.2
  have hMetaOwnNx := (meta_ownedRw_of_mem_groups hwf hNextG).2.2.2.2
  have hAllOfMem : ∀ u ∈ st.groups, u.metaPtr ∈ allMetaSlots st := fun u hu =>
    (hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu))))
  have hDisjMeta : ∀ u ∈ st.groups, ∀ v ∈ st.groups, u.metaPtr ≠ v.metaPtr →
      ∀ a, InRegion u.metaPtr 40 a → InRegion v.metaPtr 40 a → False :=
    fun u hu v hv hNe a haU haV =>
      metaSlot_disjoint_of_ne hwf (hAllOfMem u hu) (hAllOfMem v hv) hNe haU haV
  let prevUpd : GroupDesc := { prevG with next := g.next }
  let nextPre : GroupDesc :=
    { nextG with next := if nextG.metaPtr == g.prev then g.next else nextG.next }
  let nextMid : GroupDesc := { nextPre with prev := g.prev }
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let bv_a := writeBytesToMap st.byteVal prevG.metaPtr prevUpd.metaBytes
  let bv_b := writeBytesToMap bv_a nextG.metaPtr nextMid.metaBytes
  let bv_c := writeBytesToMap bv_b g.metaPtr gZero.metaBytes
  let bvDeq :=
    if g.metaPtr == head then
      writeBytesToMap bv_c nextG.metaPtr (mkActivatedGroup nextMid).metaBytes
    else
      bv_c
  have hReadBvA_G : readBytesFromMap bv_a g.metaPtr 40 = g.metaBytes := by
    refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans
      (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact writeBytesToMap_out st.byteVal prevG.metaPtr prevUpd.metaBytes fun haP =>
      hDisjMeta g hg prevG hPrevG (hPrevM ▸ Ne.symm hPvNeSelf) a ha (by simpa using haP)
  have hReadBvA_Nx : readBytesFromMap bv_a nextG.metaPtr 40 = nextPre.metaBytes := by
    by_cases hEqNP : nextG.metaPtr = g.prev
    · have hSameG : prevG = nextG :=
        mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hPrevG hNextG (hPrevM.trans hEqNP.symm)
      dsimp only [bv_a, prevUpd, nextPre]
      rw [hSameG]
      simp only [beq_iff_eq.mpr hEqNP, ↓reduceIte]
      exact readBytesFromMap_writeBytesToMap st.byteVal nextG.metaPtr _ (by simp)
    · dsimp only [nextPre]
      simp only [beq_false_of_ne hEqNP, Bool.false_eq_true, ↓reduceIte]
      refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans
        (hwf.groups_wf nextG hNextG).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact writeBytesToMap_out st.byteVal prevG.metaPtr prevUpd.metaBytes fun haP =>
        hDisjMeta nextG hNextG prevG hPrevG (hPrevM ▸ hEqNP) a ha (by simpa using haP)
  have hReadBvB_G : readBytesFromMap bv_b g.metaPtr 40 = g.metaBytes := by
    refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans hReadBvA_G
    exact writeBytesToMap_out bv_a nextG.metaPtr nextMid.metaBytes fun haN =>
      hDisjMeta g hg nextG hNextG (hNextM ▸ Ne.symm hNxNeSelf) a ha (by simpa using haN)
  have hReadBvC_Nx : readBytesFromMap bv_c nextG.metaPtr 40 = nextMid.metaBytes := by
    refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans
      (readBytesFromMap_writeBytesToMap bv_a nextG.metaPtr nextMid.metaBytes (by simp))
    exact writeBytesToMap_out bv_b g.metaPtr gZero.metaBytes fun haG =>
      hDisjMeta nextG hNextG g hg (hNextM ▸ hNxNeSelf) a ha (by simpa using haG)
  have hOnlyMetasC : ∀ a : BitVec 64, bv_c a ≠ st.byteVal a → ∃ u ∈ st.groups, InRegion u.metaPtr 40 a := by
    intro a hNe
    dsimp only [bv_c, bv_b, bv_a] at hNe
    by_cases haG : InRegion g.metaPtr 40 a
    · exact ⟨g, hg, haG⟩
    · rw [writeBytesToMap_out _ g.metaPtr gZero.metaBytes (by simpa using haG)] at hNe
      by_cases haN : InRegion nextG.metaPtr 40 a
      · exact ⟨nextG, hNextG, haN⟩
      · rw [writeBytesToMap_out _ nextG.metaPtr nextMid.metaBytes (by simpa using haN)] at hNe
        by_cases haP : InRegion prevG.metaPtr 40 a
        · exact ⟨prevG, hPrevG, haP⟩
        · exact False.elim (hNe (writeBytesToMap_out st.byteVal prevG.metaPtr prevUpd.metaBytes (by simpa using haP)))
  have hOnlyMetasDeq : ∀ a : BitVec 64, bvDeq a ≠ st.byteVal a → ∃ u ∈ st.groups, InRegion u.metaPtr 40 a := by
    intro a hNe
    dsimp only [bvDeq] at hNe
    split at hNe
    · by_cases haN : InRegion nextG.metaPtr 40 a
      · exact ⟨nextG, hNextG, haN⟩
      · rw [writeBytesToMap_out bv_c nextG.metaPtr _ (by simpa using haN)] at hNe
        exact hOnlyMetasC a hNe
    · exact hOnlyMetasC a hNe
  have hNextIfHead : g.metaPtr = head →
      nextG.availMask = 0#32 ∧ nextG.freedMask ≠ 0#32 ∧
      readBytesFromMap bv_c nextG.metaPtr 40 = nextMid.metaBytes ∧
      bv_c (nextG.mem + 8#64) = nextG.activeByte ∧
      OwnedRwByte st (nextG.mem + 8#64) ∧ (nextG.mem + 8#64) ∈ st.masterDom := by
    intro hGHd
    obtain ⟨_, hNxMs1⟩ := hIfHead hGHd
    obtain ⟨hAv0N, hFrNe0N⟩ := hTail0 1 (show 1 < ms.length by omega) (by decide) nextG hNextG hNxMs1
    obtain ⟨_, hActByte0, hHdrOwn⟩ := group_header_ownedRw hwf hNextG
    have hNxWf := hwf.groups_wf nextG hNextG
    have hMemBound := hNxWf.2.2.2.2.2.2.1
    have hTotBound := hNxWf.2.2.2.2.2.2.2.1
    obtain ⟨hStr, hCnt1, _⟩ := group_slot_toNat hNxWf
    have hMulGe : nextG.stride ≤ nextG.cnt * nextG.stride :=
      Nat.le_mul_of_pos_left nextG.stride (by omega)
    have hTotGe16 : 16 ≤ nextG.totalBytes := by omega
    have hIn16 : InRegion nextG.mem 16 (nextG.mem + 8#64) := by
      rw [inRegion_iff_toNat (by omega), BitVec.toNat_add_of_lt (by simp; omega)]
      exact ⟨by simp, by simp⟩
    have hInTot : InRegion nextG.mem nextG.totalBytes (nextG.mem + 8#64) := by
      rw [inRegion_iff_toNat (by omega), BitVec.toNat_add_of_lt (by simp; omega)]
      exact ⟨by simp, by simp; omega⟩
    have hBvC_Act : bv_c (nextG.mem + 8#64) = nextG.activeByte :=
      ((groupMetaMod_disjoint hwf hOnlyMetasC).2.2.2.2.2 nextG hNextG).1 _ hInTot |>.trans hActByte0
    exact ⟨hAv0N, hFrNe0N, hReadBvC_Nx, hBvC_Act, (hHdrOwn _ hIn16).1, (hHdrOwn _ hIn16).2⟩
  have hNxWf0 := hwf.groups_wf nextG hNextG
  have hNextActProps : g.metaPtr = head →
      let nm := nextMid
      let na := mkActivatedGroup nm
      na.slots.length = nm.slots.length ∧
      na.isEmpty = nm.isEmpty ∧
      (na.slots.filter SlotState.isClaimed).length = (nm.slots.filter SlotState.isClaimed).length ∧
      (na.slots.map slotLiveCount).sum = (nm.slots.map slotLiveCount).sum ∧
      (na.slots.map slotEffCost).sum = (nm.slots.map slotEffCost).sum ∧
      ¬ (na.availMask = 0#32 ∧ na.freedMask = 0#32) ∧
      na.availMask &&& na.freedMask = 0#32 ∧
      (na.availMask ||| na.freedMask).toNat < 2 ^ na.cnt ∧
      (∀ j (hj' : j < na.slots.length) (hj : j < nm.slots.length),
        (na.availMask.getLsbD j = true ↔ na.slots[j]'hj' = .freeAvail) ∧
        (na.freedMask.getLsbD j = true ↔ na.slots[j]'hj' = .freeInactive) ∧
        (na.activeIdx < j → na.slots[j]'hj' = .freeInactive) ∧
        (∀ cm, na.slots[j]'hj' = .liveNested cm ↔ nm.slots[j]'hj = .liveNested cm) ∧
        (∀ p n ec, na.slots[j]'hj' = .liveUser p n ec ↔ nm.slots[j]'hj = .liveUser p n ec)) := by
    intro hGHd
    obtain ⟨hAv0N, hFrNe0N, _⟩ := hNextIfHead hGHd
    have hBoundN : nextMid.freedMask.toNat < 2 ^ nextMid.cnt := by
      have hOrB := hNxWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      dsimp only [nextMid, nextPre]
      simpa [hAv0N] using hOrB
    exact mkActivatedGroup_props hNxWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hNxWf0.2.1 hNxWf0.2.2.1
      hAv0N hFrNe0N hBoundN fun j hj => by
        have hS := hNxWf0.slot_wf j hj
        exact ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
  have hMkDeqNextAct : g.metaPtr = head → mkDequeuedElem g head nextG = mkActivatedGroup nextMid := by
    intro hGHd
    unfold mkDequeuedElem
    simp only [beq_iff_eq.mpr hGHd, beq_iff_eq.mpr hNextM, Bool.and_self, ↓reduceIte]
    rfl
  have hMkDeqNextNoAct : g.metaPtr ≠ head → mkDequeuedElem g head nextG = nextMid := by
    intro hGHd
    unfold mkDequeuedElem
    simp only [beq_false_of_ne hGHd, Bool.false_and, beq_iff_eq.mpr hNextM, ↓reduceIte]
    rfl
  have hMkDeqNoAct : ∀ h0 : GroupDesc, ¬ (g.metaPtr = head ∧ h0.metaPtr = g.next) →
      mkDequeuedElem g head h0 =
        { h0 with
          prev := if h0.metaPtr == g.next then g.prev else h0.prev
          next := if h0.metaPtr == g.prev then g.next else h0.next } := by
    intro h0 hNot
    unfold mkDequeuedElem; dsimp only []
    split
    · rename_i hC
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hC
      exact False.elim (hNot ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩)
    · rfl
  obtain ⟨hNdRestM, hNdRestMem, hSetRest, hMemRestIff, hSumRest, _, _hFindRest⟩ :=
    filterOutGroup_props hwf.groups_nodup.1 hwf.groups_nodup.2 hg
  let gsDeq := updateDequeuedMultiGroups st.groups g head
  have hMapMetaEq : gsDeq.map (·.metaPtr) = (filterOutGroup st.groups g.metaPtr).map (·.metaPtr) :=
    updateDequeuedMulti_map_eq st.groups g head (·.metaPtr) (fun _ _ _ => rfl) (fun _ => rfl)
  have hMapMemEq : gsDeq.map (·.mem) = (filterOutGroup st.groups g.metaPtr).map (·.mem) :=
    updateDequeuedMulti_map_eq st.groups g head (·.mem) (fun _ _ _ => rfl) (fun _ => rfl)
  have hRootFilterEq :
      (gsDeq.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096)) =
        ((filterOutGroup st.groups g.metaPtr).filter (fun h => decide (0 < h.maplen))).map
          (fun h => (h.mem, h.maplen * 4096)) :=
    updateDequeuedMulti_filter_map_eq st.groups g head
      (fun h => decide (0 < h.maplen)) (fun h => (h.mem, h.maplen * 4096))
      (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
  have hCntFilterEq : ∀ sc : Nat,
      ((gsDeq.filter (·.sc == sc)).map GroupDesc.cnt).sum =
        (((filterOutGroup st.groups g.metaPtr).filter (·.sc == sc)).map GroupDesc.cnt).sum := fun sc =>
    congrArg List.sum (updateDequeuedMulti_filter_map_eq st.groups g head
      (·.sc == sc) GroupDesc.cnt (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl))
  have hPerElemSums : ∀ h0 ∈ filterOutGroup st.groups g.metaPtr,
      let h1 := mkDequeuedElem g head h0
      (h1.slots.filter SlotState.isClaimed).length = (h0.slots.filter SlotState.isClaimed).length ∧
      (h1.slots.map slotLiveCount).sum = (h0.slots.map slotLiveCount).sum ∧
      (h1.slots.map slotEffCost).sum = (h0.slots.map slotEffCost).sum := by
    intro h0 hh0
    dsimp only []
    by_cases hActCase : g.metaPtr = head ∧ h0.metaPtr = g.next
    · have _hEqNx : h0 = nextG :=
        mem_groups_eq_of_metaPtr hwf.groups_nodup.1 ((hMemRestIff h0).mp hh0).1 hNextG (hActCase.2.trans hNextM.symm)
      subst h0
      rw [hMkDeqNextAct hActCase.1]
      have hP := hNextActProps hActCase.1
      exact ⟨hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1⟩
    · rw [hMkDeqNoAct h0 hActCase]
      exact ⟨rfl, rfl, rfl⟩
  have hMapSumEq : ∀ (f : GroupDesc → Nat),
      (∀ h0 ∈ filterOutGroup st.groups g.metaPtr, f (mkDequeuedElem g head h0) = f h0) →
      (gsDeq.map f).sum = ((filterOutGroup st.groups g.metaPtr).map f).sum := by
    intro f hEqF
    congr 1
    dsimp only [gsDeq]
    simp only [updateDequeuedMultiGroups, List.map_map]
    exact List.map_congr_left fun h0 hh0 => hEqF h0 hh0
  refine ⟨hPvNeSelf, hCntLe, hMetaOwnG, prevG, hPrevG, nextG, hNextG, k, hk,
    hMsK, hPrevM, hPrevSc, hNextM, hNextSc, hMetaOwnPv, hMetaOwnNx,
    hReadBvA_G, hReadBvA_Nx, hReadBvB_G, hNextIfHead,
    { lens := ⟨by simp [hwf.ctx_lens.1], hUseLen, by simp [hwf.ctx_lens.2.2.2.2.2]⟩
      nodup := ⟨hMapMetaEq ▸ hNdRestM, hMapMemEq ▸ hNdRestMem⟩
      meta_set := fun x => by rw [hMapMetaEq]; exact hSetRest x
      root_filter_eq := hRootFilterEq
      each_preserved := fun h hh => by
        obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
        obtain ⟨hh0In, h0NeG⟩ := (hMemRestIff h0).mp hh0
        by_cases hActCase : g.metaPtr = head ∧ h0.metaPtr = g.next
        · have _hEqNx : h0 = nextG :=
            mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0In hNextG (hActCase.2.trans hNextM.symm)
          subst h0
          rw [hMkDeqNextAct hActCase.1]
          have hP := hNextActProps hActCase.1
          exact ⟨h0NeG, nextG, hh0In, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            hP.1, hP.2.1, fun hBoth => False.elim (hP.2.2.2.2.2.1 hBoth),
            fun j hj hj0 => ⟨(hP.2.2.2.2.2.2.2.2 j hj hj0).2.2.2.1,
              (hP.2.2.2.2.2.2.2.2 j hj hj0).2.2.2.2⟩⟩
        · rw [hMkDeqNoAct h0 hActCase]
          exact ⟨h0NeG, h0, hh0In, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id,
            fun _ _ _ => ⟨fun _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩⟩
      other_sc_mem := fun h0 hh0 hScNe => by
        have h0NeG : h0.metaPtr ≠ g.metaPtr := fun hEq =>
          hScNe (congrArg GroupDesc.sc (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq))
        have h0NeNx : h0.metaPtr ≠ g.next := fun hEq =>
          hScNe ((congrArg GroupDesc.sc
            (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hNextG (hEq.trans hNextM.symm))).trans hNextSc)
        have h0NePv : h0.metaPtr ≠ g.prev := fun hEq =>
          hScNe ((congrArg GroupDesc.sc
            (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hPrevG (hEq.trans hPrevM.symm))).trans hPrevSc)
        have hh0R : h0 ∈ filterOutGroup st.groups g.metaPtr := (hMemRestIff h0).mpr ⟨hh0, h0NeG⟩
        have hMemMap : mkDequeuedElem g head h0 ∈ gsDeq := List.mem_map_of_mem hh0R
        rw [mkDequeuedElem_eq_self g head h0 h0NeNx h0NePv] at hMemMap
        exact hMemMap
      sum_claimed := by
        rw [hMapSumEq _ fun h0 hh0 => (hPerElemSums h0 hh0).1]
        exact hSumRest _
      sum_live := by
        rw [hMapSumEq _ fun h0 hh0 => (hPerElemSums h0 hh0).2.1]
        exact hSumRest _
      sum_eff := by
        rw [hMapSumEq _ fun h0 hh0 => (hPerElemSums h0 hh0).2.2]
        exact hSumRest _
      usage_eq := fun sc hsc => (hUseEqRest sc hsc).trans (hCntFilterEq sc).symm
      g_zero_bytes := by
        split
        · refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans
            (readBytesFromMap_writeBytesToMap bv_b g.metaPtr gZero.metaBytes (by simp))
          exact writeBytesToMap_out bv_c nextG.metaPtr _ fun haN =>
            hDisjMeta g hg nextG hNextG (hNextM ▸ Ne.symm hNxNeSelf) a ha (by simpa using haN)
        · exact readBytesFromMap_writeBytesToMap bv_b g.metaPtr gZero.metaBytes (by simp)
      only_group_metas := hOnlyMetasDeq
      each_meta_bytes := fun h hh => by
        obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
        obtain ⟨hh0In, h0NeG⟩ := (hMemRestIff h0).mp hh0
        rw [mkDequeuedElem_metaPtr]
        by_cases hH0Nx : h0.metaPtr = g.next
        · have _hEqNx : h0 = nextG :=
            mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0In hNextG (hH0Nx.trans hNextM.symm)
          subst h0
          by_cases hGHd : g.metaPtr = head
          · have hEqB : (g.metaPtr == st.ctx.active[g.sc]'hActLt) = true := beq_iff_eq.mpr hGHd
            rw [hMkDeqNextAct hGHd]
            simp only [hEqB, ↓reduceIte]
            exact readBytesFromMap_writeBytesToMap bv_c nextG.metaPtr _ (by simp)
          · have hNeB : (g.metaPtr == st.ctx.active[g.sc]'hActLt) = false := beq_false_of_ne hGHd
            rw [hMkDeqNextNoAct hGHd]
            simp only [hNeB, Bool.false_eq_true, ↓reduceIte]
            exact hReadBvC_Nx
        · rw [hMkDeqNoAct h0 (fun ⟨_, h2⟩ => hH0Nx h2)]
          have hPvNo : (if h0.metaPtr == g.next then g.prev else h0.prev) = h0.prev := by
            simp [beq_false_of_ne hH0Nx]
          rw [hPvNo]
          have hNotInNx : ∀ a, InRegion h0.metaPtr 40 a → ¬ InRegion nextG.metaPtr 40 a :=
            fun a ha haN => hDisjMeta h0 hh0In nextG hNextG (hNextM ▸ hH0Nx) a ha haN
          have hNotInG : ∀ a, InRegion h0.metaPtr 40 a → ¬ InRegion g.metaPtr 40 a :=
            fun a ha haG => hDisjMeta h0 hh0In g hg h0NeG a ha haG
          have hEqBvA : readBytesFromMap bvDeq h0.metaPtr 40 = readBytesFromMap bv_a h0.metaPtr 40 := by
            apply readBytesFromMap_eq_of_inRegion (by decide)
            intro a ha
            have h1 : bvDeq a = bv_c a := by
              dsimp only [bvDeq]
              split
              · exact writeBytesToMap_out bv_c nextG.metaPtr _ (by simpa using hNotInNx a ha)
              · rfl
            have h2 : bv_c a = bv_b a :=
              writeBytesToMap_out bv_b g.metaPtr gZero.metaBytes (by simpa using hNotInG a ha)
            have h3 : bv_b a = bv_a a :=
              writeBytesToMap_out bv_a nextG.metaPtr nextMid.metaBytes (by simpa using hNotInNx a ha)
            exact h1.trans (h2.trans h3)
          refine hEqBvA.trans ?_
          by_cases hH0Pv : h0.metaPtr = g.prev
          · have _hEqPv : h0 = prevG :=
              mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0In hPrevG (hH0Pv.trans hPrevM.symm)
            subst h0
            simp only [beq_iff_eq.mpr hPrevM, ↓reduceIte]
            exact readBytesFromMap_writeBytesToMap st.byteVal prevG.metaPtr prevUpd.metaBytes (by simp)
          · simp only [beq_false_of_ne hH0Pv, Bool.false_eq_true, ↓reduceIte]
            refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans
              (hwf.groups_wf h0 hh0In).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            exact writeBytesToMap_out st.byteVal prevG.metaPtr prevUpd.metaBytes fun haP =>
              hDisjMeta h0 hh0In prevG hPrevG (hPrevM ▸ hH0Pv) a ha (by simpa using haP)
      each_masks := fun h hh => by
        obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
        obtain ⟨hh0In, _⟩ := (hMemRestIff h0).mp hh0
        have hHWf := hwf.groups_wf h0 hh0In
        by_cases hActCase : g.metaPtr = head ∧ h0.metaPtr = g.next
        · have _hEqNx : h0 = nextG :=
            mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0In hNextG (hActCase.2.trans hNextM.symm)
          subst h0
          rw [hMkDeqNextAct hActCase.1]
          have hP := hNextActProps hActCase.1
          exact ⟨hP.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.1,
            fun h63 => by change nextG.sc = 63 at h63; omega,
            fun j hj =>
              have hj0 : j < nextG.slots.length := hP.1 ▸ hj
              ⟨(hP.2.2.2.2.2.2.2.2 j hj hj0).1,
               (hP.2.2.2.2.2.2.2.2 j hj hj0).2.1,
               (hP.2.2.2.2.2.2.2.2 j hj hj0).2.2.1⟩⟩
        · rw [hMkDeqNoAct h0 hActCase]
          refine ⟨hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun h63 => ?_,
            fun j hj => ?_⟩
          · change h0.sc = 63 at h63
            have h63P := hHWf.2.2.2.1 h63
            have hNeNx : (h0.metaPtr == g.next) = false := beq_false_of_ne fun hEq => by
              have hScEq := congrArg GroupDesc.sc
                (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0In hNextG (hEq.trans hNextM.symm))
              omega
            have hNePv : (h0.metaPtr == g.prev) = false := beq_false_of_ne fun hEq => by
              have hScEq := congrArg GroupDesc.sc
                (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0In hPrevG (hEq.trans hPrevM.symm))
              omega
            simp [hNeNx, hNePv, h63P.2.2.1, h63P.2.2.2]
          · have hS := hHWf.slot_wf j hj
            exact ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1⟩
      active_wf_deq := fun sc h1 h2 => by
        have hScLt48 : sc < 48 := by simp [hwf.ctx_lens.1] at h1; exact h1
        obtain ⟨hNdErase, hLenErase, hMemErase, hIdxErase⟩ := nodup_eraseIdx_props hNdMs hk
        by_cases hEqSc : sc = g.sc
        · subst hEqSc
          simp only [List.getElem_set_self]
          let stDeq : MallocngSt :=
            { st with
              ctx := { st.ctx with
                active := st.ctx.active.set g.sc (if g.metaPtr == head then g.next else head)
                usageByClass := st.ctx.usageByClass.set g.sc
                  ((st.ctx.usageByClass[g.sc]'hUseLt) - BitVec.ofNat 64 g.cnt) }
              groups := gsDeq
              activeLists := st.activeLists.set g.sc (ms.eraseIdx k)
              byteVal := bvDeq }
          have hMapH0 : ∀ h0 ∈ filterOutGroup st.groups g.metaPtr,
              ∃ h ∈ gsDeq, h.metaPtr = h0.metaPtr ∧ h.sc = h0.sc ∧
                h.prev = (if h0.metaPtr == g.next then g.prev else h0.prev) ∧
                h.next = (if h0.metaPtr == g.prev then g.next else h0.next) := fun h0 hh0 =>
            ⟨mkDequeuedElem g head h0, List.mem_map_of_mem hh0,
              mkDequeuedElem_metaPtr g head h0, mkDequeuedElem_sc g head h0,
              mkDequeuedElem_prev g head h0, mkDequeuedElem_next g head h0⟩
          have hNodesDeqEq :
              ((ms.eraseIdx k).filterMap fun m =>
                (findGroupByMeta stDeq m).map fun h => (h.metaPtr, h.prev, h.next)) =
              (ns.eraseIdx k).map fun d =>
                (d.1, if d.1 == g.next then g.prev else d.2.1,
                      if d.1 == g.prev then g.next else d.2.2) := by
            have hSome0 : ∀ m ∈ ms,
                ((findGroupByMeta st m).map fun u => (u.metaPtr, u.prev, u.next)).isSome := by
              intro m hm
              obtain ⟨u, hu, hUM, _⟩ := hMem0 m hm
              unfold findGroupByMeta
              rw [← hUM, findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hu]
              rfl
            have hStep1 :
                (ns.eraseIdx k).map (fun d =>
                  (d.1, if d.1 == g.next then g.prev else d.2.1,
                        if d.1 == g.prev then g.next else d.2.2)) =
                (ms.eraseIdx k).filterMap (fun m =>
                  ((findGroupByMeta st m).map fun u => (u.metaPtr, u.prev, u.next)).map fun d =>
                    (d.1, if d.1 == g.next then g.prev else d.2.1,
                          if d.1 == g.prev then g.next else d.2.2)) := by
              rw [← eraseIdx_filterMap_eq ms _ k hk hSome0, List.map_filterMap]
            rw [hStep1]
            apply list_filterMap_congr
            intro m hmE
            obtain ⟨hmIn, hmNeK⟩ := (hMemErase m).mp hmE
            have hmNeG : m ≠ g.metaPtr := hMsK ▸ hmNeK
            obtain ⟨h0, hh0, rfl, _⟩ := hMem0 m hmIn
            have hh0R : h0 ∈ filterOutGroup st.groups g.metaPtr := (hMemRestIff h0).mpr ⟨hh0, hmNeG⟩
            obtain ⟨h1, hh1, h1M, _, h1Pv, h1Nx⟩ := hMapH0 h0 hh0R
            have hF0 : findGroupByMeta st h0.metaPtr = some h0 :=
              findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hh0
            have hF1 : findGroupByMeta stDeq h0.metaPtr = some h1 := by
              unfold findGroupByMeta; dsimp only [stDeq]; rw [← h1M]
              exact findGroupByMeta_eq_of_mem (hMapMetaEq ▸ hNdRestM) hh1
            rw [hF0, hF1]
            simp [h1M, h1Pv, h1Nx]
          refine ⟨fun m hmE => ?_,
            hNodesDeqEq ▸ hDllAfter,
            by rw [hNodesDeqEq, List.length_map, List.length_eraseIdx_of_lt hkN,
                   List.length_eraseIdx_of_lt hk, hLen0],
            fun h hh hS => ?_,
            fun i hi hiPos h hh hM => ?_,
            fun h1' hh1' h2' hh2' s1 s2 l1 l2 => ?_,
            fun h hh hS hLt => ?_⟩
          · obtain ⟨hmIn, hmNeK⟩ := (hMemErase m).mp hmE
            obtain ⟨h0, hh0, rfl, hS0⟩ := hMem0 m hmIn
            have hh0R : h0 ∈ filterOutGroup st.groups g.metaPtr :=
              (hMemRestIff h0).mpr ⟨hh0, hMsK ▸ hmNeK⟩
            obtain ⟨h1, hh1, h1M, h1Sc, _, _⟩ := hMapH0 h0 hh0R
            exact ⟨h1, hh1, h1M, h1Sc.trans hS0⟩
          · obtain ⟨h0, hh0R, rfl⟩ := List.mem_map.mp hh
            obtain ⟨hh0, h0NeG⟩ := (hMemRestIff h0).mp hh0R
            rw [mkDequeuedElem_sc] at hS
            have hMemIffH0 : h0.metaPtr ∉ ms.eraseIdx k ↔ h0.metaPtr ∉ ms := by
              rw [hMemErase]
              have hNeMk : h0.metaPtr ≠ ms[k]'hk := hMsK ▸ h0NeG
              exact ⟨fun hN hm => hN ⟨hm, hNeMk⟩, fun hN ⟨hm, _⟩ => hN hm⟩
            have h4 := hNotMem0 h0 hh0 hS
            by_cases hH0In : h0.metaPtr ∈ ms
            · simp only [mkDequeuedElem_metaPtr, mkDequeuedElem_prev, mkDequeuedElem_next]
              have hInE : h0.metaPtr ∈ ms.eraseIdx k :=
                (hMemErase h0.metaPtr).mpr ⟨hH0In, hMsK ▸ h0NeG⟩
              have hPvNe0_or_NxNe0 :
                  ¬ ((if h0.metaPtr == g.next then g.prev else h0.prev) = 0#64 ∧
                     (if h0.metaPtr == g.prev then g.next else h0.next) = 0#64) := by
                obtain ⟨iE, hiE, hMsEi⟩ := List.mem_iff_getElem.mp hInE
                have hiErNs : iE < (ns.eraseIdx k).length := by
                  rw [List.length_eraseIdx_of_lt hkN, hLen0, ← List.length_eraseIdx_of_lt hk]
                  exact hiE
                have hiN' : iE < ((ns.eraseIdx k).map fun d =>
                    (d.1, if d.1 == g.next then g.prev else d.2.1,
                          if d.1 == g.prev then g.next else d.2.2)).length := by
                  rw [List.length_map]; exact hiErNs
                rcases hRemList : ((ns.eraseIdx k).map fun d =>
                    (d.1, if d.1 == g.next then g.prev else d.2.1,
                          if d.1 == g.prev then g.next else d.2.2)) with _ | ⟨r0, rTl⟩
                · rw [hRemList] at hiN'; nomatch hiN'
                · have hDllR := hDllAfter; rw [hRemList] at hDllR
                  obtain ⟨_, _, hNonNullR, hLinksR⟩ := hDllR
                  have hiR : iE < (r0 :: rTl).length := by rw [← hRemList]; exact hiN'
                  have hNxtR := (hLinksR iE hiR).1
                  have hNxtNonNull := hNonNullR ((r0 :: rTl)[(iE + 1) % (r0 :: rTl).length]'(Nat.mod_lt _ (by omega)))
                    (List.getElem_mem _)
                  have hNodeEqAt : (r0 :: rTl)[iE]'hiR =
                      (h0.metaPtr,
                       if h0.metaPtr == g.next then g.prev else h0.prev,
                       if h0.metaPtr == g.prev then g.next else h0.next) := by
                    apply Option.some.inj
                    rw [← List.getElem?_eq_getElem hiR, ← hRemList, List.getElem?_map,
                        List.getElem?_eq_getElem hiErNs]
                    rcases hIdxErase iE hiE with ⟨hLtK, hi0, hEi0⟩ | ⟨hLeK, hi1, hEi1⟩
                    · obtain ⟨_, u0, hu0, hUM0, hNs0⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW hi0
                      have _hUEq : u0 = h0 := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu0 hh0
                        (hUM0.trans (hEi0.symm.trans hMsEi))
                      subst u0
                      rw [List.getElem_eraseIdx_of_lt _ hLtK, hNs0]; rfl
                    · obtain ⟨_, u1, hu1, hUM1, hNs1⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW hi1
                      have _hUEq : u1 = h0 := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu1 hh0
                        (hUM1.trans (hEi1.symm.trans hMsEi))
                      subst u1
                      rw [List.getElem_eraseIdx_of_ge _ hLeK, hNs1]; rfl
                  intro ⟨_, hNxZero⟩
                  rw [hNodeEqAt] at hNxtR
                  dsimp only [] at hNxtR
                  exact hNxtNonNull (hNxtR.symm.trans hNxZero)
              exact ⟨⟨fun hN => False.elim (hN hInE), fun hZ => False.elim (hPvNe0_or_NxNe0 hZ)⟩,
                fun hN => False.elim (hN hInE)⟩
            · have hNeNx : h0.metaPtr ≠ g.next := fun hEq => hH0In (hEq ▸ hNxInMs)
              have hNePv : h0.metaPtr ≠ g.prev := fun hEq => hH0In (hEq ▸ hPvInMs)
              rw [mkDequeuedElem_eq_self g head h0 hNeNx hNePv]
              exact ⟨⟨fun _ => h4.1.mp hH0In, fun hZ => hMemIffH0.mpr (h4.1.mpr hZ)⟩,
                fun _ => h4.2 hH0In⟩
          ·
            obtain ⟨h0, hh0R, rfl⟩ := List.mem_map.mp hh
            obtain ⟨hh0, _⟩ := (hMemRestIff h0).mp hh0R
            rw [mkDequeuedElem_metaPtr] at hM
            by_cases hGHd : g.metaPtr = head
            · obtain ⟨hk0, hNxMs1⟩ := hIfHead hGHd
              subst hk0
              have hi1 : i + 1 < ms.length := by
                have hi' : i < (ms.eraseIdx 0).length := hi
                rw [List.length_eraseIdx_of_lt hk] at hi'
                omega
              have hEiEq : (ms.eraseIdx 0)[i]'hi = ms[i + 1]'hi1 := by
                rcases hIdxErase i hi with ⟨hLt0, _⟩ | ⟨_, _, hEq⟩
                · omega
                · exact hEq
              have hNeNx : h0.metaPtr ≠ g.next := fun hEq => by
                have hIdxEq := nodup_idx_eq hNdMs hi1 (by omega)
                  (hEiEq.symm.trans (hM.symm.trans (hEq.trans (hNextM.symm.trans hNxMs1))))
                omega
              rw [hMkDeqNoAct h0 (fun ⟨_, h2⟩ => hNeNx h2)]
              exact hTail0 (i + 1) hi1 (by omega) h0 hh0 (hM.trans hEiEq)
            · rw [hMkDeqNoAct h0 (fun ⟨h1, _⟩ => hGHd h1)]
              rcases hIdxErase i hi with ⟨_, hi0, hEi0⟩ | ⟨_, hi1, hEi1⟩
              · exact hTail0 i hi0 hiPos h0 hh0 (hM.trans hEi0)
              · exact hTail0 (i + 1) hi1 (by omega) h0 hh0 (hM.trans hEi1)
          ·
            obtain ⟨a1, ha1R, rfl⟩ := List.mem_map.mp hh1'
            obtain ⟨a2, ha2R, rfl⟩ := List.mem_map.mp hh2'
            rw [mkDequeuedElem_sc] at s1 s2
            rw [mkDequeuedElem_activeIdx, mkDequeuedElem_lastIdx] at l1 l2
            rw [mkDequeuedElem_metaPtr, mkDequeuedElem_metaPtr]
            exact hUniq0 a1 ((hMemRestIff a1).mp ha1R).1 a2 ((hMemRestIff a2).mp ha2R).1 s1 s2 l1 l2
          ·
            obtain ⟨h0, hh0R, rfl⟩ := List.mem_map.mp hh
            obtain ⟨hh0, h0NeG⟩ := (hMemRestIff h0).mp hh0R
            rw [mkDequeuedElem_sc] at hS
            rw [mkDequeuedElem_activeIdx, mkDequeuedElem_lastIdx] at hLt
            rw [mkDequeuedElem_metaPtr]
            obtain ⟨hIn0, hPos0⟩ := hActMem0 h0 hh0 hS hLt
            exact ⟨(hMemErase h0.metaPtr).mpr ⟨hIn0, hMsK ▸ h0NeG⟩, hPos0⟩
        ·
          simp only [List.getElem_set, Ne.symm hEqSc, ↓reduceIte]
          exact activeClassWf_other_sc hwf hScLt48 (hMapMetaEq ▸ hNdRestM) fun h => by
            constructor
            · rintro ⟨hh, hScH⟩
              obtain ⟨h0, hh0R, rfl⟩ := List.mem_map.mp hh
              obtain ⟨hh0, _⟩ := (hMemRestIff h0).mp hh0R
              rw [mkDequeuedElem_sc] at hScH
              have hNeNx : h0.metaPtr ≠ g.next := fun hEq =>
                hEqSc (hScH.symm.trans ((congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hNextG (hEq.trans hNextM.symm))).trans hNextSc))
              have hNePv : h0.metaPtr ≠ g.prev := fun hEq =>
                hEqSc (hScH.symm.trans ((congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hPrevG (hEq.trans hPrevM.symm))).trans hPrevSc))
              rw [mkDequeuedElem_eq_self g head h0 hNeNx hNePv]
              exact ⟨hh0, hScH⟩
            · rintro ⟨hh, hScH⟩
              have hNeG : h.metaPtr ≠ g.metaPtr := fun hEq =>
                hEqSc (hScH.symm.trans (congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq)))
              have hNeNx : h.metaPtr ≠ g.next := fun hEq =>
                hEqSc (hScH.symm.trans ((congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hNextG (hEq.trans hNextM.symm))).trans hNextSc))
              have hNePv : h.metaPtr ≠ g.prev := fun hEq =>
                hEqSc (hScH.symm.trans ((congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hPrevG (hEq.trans hPrevM.symm))).trans hPrevSc))
              have hhR : h ∈ filterOutGroup st.groups g.metaPtr := (hMemRestIff h).mpr ⟨hh, hNeG⟩
              have hMemMap : mkDequeuedElem g head h ∈ gsDeq := List.mem_map_of_mem hhR
              rw [mkDequeuedElem_eq_self g head h hNeNx hNePv] at hMemMap
              exact ⟨hMemMap, hScH⟩
      empty_act_singleton := fun h hh hEmp => by
        have hLift : ∀ u ∈ gsDeq, u.isEmpty = true →
            ∃ u0 ∈ st.groups, u.metaPtr = u0.metaPtr ∧ u.sc = u0.sc ∧
              u0.metaPtr ≠ g.metaPtr ∧ u0.isEmpty = true := by
          intro u hu huEmp
          obtain ⟨u0, hu0R, rfl⟩ := List.mem_map.mp hu
          obtain ⟨hu0, hNeG⟩ := (hMemRestIff u0).mp hu0R
          refine ⟨u0, hu0, mkDequeuedElem_metaPtr g head u0, mkDequeuedElem_sc g head u0, hNeG, ?_⟩
          by_cases hActCase : g.metaPtr = head ∧ u0.metaPtr = g.next
          · have _hEqNx : u0 = nextG :=
              mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu0 hNextG (hActCase.2.trans hNextM.symm)
            subst u0
            rw [hMkDeqNextAct hActCase.1] at huEmp
            exact (hNextActProps hActCase.1).2.1.symm.trans huEmp
          · rw [hMkDeqNoAct u0 hActCase] at huEmp
            exact huEmp
        obtain ⟨h0, hh0, hM0, hSc0, hNeG0, hEmp0⟩ := hLift h hh hEmp
        have hB := hwf.empty_groups_bound h0 hh0 hEmp0
        refine ⟨fun hLt => ?_, fun h' hh' hEmp' hSc' => ?_⟩
        · have hLt0 : h0.sc < st.activeLists.length := by
            rw [hSc0, List.length_set] at hLt; exact hLt
          have hIn0 := hB.2.2.2.2.1 hLt0
          by_cases hScEq : h0.sc = g.sc
          · have hInMs : h0.metaPtr ∈ ms := by dsimp only [ms]; simpa [hScEq] using hIn0
            have hInEr : h0.metaPtr ∈ ms.eraseIdx k :=
              ((nodup_eraseIdx_props hNdMs hk).2.2.1 h0.metaPtr).mpr ⟨hInMs, hMsK ▸ hNeG0⟩
            simp only [hM0, hSc0, hScEq, List.getElem_set_self]
            exact hInEr
          · simp only [hM0, hSc0, List.getElem_set, Ne.symm hScEq, ↓reduceIte]
            exact hIn0
        · obtain ⟨h0', hh0', hM0', hSc0', _, hEmp0'⟩ := hLift h' hh' hEmp'
          exact hM0'.trans ((hB.2.2.2.2.2.1 h0' hh0' hEmp0' (hSc0'.symm.trans (hSc'.trans hSc0))).trans hM0.symm) }⟩

end

end LibsignalBinary.Heap.Fine.VendorFree
