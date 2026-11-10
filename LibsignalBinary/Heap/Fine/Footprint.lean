/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.Init
public import VerifiedLibraries.Mallocng.Proofs.Accounting

/-!
# Fine-Grained Footprint and Occupancy Bounds

Bounds global group counts, `meta_area` page counts, per-class slot occupancy when
`ctx.active[sc] = 0#64` (`active_zero_occ_bounds`), and total `dynamicRootRegions` / `masterDom`
bytes under `MallocngFineInv`, discharging `MallocngCostModelSound.heap_footprint_bound`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Group-Count and `meta_area` Page-Count Bounds -/

private theorem filter_lt_sum_eq_sum_range {α : Type} (key : α → Nat) (w : α → Nat) :
    ∀ (k : Nat) (xs : List α),
      ((xs.filter fun x => decide (key x < k)).map w).sum =
        ((List.range k).map fun sc => ((xs.filter fun x => key x == sc).map w).sum).sum
  | 0, [] => rfl
  | 0, _ :: rest => filter_lt_sum_eq_sum_range key w 0 rest
  | k + 1, xs => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [← filter_lt_sum_eq_sum_range key w k xs]
    induction xs with
    | nil => simp
    | cons x rest ih =>
      simp only [List.filter_cons]
      by_cases h1 : key x < k
      · have h2 : key x < k + 1 := by omega
        have h3 : (key x == k) = false := beq_eq_false_iff_ne.mpr (by omega)
        simp [h1, h2, h3, ih, Nat.add_assoc]
      · by_cases hEq : key x = k
        · have h2 : key x < k + 1 := by omega
          have h3 : (key x == k) = true := beq_iff_eq.mpr hEq
          simp [h1, h2, h3, ih]
          omega
        · have h2 : ¬ (key x < k + 1) := by omega
          have h3 : (key x == k) = false := beq_eq_false_iff_ne.mpr hEq
          simp [h1, h2, h3, ih]

private theorem sum_ones_eq_len {α : Type} :
    ∀ (xs : List α), (xs.map fun _ => 1).sum = xs.length
  | [] => rfl
  | _ :: rest => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_ones_eq_len rest]
    omega

private theorem filter_lt_length_eq_sum_range {α : Type} (key : α → Nat) (k : Nat) (xs : List α) :
    (xs.filter fun x => decide (key x < k)).length =
      ((List.range k).map fun sc => (xs.filter fun x => key x == sc).length).sum := by
  rw [← sum_ones_eq_len, filter_lt_sum_eq_sum_range key (fun _ => 1) k xs]
  congr 1
  refine List.map_congr_left fun sc _ => ?_
  exact sum_ones_eq_len _

/-- Exact partition of `st.groups` with `g.sc < 48` into `allGroups st sc` for `0 ≤ sc < 48`. -/
theorem filter_lt48_length_eq_sum_allGroups (st : MallocngSt) :
    (st.groups.filter fun g => decide (g.sc < 48)).length =
      ((List.range 48).map fun sc => (allGroups st sc).length).sum :=
  filter_lt_length_eq_sum_range GroupDesc.sc 48 st.groups

/-- Global group-count bound under `MallocngFineInv`: `st.groups.length ≤ fineMaxGroups b`. -/
theorem groups_fine_length_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {b : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hFine : MallocngFineInv inflight b ivs alignMap st) :
    st.groups.length ≤ fineMaxGroups b := by
  have hPart63 := accounting_length_filter_partition (·.sc == 63) st.groups
  have hNot63Eq :
      (st.groups.filter fun g => !(g.sc == 63)) =
        (st.groups.filter fun g => decide (g.sc < 48)) := by
    refine List.filter_congr fun g hg => ?_
    rcases (hwf.groups_wf g hg).1 with hLt48 | hEq63
    · have hNe : (g.sc == 63) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp [hNe, hLt48]
    · simp [hEq63]
  have hPartLarge := accounting_length_filter_partition isLarge63Group (groups63 st)
  have hLargeLe : (large63Groups st).length ≤ finePeak63Count b := by
    unfold finePeak63Count
    have hEq := hFine.live63_eq.2
    omega
  obtain ⟨pk, pkStraddleCnt, _pkStraddleBytes, _hPkLen, _hLiveLe, hAllLe, _hEdgeLe, _hRootLe,
    hStrCntLe, _hStrBytesLe, hCumG, _hCumB⟩ := hFine.small_witness
  have hLt48Le :
      (st.groups.filter fun g => decide (g.sc < 48)).length ≤
        ((List.range 48).map (gBound pk)).sum := by
    rw [filter_lt48_length_eq_sum_allGroups]
    exact accounting_sum_map_le fun sc hsc => hAllLe sc (List.mem_range.mp hsc)
  have hSmallTotal := sum_gBound_le pk hCumG
  unfold groups63 at hPartLarge
  unfold large63Groups groups63 at hLargeLe
  unfold straddle63Groups groups63 at hStrCntLe
  rw [hNot63Eq] at hPart63
  unfold fineMaxGroups
  generalize gBaseConst = gb at hSmallTotal ⊢
  generalize (b.cumSmallGroupsS + FineScale - 1) / FineScale = q at hSmallTotal ⊢
  generalize finePeak63Count b = p63c at hLargeLe ⊢
  omega

private theorem nodup_map_of_inj_on {α β : Type} {f : α → β} {xs : List α}
    (hnd : xs.Nodup) (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [List.nodup_cons, List.map_cons] at hnd ⊢
    refine ⟨?_, ih hnd.2 (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
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

/-- Budget-independent `meta_area` activation bound from `st.groups.length ≤ maxGroups`:
    when `freeMetas = []` and `bumpMetas = []` at `inflight ≤ 7`,
    `st.metaAreas.length + 1 ≤ 1 + (7 + maxGroups) / 101`. -/
theorem metaAreas_succ_le_of_groups_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost maxGroups : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hGs : st.groups.length ≤ maxGroups)
    (hInflight : inflight ≤ 7)
    (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) :
    st.metaAreas.length + 1 ≤ 1 + (7 + maxGroups) / 101 := by
  let usedAndFree :=
    st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
  have ⟨_hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
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
  have hInflightBound := hwf.inflight_wf
  have hUfLen : usedAndFree.length = st.groups.length + st.reservedMetas.length := by
    simp [usedAndFree, hNoFree, hNoBump]
  omega

/-- `meta_area` activation bound under `MallocngFineInv`:
    when `freeMetas = []` and `bumpMetas = []` at `inflight ≤ 7`,
    `st.metaAreas.length + 1 ≤ fineMaxMetaAreas b`. -/
theorem metaAreas_fine_succ_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {b : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hFine : MallocngFineInv inflight b ivs alignMap st)
    (hInflight : inflight ≤ 7)
    (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) :
    st.metaAreas.length + 1 ≤ fineMaxMetaAreas b :=
  metaAreas_succ_le_of_groups_le hwf (groups_fine_length_le hwf hFine) hInflight hNoFree hNoBump

/-! ## Ring-Empty Occupancy and Group-Creation Bounds -/

private def checkTag6Inj : Bool :=
  (List.range 32).all fun i =>
    (List.range 32).all fun j =>
      if BitVec.ofNat 8 ((6 <<< 5) ||| i) == BitVec.ofNat 8 ((6 <<< 5) ||| j) then decide (i = j)
      else true

private theorem checkTag6Inj_true : checkTag6Inj = true := by
  decide

private theorem tag6_inj {i j : Nat} (hi : i < 32) (hj : j < 32)
    (hEq : BitVec.ofNat 8 ((6 <<< 5) ||| i) = BitVec.ofNat 8 ((6 <<< 5) ||| j)) :
    i = j := by
  have hRow := List.all_eq_true.mp checkTag6Inj_true i (List.mem_range.mpr hi)
  have hCell := List.all_eq_true.mp hRow j (List.mem_range.mpr hj)
  have hBeq : (BitVec.ofNat 8 ((6 <<< 5) ||| i) == BitVec.ofNat 8 ((6 <<< 5) ||| j)) = true :=
    beq_iff_eq.mpr hEq
  simp only [hBeq, ↓reduceIte, decide_eq_true_eq] at hCell
  exact hCell

private def slotNestedOpt : SlotState → Option (BitVec 64)
  | .liveNested cm => some cm
  | _ => none

private def groupNestedPtrs (g : GroupDesc) : List (BitVec 64) :=
  g.slots.filterMap slotNestedOpt

private theorem groupNestedPtrs_length (g : GroupDesc) :
    (groupNestedPtrs g).length = groupNestedCount g := by
  unfold groupNestedPtrs groupNestedCount
  induction g.slots with
  | nil => rfl
  | cons s rest ih =>
    cases s <;> simp [List.filterMap_cons, slotNestedOpt, ih]

private theorem filterMap_range_slots :
    ∀ (slots : List SlotState),
      ((List.range slots.length).filterMap fun idx =>
        match slots[idx]? with
        | some s => slotNestedOpt s
        | none => none) = slots.filterMap slotNestedOpt
  | [] => rfl
  | s :: rest => by
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons]
    have hHead : (match (s :: rest)[0]? with | some x => slotNestedOpt x | none => none) =
        slotNestedOpt s := rfl
    rw [hHead, List.filterMap_map]
    have hTail :
        (List.filterMap
          ((fun idx => match (s :: rest)[idx]? with | some x => slotNestedOpt x | none => none) ∘
            Nat.succ)
          (List.range rest.length)) =
        ((List.range rest.length).filterMap fun idx =>
          match rest[idx]? with | some x => slotNestedOpt x | none => none) := by
      congr 1
    rw [hTail, filterMap_range_slots rest, List.filterMap_cons]

private theorem groupNestedPtrs_mem_iff (g : GroupDesc) (cm : BitVec 64) :
    cm ∈ groupNestedPtrs g ↔
      ∃ idx : Nat, ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveNested cm := by
  unfold groupNestedPtrs
  constructor
  · intro hMem
    obtain ⟨s, hsMem, hsEq⟩ := List.mem_filterMap.mp hMem
    obtain ⟨idx, hIdx, hGet⟩ := List.getElem_of_mem hsMem
    cases s <;> simp [slotNestedOpt] at hsEq
    subst hsEq
    exact ⟨idx, hIdx, hGet⟩
  · rintro ⟨idx, hIdx, hGet⟩
    exact List.mem_filterMap.mpr ⟨.liveNested cm, hGet ▸ List.getElem_mem hIdx, rfl⟩

private theorem filterMap_nodup_of_inj {α β : Type} {f : α → Option β} {xs : List α}
    (hnd : xs.Nodup)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, ∀ b : β, f x = some b → f y = some b → x = y) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [List.nodup_cons] at hnd
    rw [List.filterMap_cons]
    have hTail := ih hnd.2 (fun a ha c hc b hb1 hb2 =>
      hinj a (List.mem_cons_of_mem x ha) c (List.mem_cons_of_mem x hc) b hb1 hb2)
    cases hfx : f x with
    | none => exact hTail
    | some b =>
      refine List.nodup_cons.mpr ⟨?_, hTail⟩
      intro hMem
      obtain ⟨y, hyRest, hfy⟩ := List.mem_filterMap.mp hMem
      have hxy := hinj y (List.mem_cons_of_mem x hyRest) x List.mem_cons_self b hfy hfx
      exact hnd.1 (hxy ▸ hyRest)

private theorem groupNestedPtrs_nodup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    (groupNestedPtrs g).Nodup := by
  unfold groupNestedPtrs
  rw [← filterMap_range_slots g.slots]
  refine filterMap_nodup_of_inj List.nodup_range ?_
  intro idx1 h1 idx2 h2 cm hOpt1 hOpt2
  have hIdx1 : idx1 < g.slots.length := List.mem_range.mp h1
  have hIdx2 : idx2 < g.slots.length := List.mem_range.mp h2
  simp only [List.getElem?_eq_getElem hIdx1] at hOpt1
  simp only [List.getElem?_eq_getElem hIdx2] at hOpt2
  have hS1 : g.slots[idx1]'hIdx1 = .liveNested cm := by
    generalize g.slots[idx1]'hIdx1 = s1 at hOpt1
    cases s1 <;> simp [slotNestedOpt] at hOpt1
    exact congrArg SlotState.liveNested hOpt1
  have hS2 : g.slots[idx2]'hIdx2 = .liveNested cm := by
    generalize g.slots[idx2]'hIdx2 = s2 at hOpt2
    cases s2 <;> simp [slotNestedOpt] at hOpt2
    exact congrArg SlotState.liveNested hOpt2
  have hgWf := hwf.groups_wf g hg
  have hLast : g.lastIdx ≤ 31 := hgWf.2.1
  have hSlotsCnt : g.slots.length = g.cnt := hgWf.2.2.1
  have hSWf1 := hgWf.slot_wf idx1 hIdx1
  have hSWf2 := hgWf.slot_wf idx2 hIdx2
  rw [hS1] at hSWf1
  rw [hS2] at hSWf2
  obtain ⟨cg1, hcg1, hcm1, _, _, _, _, _, _, _, hTag1, _⟩ := hSWf1.2.2.2.2.2
  obtain ⟨cg2, hcg2, hcm2, _, _, _, _, _, _, _, hTag2, _⟩ := hSWf2.2.2.2.2.2
  have hCgEq : cg1 = cg2 :=
    mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg1 hcg2 (hcm1.trans hcm2.symm)
  subst hCgEq
  exact tag6_inj (by unfold GroupDesc.cnt at hSlotsCnt; omega)
    (by unfold GroupDesc.cnt at hSlotsCnt; omega) (hTag1.symm.trans hTag2)

private theorem flatMap_groupNestedPtrs_nodup {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (gs : List GroupDesc)
    (hSub : ∀ g ∈ gs, g ∈ st.groups)
    (hNd : (gs.map (·.metaPtr)).Nodup) :
    (gs.flatMap groupNestedPtrs).Nodup := by
  induction gs with
  | nil => exact List.nodup_nil
  | cons g rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd
    rw [List.flatMap_cons]
    have hgIn := hSub g List.mem_cons_self
    have hRestSub : ∀ g' ∈ rest, g' ∈ st.groups :=
      fun g' hg' => hSub g' (List.mem_cons_of_mem g hg')
    refine List.nodup_append.mpr
      ⟨groupNestedPtrs_nodup hwf hgIn, ih hRestSub hNd.2, fun cm1 h1 cm2 h2 hEq => ?_⟩
    subst hEq
    obtain ⟨idx1, hIdx1, hS1⟩ := (groupNestedPtrs_mem_iff g cm1).mp h1
    obtain ⟨g2, hg2Rest, h2'⟩ := List.mem_flatMap.mp h2
    obtain ⟨idx2, hIdx2, hS2⟩ := (groupNestedPtrs_mem_iff g2 cm1).mp h2'
    have hg2In := hRestSub g2 hg2Rest
    have hSWf1 := (hwf.groups_wf g hgIn).slot_wf idx1 hIdx1
    have hSWf2 := (hwf.groups_wf g2 hg2In).slot_wf idx2 hIdx2
    rw [hS1] at hSWf1
    rw [hS2] at hSWf2
    obtain ⟨cg1, hcg1, hcm1, hPar1, _⟩ := hSWf1.2.2.2.2.2
    obtain ⟨cg2, hcg2, hcm2, hPar2, _⟩ := hSWf2.2.2.2.2.2
    have hCgEq : cg1 = cg2 :=
      mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg1 hcg2 (hcm1.trans hcm2.symm)
    subst hCgEq
    have hMetaEq : g.metaPtr = g2.metaPtr := Option.some.inj (hPar1.symm.trans hPar2)
    exact hNd.1 (hMetaEq ▸ List.mem_map_of_mem hg2Rest)

private theorem flatMap_groupNestedPtrs_length :
    ∀ (gs : List GroupDesc),
      (gs.flatMap groupNestedPtrs).length = (gs.map groupNestedCount).sum
  | [] => rfl
  | g :: rest => by
    simp only [List.flatMap_cons, List.length_append, groupNestedPtrs_length, List.map_cons,
      List.sum_cons, flatMap_groupNestedPtrs_length rest]

private theorem slots_no_free_count_eq :
    ∀ (slots : List SlotState),
      (∀ s ∈ slots, s ≠ .freeAvail ∧ s ≠ .freeInactive) →
      (slots.filter fun s => match s with | .liveUser _ _ _ => true | _ => false).length +
        (slots.filter SlotState.isClaimed).length +
        (slots.filter fun s => match s with | .liveNested _ => true | _ => false).length =
        slots.length
  | [], _ => rfl
  | s :: rest, hNoFree => by
    have hHead := hNoFree s List.mem_cons_self
    have hTail := slots_no_free_count_eq rest (fun x hx => hNoFree x (List.mem_cons_of_mem s hx))
    cases s with
    | freeAvail => exact False.elim (hHead.1 rfl)
    | freeInactive => exact False.elim (hHead.2 rfl)
    | claimed =>
      simp only [List.filter_cons, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      omega
    | liveNested _ =>
      simp only [List.filter_cons, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      omega
    | liveUser _ _ _ =>
      simp only [List.filter_cons, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      omega

private theorem sum_filter_le_sum {α : Type} (p : α → Bool) (w : α → Nat) :
    ∀ (xs : List α), ((xs.filter p).map w).sum ≤ (xs.map w).sum
  | [] => Nat.le_refl 0
  | x :: rest => by
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    have ih := sum_filter_le_sum p w rest
    cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons] <;> omega

private theorem sum_const_mul_le {α : Type} (c : Nat) (w : α → Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, c ≤ w x) → c * xs.length ≤ (xs.map w).sum
  | [], _ => by simp
  | x :: rest, hGe => by
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 := hGe x List.mem_cons_self
    have h2 := sum_const_mul_le c w rest (fun y hy => hGe y (List.mem_cons_of_mem x hy))
    rw [Nat.mul_succ]
    omega

private theorem sum_mul_const {α : Type} (c : Nat) (w : α → Nat) :
    ∀ (xs : List α), (xs.map fun x => c * w x).sum = c * (xs.map w).sum
  | [] => by simp
  | x :: rest => by
    simp only [List.map_cons, List.sum_cons, sum_mul_const c w rest, Nat.mul_add]

/-- Core recurrence lemma for `__malloc_alloc_group(sc)` (`sc < 48`, `inflight ≤ 4`):
    whenever `st.ctx.active[sc] = 0#64` (so no group in `sc` has any `.freeAvail` or
    `.freeInactive` slot), total slots in `sc` are bounded by `occPreBound pk sc`, giving `+1`
    headroom in `gBound pk sc`, `edgeBound pk sc pSc`, and `rBound pk sc`. -/
theorem active_zero_occ_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {sc : Nat} {pk : List Nat}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 4)
    (hGroupsGeom : ∀ g ∈ st.groups, GroupFineGeom g)
    (hsc : sc < 48)
    (hActLen : sc < st.ctx.active.length)
    (hActZero : st.ctx.active[sc]'hActLen = 0#64)
    (hLiveLe : liveSlotsInClass st sc ≤ pk.getD sc 0)
    (hEdgeLe : ∀ ch < sc, (nestedEdge st ch sc).length ≤ edgeBound pk ch sc) :
    ((allGroups st sc).map GroupDesc.cnt).sum ≤ occPreBound pk sc ∧
    (allGroups st sc).length + 1 ≤ gBound pk sc ∧
    (∀ pSc < 48, 0 < minCntEdge sc pSc →
      (nestedEdge st sc pSc).length + 1 ≤ edgeBound pk sc pSc) ∧
    (∀ newBytes : Nat, newBytes ≤ maxRootBytes sc →
      rootBytes st sc + newBytes ≤ rBound pk sc) := by
  have hActListsLen : sc < st.activeLists.length := by
    have := hwf.ctx_lens.2.2.2.2.2; omega
  have hActWf := hwf.active_wf sc hActLen hActListsLen
  have hMsEmpty : st.activeLists[sc]'hActListsLen = [] := by
    have hDll := hActWf.2.1
    have hNodesLen := hActWf.2.2.1
    rw [hActZero] at hDll
    generalize
      ((st.activeLists[sc]'hActListsLen).filterMap fun m =>
        (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)) = nodes at hDll hNodesLen
    cases nodes with
    | nil =>
      exact List.eq_nil_of_length_eq_zero hNodesLen.symm
    | cons hd tl =>
      rcases hd with ⟨p0, pv0, nx0⟩
      have hHeadEq : (0#64 : BitVec 64) = p0 := hDll.1
      have hNe0 : p0 ≠ 0#64 := hDll.2.2.1 (p0, pv0, nx0) List.mem_cons_self
      exact False.elim (hNe0 hHeadEq.symm)
  have hGroupFull : ∀ g ∈ allGroups st sc,
      g.cnt = groupLiveUserCount g + groupClaimedCount g + groupNestedCount g := by
    intro g hgAll
    obtain ⟨hgIn, hScBeq⟩ := List.mem_filter.mp hgAll
    have hgSc : g.sc = sc := beq_iff_eq.mp hScBeq
    have hNotMemMs : g.metaPtr ∉ st.activeLists[sc]'hActListsLen := by simp [hMsEmpty]
    have ⟨hAvail0, hFreed0, _⟩ := (hActWf.2.2.2.1 g hgIn hgSc).2 hNotMemMs
    have hgWf := hwf.groups_wf g hgIn
    have hSlotsCnt : g.slots.length = g.cnt := hgWf.2.2.1
    rw [← hSlotsCnt]
    refine (slots_no_free_count_eq g.slots ?_).symm
    intro s hsMem
    obtain ⟨idx, hIdx, rfl⟩ := List.getElem_of_mem hsMem
    have hSWf := hgWf.slot_wf idx hIdx
    refine ⟨fun hAv => ?_, fun hFr => ?_⟩
    · have hBit := hSWf.2.1.mpr hAv
      rw [hAvail0] at hBit
      simp at hBit
    · have hBit := hSWf.2.2.1.mpr hFr
      rw [hFreed0] at hBit
      simp at hBit
  have hCntSplit :
      ((allGroups st sc).map GroupDesc.cnt).sum =
        liveSlotsInClass st sc +
        ((allGroups st sc).map groupClaimedCount).sum +
        ((allGroups st sc).map groupNestedCount).sum := by
    unfold liveSlotsInClass
    have hMapEq :
        (allGroups st sc).map GroupDesc.cnt =
          (allGroups st sc).map
            (fun g => groupLiveUserCount g + groupClaimedCount g + groupNestedCount g) :=
      List.map_congr_left hGroupFull
    rw [hMapEq]
    clear hMapEq hGroupFull
    induction allGroups st sc with
    | nil => rfl
    | cons g rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega
  have hClaimedLe : ((allGroups st sc).map groupClaimedCount).sum ≤ 4 := by
    have h1 : ((allGroups st sc).map groupClaimedCount).sum ≤ totalClaimedSlots st := by
      unfold allGroups totalClaimedSlots groupClaimedCount
      exact sum_filter_le_sum (·.sc == sc) (fun g => (g.slots.filter SlotState.isClaimed).length) st.groups
    have h2 := hwf.inflight_wf
    omega
  let childAll :=
    st.groups.filter fun cg => decide (cg.sc < sc ∧ cg.maplen = 0 ∧ cg.nestedCap = slotStride sc - 4)
  have hSubNested :
      ∀ cm ∈ (allGroups st sc).flatMap groupNestedPtrs, cm ∈ childAll.map (·.metaPtr) := by
    intro cm hMem
    obtain ⟨g, hgAll, hCmG⟩ := List.mem_flatMap.mp hMem
    obtain ⟨hgIn, hScBeq⟩ := List.mem_filter.mp hgAll
    have hgSc : g.sc = sc := beq_iff_eq.mp hScBeq
    obtain ⟨idx, hIdx, hSlot⟩ := (groupNestedPtrs_mem_iff g cm).mp hCmG
    have hSWf := (hwf.groups_wf g hgIn).slot_wf idx hIdx
    rw [hSlot] at hSWf
    obtain ⟨cg, hcgIn, hCgMeta, hCgPar, _, _, _, hCgCap, _⟩ := hSWf.2.2.2.2.2
    have hcgWf := hwf.groups_wf cg hcgIn
    have hCgMap0 : cg.maplen = 0 := by
      by_cases hPos : 0 < cg.maplen
      · have hNone := hcgWf.2.2.2.2.2.2.2.2.2.2.1.mp hPos
        rw [hCgPar] at hNone
        cases hNone
      · omega
    obtain ⟨_, pg, hpgIn, _, _, hParPg, _, hCgLtPg, _⟩ :=
      hcgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hCgMap0
    have hPgEq : g = pg :=
      mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgIn hpgIn
        (Option.some.inj (hCgPar.symm.trans hParPg))
    subst hPgEq
    have hCgInChild : cg ∈ childAll := by
      refine List.mem_filter.mpr ⟨hcgIn, decide_eq_true ?_⟩
      exact ⟨by omega, hCgMap0, by rw [← hgSc]; exact hCgCap⟩
    exact hCgMeta ▸ List.mem_map_of_mem hCgInChild
  have hAllNd : ((allGroups st sc).map (·.metaPtr)).Nodup :=
    nodup_filter_metaPtr _ hwf.groups_nodup.1
  have hNestedPtrsNd : ((allGroups st sc).flatMap groupNestedPtrs).Nodup :=
    flatMap_groupNestedPtrs_nodup hwf (allGroups st sc)
      (fun g hg => (List.mem_filter.mp hg).1) hAllNd
  have hNestedSumLeChild :
      ((allGroups st sc).map groupNestedCount).sum ≤ childAll.length := by
    rw [← flatMap_groupNestedPtrs_length]
    have hLe := nodup_length_le_of_subset hNestedPtrsNd hSubNested
    simpa only [List.length_map] using hLe
  have hChildSplit :
      childAll.length = ((List.range sc).map fun ch => (nestedEdge st ch sc).length).sum := by
    let baseChild :=
      st.groups.filter fun cg => decide (cg.maplen = 0 ∧ cg.nestedCap = slotStride sc - 4)
    have hEq1 : childAll = baseChild.filter (fun cg => decide (cg.sc < sc)) := by
      dsimp only [childAll, baseChild]
      rw [List.filter_filter]
      refine List.filter_congr fun cg _ => ?_
      by_cases h1 : cg.sc < sc <;> by_cases h2 : cg.maplen = 0 <;>
        by_cases h3 : cg.nestedCap = slotStride sc - 4 <;> simp [h1, h2, h3]
    rw [hEq1, filter_lt_length_eq_sum_range GroupDesc.sc sc baseChild]
    congr 1
    refine List.map_congr_left fun ch _ => ?_
    dsimp only [baseChild]
    unfold nestedEdge
    rw [List.filter_filter]
    congr 1
    refine List.filter_congr fun cg _ => ?_
    by_cases h1 : cg.sc = ch <;> by_cases h2 : cg.maplen = 0 <;>
      by_cases h3 : cg.nestedCap = slotStride sc - 4 <;> simp [h1, h2, h3]
  have hChildLeEdges :
      ((List.range sc).map fun ch => (nestedEdge st ch sc).length).sum ≤
        ((List.range sc).map fun ch => edgeBound pk ch sc).sum :=
    accounting_sum_map_le fun ch hch => hEdgeLe ch (List.mem_range.mp hch)
  have hOccBound : ((allGroups st sc).map GroupDesc.cnt).sum ≤ occPreBound pk sc := by
    rw [occPreBound_eq pk sc]
    omega
  have hGroupBound : (allGroups st sc).length + 1 ≤ gBound pk sc := by
    have hCntPos : 0 < cntMin sc := cntMin_pos hsc
    have hMul : cntMin sc * (allGroups st sc).length ≤ occPreBound pk sc := by
      refine Nat.le_trans (sum_const_mul_le (cntMin sc) GroupDesc.cnt (allGroups st sc) ?_) hOccBound
      intro g hg
      obtain ⟨hgIn, hScBeq⟩ := List.mem_filter.mp hg
      have hgSc : g.sc = sc := beq_iff_eq.mp hScBeq
      simpa only [hgSc] using (hGroupsGeom g hgIn).1 (hgSc ▸ hsc)
    have hDiv : (allGroups st sc).length ≤ occPreBound pk sc / cntMin sc :=
      (Nat.le_div_iff_mul_le hCntPos).mpr (by rw [Nat.mul_comm]; exact hMul)
    unfold gBound
    omega
  have hEdgeNext : ∀ pSc < 48, 0 < minCntEdge sc pSc →
      (nestedEdge st sc pSc).length + 1 ≤ edgeBound pk sc pSc := by
    intro pSc hpSc hMinPos
    have hSubAll :
        ((nestedEdge st sc pSc).map GroupDesc.cnt).sum ≤ ((allGroups st sc).map GroupDesc.cnt).sum := by
      have hEqEdge :
          nestedEdge st sc pSc =
            (allGroups st sc).filter (fun g => decide (g.maplen = 0 ∧ g.nestedCap = slotStride pSc - 4)) := by
        unfold nestedEdge allGroups
        rw [List.filter_filter]
        refine List.filter_congr fun g _ => ?_
        by_cases h1 : g.sc = sc <;> by_cases h2 : g.maplen = 0 <;>
          by_cases h3 : g.nestedCap = slotStride pSc - 4 <;> simp [h1, h2, h3]
      rw [hEqEdge]
      exact sum_filter_le_sum _ GroupDesc.cnt (allGroups st sc)
    have hMul : minCntEdge sc pSc * (nestedEdge st sc pSc).length ≤ occPreBound pk sc := by
      refine Nat.le_trans (sum_const_mul_le (minCntEdge sc pSc) GroupDesc.cnt (nestedEdge st sc pSc) ?_)
        (Nat.le_trans hSubAll hOccBound)
      intro g hg
      obtain ⟨hgIn, hPredB⟩ := List.mem_filter.mp hg
      obtain ⟨hgSc, hml0, hCap⟩ := of_decide_eq_true hPredB
      have hGeom := (hGroupsGeom g hgIn).2.2 (hgSc ▸ hsc) hml0 pSc hpSc hCap
      simpa only [hgSc] using hGeom.2
    have hDiv : (nestedEdge st sc pSc).length ≤ occPreBound pk sc / minCntEdge sc pSc :=
      (Nat.le_div_iff_mul_le hMinPos).mpr (by rw [Nat.mul_comm]; exact hMul)
    unfold edgeBound
    simp only [hMinPos, ↓reduceIte]
    omega
  have hRootNext : ∀ newBytes : Nat, newBytes ≤ maxRootBytes sc →
      rootBytes st sc + newBytes ≤ rBound pk sc := by
    intro newBytes hNewLe
    let rootSc := st.groups.filter fun g => decide (g.sc = sc ∧ 0 < g.maplen)
    have hEachRoot : ∀ g ∈ rootSc, g.maplen * 4096 ≤ ceilRootPerSlot sc * g.cnt := by
      intro g hg
      obtain ⟨hgIn, hPredB⟩ := List.mem_filter.mp hg
      obtain ⟨hgSc, hmlPos⟩ := of_decide_eq_true hPredB
      have hGeom := (hGroupsGeom g hgIn).2.1 (hgSc ▸ hsc) hmlPos
      simpa only [hgSc] using hGeom.2.2.1
    have hRootLeSc :
        rootBytes st sc ≤ ((rootSc.map fun g => ceilRootPerSlot sc * g.cnt)).sum := by
      unfold rootBytes
      exact accounting_sum_map_le hEachRoot
    have hRootScFilter :
        rootSc = (allGroups st sc).filter (fun g => decide (0 < g.maplen)) := by
      dsimp only [rootSc]
      unfold allGroups
      rw [List.filter_filter]
      refine List.filter_congr fun g _ => ?_
      by_cases h1 : g.sc = sc <;> by_cases h2 : 0 < g.maplen <;> simp [h1, h2]
    have hSumCeil :
        (rootSc.map fun g => ceilRootPerSlot sc * g.cnt).sum ≤
          ceilRootPerSlot sc * occPreBound pk sc := by
      rw [hRootScFilter, sum_mul_const]
      refine Nat.mul_le_mul_left (ceilRootPerSlot sc) ?_
      exact Nat.le_trans (sum_filter_le_sum _ GroupDesc.cnt (allGroups st sc)) hOccBound
    unfold rBound
    omega
  exact ⟨hOccBound, hGroupBound, hEdgeNext, hRootNext⟩

/-! ## `dynamicRootRegions` and `masterDom` Footprint Bounds -/

/-- Tight `3×` page-count bound: `metaAreas + guardPages + availMetaPages ≤ 3 * metaAreas + 2`. -/
theorem meta_guard_avail_pages_le_three_mul {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    st.metaAreas.length + st.guardPages.length + st.availMetaPages.length ≤
      3 * st.metaAreas.length + 2 := by
  have ⟨_hMetaLe, hShift0, hShiftPos⟩ := hwf.meta_pages_bound
  by_cases hZero : st.ctx.metaAllocShift = 0#64
  · have ⟨hAvNil, hGdLe⟩ := hShift0 hZero
    have hAvLen : st.availMetaPages.length = 0 := by simp [hAvNil]
    omega
  · have hPos : 1 ≤ st.ctx.metaAllocShift.toNat := by
      have : st.ctx.metaAllocShift.toNat ≠ 0 := fun h => hZero (BitVec.eq_of_toNat_eq h)
      omega
    have ⟨hmLe40, hPowLeMeta, _hSumLe, hGdLe, hAvLe⟩ :=
      hShiftPos st.ctx.metaAllocShift.toNat hPos rfl
    have hShift := meta_guard_avail_shift_bound hPos hmLe40
    omega

private theorem sum_snd_const {α : Type} (f : α → BitVec 64) (c : Nat) (xs : List α) :
    ((xs.map fun x => (f x, c)).map Prod.snd).sum = c * xs.length := by
  induction xs with
  | nil => simp
  | cons _ rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.mul_succ, Nat.add_comm]

private theorem dynamicRootRegions_fit48_inflight {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ iv ∈ dynamicRootRegions st, iv.1.toNat + iv.2 ≤ 2 ^ 48 := by
  intro iv hr
  unfold dynamicRootRegions at hr
  simp only [List.mem_append, List.mem_map, List.mem_filter] at hr
  rcases hr with (((⟨ma, hma, rfl⟩ | ⟨gp, hgp, rfl⟩) | ⟨ap, hap, rfl⟩) | ⟨g, ⟨hg, hPosB⟩, rfl⟩)
  · exact (hwf.metaAreas_wf.2.1 ma hma).2.2.1
  · exact (hwf.guard_avail_wf.2.1 gp hgp).2.2
  · exact (hwf.guard_avail_wf.2.2.2 ap hap).2.2.1
  · have hPos : 0 < g.maplen := of_decide_eq_true hPosB
    have hTot := (hwf.groups_wf g hg).2.2.2.2.2.2.1
    simp only [GroupDesc.totalBytes, hPos, ↓reduceIte] at hTot
    exact hTot

private theorem footprint_combine_arith
    (base pages maxMeta rootLt48 linWt strB cumSB largeB peak63 : Nat)
    (hPages : pages ≤ 3 * maxMeta + 2)
    (hRootLt : rootLt48 ≤ base + linWt)
    (hSmall : linWt + strB ≤ cumSB)
    (hLarge : largeB ≤ peak63) :
    4096 * pages + ((largeB + strB) + rootLt48) ≤
      base + cumSB + peak63 + 4096 * (3 * maxMeta + 2) := by
  omega

/-- Derived `dynamicRootRegions` interval-count, byte-sum, and 48-bit fit bounds under
    `MallocngFineInv`. -/
theorem dynamicRootRegions_fine_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {b : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hFine : MallocngFineInv inflight b ivs alignMap st) :
    (dynamicRootRegions st).length ≤ fineMaxDynIvs b ∧
    ((dynamicRootRegions st).map Prod.snd).sum ≤ fineFootprint b ∧
    (∀ iv ∈ dynamicRootRegions st, iv.1.toNat + iv.2 ≤ 2 ^ 48) := by
  let rootGs := st.groups.filter (fun g => decide (0 < g.maplen))
  have hDynLen :
      (dynamicRootRegions st).length =
        (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length) +
        rootGs.length := by
    unfold dynamicRootRegions
    dsimp only [rootGs]
    simp only [List.length_append, List.length_map]
  have hDynSum :
      ((dynamicRootRegions st).map Prod.snd).sum =
        4096 * (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length) +
        (rootGs.map fun g => g.maplen * 4096).sum := by
    unfold dynamicRootRegions
    simp only [List.map_append, List.sum_append, sum_snd_const]
    have hRootMap :
        ((rootGs.map fun g => (g.mem, g.maplen * 4096)).map Prod.snd) =
          (rootGs.map fun g => g.maplen * 4096) := by
      rw [List.map_map]; rfl
    rw [hRootMap]
    omega
  have hPages3 := meta_guard_avail_pages_le_three_mul hwf
  have hMetaLe := hFine.metaAreas_le
  have hPagesLeMax :
      st.metaAreas.length + st.guardPages.length + st.availMetaPages.length ≤
        3 * fineMaxMetaAreas b + 2 := by
    omega
  have hGsLe := groups_fine_length_le hwf hFine
  have hRootGsLenLe : rootGs.length ≤ fineMaxGroups b :=
    Nat.le_trans (List.length_filter_le _ _) hGsLe
  have hLenBound : (dynamicRootRegions st).length ≤ fineMaxDynIvs b := by
    unfold fineMaxDynIvs
    omega
  have hPartRoot :=
    accounting_sum_filter_partition (·.sc == 63) (fun g => g.maplen * 4096) rootGs
  have hRoot63Eq : rootGs.filter (·.sc == 63) = groups63 st := by
    dsimp only [rootGs]
    unfold groups63
    rw [List.filter_filter]
    refine List.filter_congr fun g hg => ?_
    by_cases h63 : g.sc = 63
    · have hPos : 0 < g.maplen := ((hwf.groups_wf g hg).2.2.2.1 h63).2.1
      simp [h63, hPos]
    · have hBeqF : (g.sc == 63) = false := beq_eq_false_iff_ne.mpr h63
      simp [hBeqF]
  have hRootLt48Eq :
      rootGs.filter (fun g => !(g.sc == 63)) =
        rootGs.filter (fun g => decide (g.sc < 48)) := by
    refine List.filter_congr fun g hg => ?_
    have hgIn := (List.mem_filter.mp hg).1
    rcases (hwf.groups_wf g hgIn).1 with hLt48 | hEq63
    · have hNe : (g.sc == 63) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp [hNe, hLt48]
    · simp [hEq63]
  have hPart63 :=
    accounting_sum_filter_partition isLarge63Group (fun g => g.maplen * 4096) (groups63 st)
  have hLargeBytesLe :
      ((large63Groups st).map fun g => g.maplen * 4096).sum ≤ finePeak63Bytes b := by
    have hEachLarge : ∀ g ∈ large63Groups st,
        g.maplen * 4096 ≤ (g.slots.map (slotDecl63 alignMap)).sum := by
      intro g hgL
      obtain ⟨hg63, hIsLB⟩ := List.mem_filter.mp hgL
      obtain ⟨hgIn, hScBeq⟩ := List.mem_filter.mp hg63
      have hgSc63 : g.sc = 63 := beq_iff_eq.mp hScBeq
      have hgWf := hwf.groups_wf g hgIn
      have hLast0 : g.lastIdx = 0 := (hgWf.2.2.2.1 hgSc63).1
      have hLen1 : g.slots.length = 1 := by
        have hCnt := hgWf.2.2.1
        unfold GroupDesc.cnt at hCnt
        omega
      cases hSlots : g.slots with
      | nil => simp [hSlots] at hLen1
      | cons s0 rest =>
        cases rest with
        | cons _ _ => simp [hSlots] at hLen1
        | nil =>
          unfold isLarge63Group at hIsLB
          rw [hSlots] at hIsLB
          simp only [List.any_cons, List.any_nil, Bool.or_false] at hIsLB
          cases s0 with
          | freeAvail | freeInactive | claimed | liveNested _ =>
            simp [slotIs63Large] at hIsLB
          | liveUser p req eff =>
            have hGeTh : Guaranteed63Threshold ≤ req :=
              of_decide_eq_true (by simpa [slotIs63Large] using hIsLB)
            have hSlot0 : g.slots[0]'(by simp [hSlots]) = .liveUser p req eff := by
              simp [hSlots]
            obtain ⟨al, hAlSome, hMapLe⟩ :=
              hFine.alignMap_wf.2 g hgIn 0 (by simp [hSlots]) p req eff hSlot0
            have hDeclLe := (hMapLe hgSc63).2
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, slotDecl63,
              hGeTh, ↓reduceIte, hAlSome, Option.getD_some, Nat.add_zero]
            exact hDeclLe
    have hSumLe :
        ((large63Groups st).map fun g => g.maplen * 4096).sum ≤ large63DeclBytes st alignMap :=
      accounting_sum_map_le hEachLarge
    have hEqLive := hFine.live63_eq.1
    unfold finePeak63Bytes
    omega
  obtain ⟨pk, _pkStraddleCnt, pkStraddleBytes, _hPkLen, _hLiveLe, _hAllLe, _hEdgeLe, hRootLe,
    _hStrCntLe, hStrBytesLe, _hCumG, hCumB⟩ := hFine.small_witness
  have hLt48SumEq :
      ((rootGs.filter fun g => decide (g.sc < 48)).map fun g => g.maplen * 4096).sum =
        ((List.range 48).map (rootBytes st)).sum := by
    rw [filter_lt_sum_eq_sum_range GroupDesc.sc (fun g => g.maplen * 4096) 48 rootGs]
    congr 1
    refine List.map_congr_left fun sc _ => ?_
    dsimp only [rootGs]
    unfold rootBytes
    rw [List.filter_filter]
    congr 1
    congr 1
    refine List.filter_congr fun g _ => ?_
    by_cases h1 : g.sc = sc <;> by_cases h2 : 0 < g.maplen <;> simp [h1, h2]
  have hLt48LeR :
      ((rootGs.filter fun g => decide (g.sc < 48)).map fun g => g.maplen * 4096).sum ≤
        BaseRootFine + linForm slotWt pk := by
    rw [hLt48SumEq]
    exact Nat.le_trans
      (accounting_sum_map_le fun sc hsc => hRootLe sc (List.mem_range.mp hsc))
      (sum_rBound_le pk)
  have hRootSumEq :
      (rootGs.map fun g => g.maplen * 4096).sum =
        (((large63Groups st).map fun g => g.maplen * 4096).sum + straddle63Bytes st) +
        ((rootGs.filter fun g => decide (g.sc < 48)).map fun g => g.maplen * 4096).sum := by
    rw [hPartRoot, hRoot63Eq, hRootLt48Eq, hPart63]
    rfl
  have hByteBound : ((dynamicRootRegions st).map Prod.snd).sum ≤ fineFootprint b := by
    rw [hDynSum, hRootSumEq]
    unfold fineFootprint
    exact footprint_combine_arith BaseRootFine
      (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length)
      (fineMaxMetaAreas b)
      ((rootGs.filter fun g => decide (g.sc < 48)).map fun g => g.maplen * 4096).sum
      (linForm slotWt pk)
      (straddle63Bytes st)
      b.cumSmallBytes
      ((large63Groups st).map fun g => g.maplen * 4096).sum
      (finePeak63Bytes b)
      hPagesLeMax hLt48LeR ( Nat.le_trans (Nat.add_le_add_left hStrBytesLe _) hCumB ) hLargeBytesLe
  exact ⟨hLenBound, hByteBound, dynamicRootRegions_fit48_inflight hwf⟩

/-- Derived `masterDom` byte-count bound under `MallocngFineInv`:
    `st.masterDom.length ≤ fineFootprint b`. -/
theorem masterDom_fine_length_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {b : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hFine : MallocngFineInv inflight b ivs alignMap st) :
    st.masterDom.length ≤ fineFootprint b := by
  have ⟨_, hByteBound, hFit48⟩ := dynamicRootRegions_fine_bounds hwf hFine
  let allDynBytes := (dynamicRootRegions st).flatMap fun r => rangeAddrs r.1 r.2
  have hRegBound : ∀ r ∈ dynamicRootRegions st, r.2 ≤ 2 ^ 64 := by
    intro r hr
    have h48 := hFit48 r hr
    omega
  have hSubDom : ∀ a ∈ st.masterDom, a ∈ allDynBytes := by
    intro a ha
    obtain ⟨r, hrMem, hInReg⟩ := hwf.masterDom_wf.2.2 a ha
    exact List.mem_flatMap.mpr ⟨r, hrMem,
      (mem_rangeAddrs_iff_inRegion r.1 (hRegBound r hrMem) a).mpr hInReg⟩
  have hDomLeAll : st.masterDom.length ≤ allDynBytes.length :=
    nodup_length_le_of_subset hwf.masterDom_wf.1 hSubDom
  have hFlatLen : ∀ rs : List (BitVec 64 × Nat),
      ((rs.flatMap fun r => rangeAddrs r.1 r.2).length) = (rs.map Prod.snd).sum := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rest ih =>
      simp only [List.flatMap_cons, List.length_append, rangeAddrs_length, List.map_cons,
        List.sum_cons, ih]
  rw [hFlatLen] at hDomLeAll
  exact Nat.le_trans hDomLeAll hByteBound

/-! ## `heap_footprint_bound` Discharge -/

private theorem holds_sepConj_right {P Q : SepProp} {h : Heap}
    (hh : (P ∗ Q).holds h) :
    ∃ h₂, Q.holds h₂ := by
  rw [sepConj_comm] at hh
  exact SepProp.holds_sepConj_left hh

/-- Discharges `MallocngCostModelSound.heap_footprint_bound`. -/
theorem fineHeap_footprint_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (FineHeapImpl γ A tp brkStart brk b ivs) h) :
    ivs.length ≤ fineMaxDynIvs b ∧
    (ivs.map Prod.snd).sum ≤ fineFootprint b ∧
    ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48 := by
  have hHolds' : (FineHeapImpl γ A tp brkStart brk b ivs).holds h := hHolds
  rw [FineHeapImpl_eq, FineCoreImpl_eq] at hHolds'
  obtain ⟨_, hCoreH⟩ := SepProp.holds_sepConj_left hHolds'
  obtain ⟨_, hExH⟩ := holds_sepConj_right hCoreH
  obtain ⟨st, hExH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨alignMap, hExH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨liveCost, hExH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨peakCost, hBodyH⟩ := SepProp.holds_sepExists hExH
  unfold FineCoreStInflightA MallocngCoreStInflightA at hBodyH
  obtain ⟨hFine, hRest1⟩ := SepProp.holds_pure_sepConj hBodyH
  obtain ⟨_, hRest2⟩ := holds_sepConj_right hRest1
  obtain ⟨hwf, _⟩ := SepProp.holds_pure_sepConj hRest2
  rw [hFine.ivs_eq rfl]
  exact dynamicRootRegions_fine_bounds hwf hFine

end LibsignalBinary.Heap.Fine
