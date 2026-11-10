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
public import VerifiedLibraries.Mallocng.Proofs.AccountingHelpers

/-!
# Virtual-Memory and Metadata Accounting

Derives `dynamicRootRegions` and `masterDom` byte-footprint bounds from `MallocngWF`,
discharging `MallocngIfaceFacts.heap_footprint_bound`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Dynamic virtual-memory footprint bounds -/

private def checkMetaShiftBound : Bool :=
  (List.range 41).all fun m =>
    if 1 ≤ m then (m + 1) + (2 ^ (m + 1) - 2) ≤ 5 * (2 ^ m - m) + 4 else true

private theorem checkMetaShiftBound_true : checkMetaShiftBound = true := by
  decide +kernel

private theorem meta_guard_avail_pages_le {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    st.metaAreas.length + st.guardPages.length + st.availMetaPages.length ≤
      16 + 6 * (peakCost / 655360) := by
  have ⟨hMetaLe, hShift0, hShiftPos⟩ := hwf.meta_pages_bound
  by_cases hZero : st.ctx.metaAllocShift = 0#64
  · have ⟨hAvNil, hGdLe⟩ := hShift0 hZero
    have hAvLen : st.availMetaPages.length = 0 := by simp [hAvNil]
    omega
  · have hPos : 1 ≤ st.ctx.metaAllocShift.toNat := by
      have : st.ctx.metaAllocShift.toNat ≠ 0 := fun h => hZero (BitVec.eq_of_toNat_eq h)
      omega
    have ⟨hmLe40, hPowLeMeta, _hSumLe, hGdLe, hAvLe0⟩ := hShiftPos st.ctx.metaAllocShift.toNat hPos rfl
    have hAvLe : st.availMetaPages.length ≤ 2 ^ (st.ctx.metaAllocShift.toNat + 1) - 2 := by
      have : 2 ^ st.ctx.metaAllocShift.toNat ≤ 2 ^ (st.ctx.metaAllocShift.toNat + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hCheck := List.all_eq_true.mp checkMetaShiftBound_true st.ctx.metaAllocShift.toNat
      (List.mem_range.mpr (by omega))
    simp only [hPos, ↓reduceIte, decide_eq_true_eq] at hCheck
    omega

private theorem sum_const_bound {α : Type} {f : α → Nat} {c : Nat} {xs : List α}
    (hle : ∀ x ∈ xs, f x ≤ c) :
    (xs.map f).sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hle x List.mem_cons_self
    have h2 := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    have hDist : (rest.length + 1) * c = c + rest.length * c := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

private theorem no_claimed_slot_of_zero {st : MallocngSt} (h0 : totalClaimedSlots st = 0)
    {g : GroupDesc} (hg : g ∈ st.groups) {s : SlotState} (hs : s ∈ g.slots) :
    s ≠ .claimed := by
  intro hEq
  have hMemF : s ∈ g.slots.filter SlotState.isClaimed :=
    List.mem_filter.mpr ⟨hs, by simp [hEq, SlotState.isClaimed]⟩
  have hPos : 1 ≤ (g.slots.filter SlotState.isClaimed).length := List.length_pos_of_mem hMemF
  have hMemSum : (g.slots.filter SlotState.isClaimed).length ∈
      st.groups.map (fun h => (h.slots.filter SlotState.isClaimed).length) :=
    List.mem_map_of_mem hg
  have hLe := accounting_le_sum_of_mem hMemSum
  unfold totalClaimedSlots at h0
  omega

private theorem sum_snd_const {α : Type} (f : α → BitVec 64) (c : Nat) (xs : List α) :
    ((xs.map fun x => (f x, c)).map Prod.snd).sum = c * xs.length := by
  induction xs with
  | nil => simp
  | cons _ rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.mul_succ, Nat.add_comm]

/-- Interval-count and byte-sum bounds for `dynamicRootRegions` at quiescent API boundaries. -/
theorem dynamicRootRegions_bounds {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st) :
    (dynamicRootRegions st).length ≤ 48 + peakCost / 32768 ∧
    ((dynamicRootRegions st).map Prod.snd).sum ≤ 30 * 1024 * 1024 + MallocngLinearFactor * peakCost := by
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
  let empRootGs := rootGs.filter GroupDesc.isEmpty
  let nonEmpRootGs := rootGs.filter (fun g => !GroupDesc.isEmpty g)
  have hRootLenSplit : rootGs.length = empRootGs.length + nonEmpRootGs.length :=
    accounting_length_filter_partition GroupDesc.isEmpty rootGs
  have hRootSplit :
      (rootGs.map fun g => g.maplen * 4096).sum =
      (empRootGs.map fun g => g.maplen * 4096).sum +
      (nonEmpRootGs.map fun g => g.maplen * 4096).sum :=
    accounting_sum_filter_partition GroupDesc.isEmpty (fun g => g.maplen * 4096) rootGs
  have hSubEmp : ∀ m ∈ empRootGs.map (·.metaPtr),
      m ∈ (st.groups.filter (·.isEmpty)).map (·.metaPtr) := by
    intro m hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
    have ⟨hgRoot, hE⟩ := List.mem_filter.mp hg
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
  have hEmpNd : (empRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hEmpRootLen : empRootGs.length ≤ 32 := by
    have h1 := nodup_length_le_of_subset hEmpNd hSubEmp
    have h2 := emptyGroups_length_le hwf
    simp only [List.length_map] at h1
    omega
  have hEmpRootBytes : (empRootGs.map fun g => g.maplen * 4096).sum ≤ 32 * 524288 := by
    let empSmall := empRootGs.filter (fun g => decide (g.sc ≤ 25))
    let empMed := empRootGs.filter (fun g => !decide (g.sc ≤ 25))
    have hSplitEmp := accounting_sum_filter_partition (fun g => decide (g.sc ≤ 25))
      (fun g => g.maplen * 4096) empRootGs
    have hSmallNd : (empSmall.map (·.metaPtr)).Nodup :=
      ((List.filter_sublist).map _).nodup hEmpNd
    have hMedNd : (empMed.map (·.metaPtr)).Nodup :=
      ((List.filter_sublist).map _).nodup hEmpNd
    have hSmallLen : empSmall.length ≤ 19 :=
      empGs_range_length_le hwf empSmall 7 19 hSmallNd
        (fun g hg => by
          have ⟨hgEmp, _⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          exact ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
        (fun g hg => by
          have ⟨hgEmp, hLe25B⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          have hLe25 : g.sc ≤ 25 := of_decide_eq_true hLe25B
          have ⟨_, hGe7, _⟩ := hwf.empty_groups_bound g (List.mem_filter.mp hgRoot).1 hE
          omega)
    have hMedLen : empMed.length ≤ 13 :=
      empGs_range_length_le hwf empMed 26 13 hMedNd
        (fun g hg => by
          have ⟨hgEmp, _⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          exact ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
        (fun g hg => by
          have ⟨hgEmp, hGt25B⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          have hNotLe25 : ¬ (g.sc ≤ 25) := of_decide_eq_false (by simpa using hGt25B)
          have ⟨_, _, hLe38, _⟩ := hwf.empty_groups_bound g (List.mem_filter.mp hgRoot).1 hE
          omega)
    have hSmallEach : ∀ g ∈ empSmall, g.maplen * 4096 ≤ 65536 := by
      intro g hg
      have ⟨hgEmp, hLe25B⟩ := List.mem_filter.mp hg
      have ⟨hgRoot, _⟩ := List.mem_filter.mp hgEmp
      have ⟨hgIn, hMapPosB⟩ := List.mem_filter.mp hgRoot
      exact ((hwf.groups_wf g hgIn).2.2.2.2.2.2.2.2.2.2.2.1 (of_decide_eq_true hMapPosB)).2.2.1
        (of_decide_eq_true hLe25B)
    have hMedEach : ∀ g ∈ empMed, g.maplen * 4096 ≤ 1048576 := by
      intro g hg
      have ⟨hgEmp, _⟩ := List.mem_filter.mp hg
      have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
      exact (hwf.empty_groups_bound g (List.mem_filter.mp hgRoot).1 hE).2.2.2.1
    have hSmallSum := sum_const_bound hSmallEach
    have hMedSum := sum_const_bound hMedEach
    dsimp only [empSmall, empMed] at hSmallLen hMedLen hSmallSum hMedSum
    omega
  let rootMeta : GroupDesc → BitVec 64 := fun h => iterParentMeta st 7 h.metaPtr
  let groupWeight : GroupDesc → Nat := fun h => 16 * (h.slots.map slotEffCost).sum
  have hClaim0 : totalClaimedSlots st = 0 := by
    have h := hwf.inflight_wf; omega
  have hEachNonEmp : ∀ g ∈ nonEmpRootGs,
      g.maplen * 4096 ≤
        ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight).sum ∧
      16 * 65536 ≤
        ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight).sum := by
    intro g hg
    have ⟨hgRoot, hgNotEB⟩ := List.mem_filter.mp hg
    have ⟨hgIn, hgMapPosB⟩ := List.mem_filter.mp hgRoot
    have hgMapPos : 0 < g.maplen := of_decide_eq_true hgMapPosB
    have hgNotE : g.isEmpty = false := by simpa using hgNotEB
    have hGWf := hwf.groups_wf g hgIn
    have hParNone : g.parentMeta = none := hGWf.2.2.2.2.2.2.2.2.2.2.1.mp hgMapPos
    have hFixG : parentMetaStep st g.metaPtr = g.metaPtr := by
      simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hgIn, hParNone]
    obtain ⟨leaf, hleaf, d, hdLt8, hLeafDir, hIterD, hGe25Eq⟩ :=
      descend_nonempty_group hwf hgIn hgNotE
    have hRootEq : rootMeta leaf = g.metaPtr := by
      show iterParentMeta st 7 leaf.metaPtr = g.metaPtr
      have hdEq : 7 = d + (7 - d) := by omega
      rw [hdEq, iterParentMeta_add, hIterD]
      exact iterParentMeta_fixed hFixG (7 - d)
    unfold GroupDesc.hasDirectLeaf at hLeafDir
    obtain ⟨s, hsMem, hsDir⟩ := List.any_eq_true.mp hLeafDir
    obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
    have hsNotClaimed := no_claimed_slot_of_zero hClaim0 hleaf hsMem
    rcases hS : s with _ | _ | _ | cm | ⟨userPtr, reqSize, effCost⟩
    · simp [hS] at hsDir
    · simp [hS] at hsDir
    · exact False.elim (hsNotClaimed hS)
    · simp [hS] at hsDir
    · have hSlotEq : leaf.slots[idx]'hIdx = .liveUser userPtr reqSize effCost := hEqS.trans hS
      have hLeafSWf := (hwf.groups_wf leaf hleaf).slot_wf idx hIdx
      rw [hSlotEq] at hLeafSWf
      have hGe64k : 65536 ≤ effCost := by
        have hMax := hLeafSWf.2.2.2.2.2.2.2.1
        unfold MallocngMinBlockCost at hMax
        omega
      have hBytesLeEff : g.maplen * 4096 ≤ 16 * effCost := by
        rcases hGWf.1 with hScLt48 | hSc63
        · have hLe1M := (hGWf.2.2.2.2.2.2.2.2.2.2.2.1 hgMapPos).2.2.2 hScLt48
          omega
        · have ⟨_, hLeafEqG⟩ := hGe25Eq (by omega)
          subst hLeafEqG
          have h63Le := hLeafSWf.2.2.2.2.2.2.2.2.2.2.2.1 hSc63
          omega
      have hEffInLeaf : effCost ≤ (leaf.slots.map slotEffCost).sum := by
        have hMemC : effCost ∈ leaf.slots.map slotEffCost := by
          rw [hS] at hsMem
          exact List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩
        exact accounting_le_sum_of_mem hMemC
      have hLeafInFiber : groupWeight leaf ∈
          (st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨hleaf, beq_iff_eq.mpr hRootEq⟩)
      have hWeightInFiber : groupWeight leaf ≤
          ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight).sum :=
        accounting_le_sum_of_mem hLeafInFiber
      have hWLeaf : groupWeight leaf = 16 * (leaf.slots.map slotEffCost).sum := rfl
      have hW1 : g.maplen * 4096 ≤ groupWeight leaf := by
        clear hGWf hLeafSWf hGe25Eq
        rw [hWLeaf]; omega
      have hW2 : 16 * 65536 ≤ groupWeight leaf :=
        Nat.mul_le_mul_left 16 (Nat.le_trans hGe64k hEffInLeaf)
      exact ⟨Nat.le_trans hW1 hWeightInFiber, Nat.le_trans hW2 hWeightInFiber⟩
  have hNonEmpMetaNd : (nonEmpRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hFiberBound :
      (nonEmpRootGs.map fun g =>
        ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight).sum).sum ≤
      (st.groups.map groupWeight).sum := by
    have hMapEq :
        (nonEmpRootGs.map fun g =>
          ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight).sum) =
        ((nonEmpRootGs.map (·.metaPtr)).map fun m =>
          ((st.groups.filter fun h => rootMeta h == m).map groupWeight).sum) := by
      rw [List.map_map]; rfl
    rw [hMapEq]
    exact sum_filter_beq_le_of_nodup rootMeta groupWeight st.groups hNonEmpMetaNd
  have hWeightTotal : (st.groups.map groupWeight).sum = 16 * totalLiveEffCost st := by
    unfold totalLiveEffCost
    dsimp only [groupWeight]
    clear hFiberBound hEachNonEmp
    induction st.groups with
    | nil => rfl
    | cons h rest ih => simp [ih]; omega
  have hEffLe : totalLiveEffCost st ≤ liveCost := hwf.effCost_le_live
  have hLiveLePeak : liveCost ≤ peakCost := hwf.live_le_peak
  have hNonEmpBytesLe : (nonEmpRootGs.map fun g => g.maplen * 4096).sum ≤ 16 * peakCost := by
    have h1 := accounting_sum_map_le fun g hg => (hEachNonEmp g hg).1
    omega
  have hNonEmpLenLe : nonEmpRootGs.length ≤ peakCost / 65536 := by
    have hMinSum : (nonEmpRootGs.map fun _ => 16 * 65536).sum ≤
        (nonEmpRootGs.map fun g =>
          ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupWeight).sum).sum :=
      accounting_sum_map_le fun g hg => (hEachNonEmp g hg).2
    have hConstSum : (nonEmpRootGs.map fun _ => 16 * 65536).sum = 16 * 65536 * nonEmpRootGs.length := by
      clear hMinSum
      induction nonEmpRootGs with
      | nil => rfl
      | cons _ rest ih => simp [ih]; omega
    omega
  have hPagesLe := meta_guard_avail_pages_le hwf
  simp only [MallocngLinearFactor]
  exact ⟨by omega, by omega⟩

/-- Byte-count bound on `st.masterDom` at quiescent API boundaries. -/
theorem masterDom_length_le {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st) :
    st.masterDom.length ≤ 30 * 1024 * 1024 + MallocngLinearFactor * peakCost := by
  let allDynBytes := (dynamicRootRegions st).flatMap fun r => rangeAddrs r.1 r.2
  have hRegBound : ∀ r ∈ dynamicRootRegions st, r.2 ≤ 2 ^ 64 := by
    intro r hr
    unfold dynamicRootRegions at hr
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hr
    rcases hr with (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨g, ⟨hg, hPosB⟩, rfl⟩)
    · dsimp; omega
    · dsimp; omega
    · dsimp; omega
    · have hPos : 0 < g.maplen := of_decide_eq_true hPosB
      have hTot := (hwf.groups_wf g hg).2.2.2.2.2.2.1
      simp only [GroupDesc.totalBytes, hPos, ↓reduceIte] at hTot
      dsimp
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
  exact Nat.le_trans hDomLeAll (dynamicRootRegions_bounds hwf).2

/-! ## Top-level heap footprint bounds -/

private theorem flatMap_pair_length (es : List (BitVec 64 × BitVec 64)) :
    (es.flatMap fun (t, v) => [t, v]).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨t, v⟩
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons]
    exact congrArg (· + 2) ih ▸ by omega

private theorem FootprintIn_pointsToWords64 (a : BitVec 64) (ws : List (BitVec 64))
    (hlen : 8 * ws.length ≤ 2 ^ 64) {S : BitVec 64 → Prop}
    (hS : ∀ x, InRegion a (8 * ws.length) x → S x) :
    SepProp.FootprintIn (a ↦₆₄* ws) S := by
  induction ws generalizing a with
  | nil =>
    simpa [pointsToWords64_nil] using SepProp.FootprintIn.emp
  | cons w rest ih =>
    simp only [List.length_cons] at hlen hS
    rw [pointsToWords64_cons]
    refine SepProp.FootprintIn.sepConj
      (SepProp.FootprintIn.pointsTo64 fun x hx => hS x ?_)
      (ih (a + 8#64) (by omega) fun x hx => hS x ?_)
    · unfold InRegion at hx ⊢; omega
    · unfold InRegion at hx ⊢; bv_omega

private theorem boundedFootprint_mallocngAuxvAt (auxvPtr : BitVec 64) :
    SepProp.BoundedFootprint (MallocngAuxvAt auxvPtr) 1064 := by
  unfold MallocngAuxvAt
  refine SepProp.BoundedFootprint.sepExists fun preEntries => ?_
  refine SepProp.BoundedFootprint.sepExists fun sufEntries => ?_
  refine SepProp.BoundedFootprint.sepExists fun randPtr => ?_
  refine SepProp.BoundedFootprint.sepExists fun nullVal => ?_
  refine SepProp.BoundedFootprint.sepExists fun secretBytes => ?_
  refine SepProp.BoundedFootprint.pure_sepConj fun hPure => ?_
  have hSumLe : preEntries.length + sufEntries.length ≤ 64 := hPure.2.2.1
  have hSecLen : secretBytes.length = 8 := hPure.2.2.2.2.2
  let ws :=
    (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v]
  have hWsLen : ws.length = 2 * (preEntries.length + sufEntries.length + 2) := by
    simp only [ws, flatMap_pair_length, List.length_append, List.length_singleton]
    omega
  have hB1 : SepProp.BoundedFootprint (auxvPtr ↦₆₄* ws) (8 * ws.length) :=
    BoundedFootprint_pointsToWords64 auxvPtr ws (by omega)
  have hB2 : SepProp.BoundedFootprint ((randPtr + 8#64) ↦ₛ secretBytes) secretBytes.length :=
    BoundedFootprint_pointsToBytes (randPtr + 8#64) secretBytes (by omega)
  exact SepProp.BoundedFootprint.mono (SepProp.BoundedFootprint.sepConj hB1 hB2) (by omega)

private theorem boundedFootprint_mallocngAuxvState (γ : GhostName) (auxvPtr : BitVec 64)
    (snap : Option MallocngAuxvSnap) :
    SepProp.BoundedFootprint (MallocngAuxvState γ auxvPtr snap) 1064 := by
  unfold MallocngAuxvState
  have hBody : SepProp.BoundedFootprint (match snap with
      | none => MallocngAuxvAt auxvPtr
      | some (preEntries, randPtr, sufEntries, nullVal, sec) =>
        ⌜MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries⌝ ∗
        (auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
          fun (t, v) => [t, v])) ∗
        ((randPtr + 8#64) ↦₆₄ sec)) 1064 := by
    rcases snap with _ | ⟨preEntries, randPtr, sufEntries, nullVal, sec⟩
    · exact boundedFootprint_mallocngAuxvAt auxvPtr
    · refine SepProp.BoundedFootprint.pure_sepConj fun hPure => ?_
      have hSumLe : preEntries.length + sufEntries.length ≤ 64 := hPure.2.2.1
      let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v]
      have hWsLen : ws.length = 2 * (preEntries.length + sufEntries.length + 2) := by
        simp only [ws, flatMap_pair_length, List.length_append, List.length_singleton]; omega
      have hB1 : SepProp.BoundedFootprint (auxvPtr ↦₆₄* ws) (8 * ws.length) :=
        BoundedFootprint_pointsToWords64 auxvPtr ws (by omega)
      have hB2 : SepProp.BoundedFootprint ((randPtr + 8#64) ↦₆₄ sec) 8 :=
        BoundedFootprint_pointsTo64 (randPtr + 8#64) sec
      exact SepProp.BoundedFootprint.mono (SepProp.BoundedFootprint.sepConj hB1 hB2) (by omega)
  exact SepProp.BoundedFootprint.mono
    (SepProp.BoundedFootprint.sepConj
      (BoundedFootprint_ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr snap)) hBody)
    (by omega)

private theorem boundedFootprint_mallocngRuntime (A : MallocngAddrs) (tp : BitVec 64) :
    SepProp.BoundedFootprint (MallocngRuntime A tp) 13 := by
  unfold MallocngRuntime
  have h1 : SepProp.BoundedFootprint (∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) 4 :=
    SepProp.BoundedFootprint.sepExists fun errnoVal => BoundedFootprint_pointsTo32 _ errnoVal
  have h2 : SepProp.BoundedFootprint ((A.libc + 3#64) ↦₈ 0#8) 1 :=
    BoundedFootprint_pointsTo8 _ _
  have h3 : SepProp.BoundedFootprint ((A.libc + 48#64) ↦₆₄ 4096#64) 8 :=
    BoundedFootprint_pointsTo64 _ _
  exact SepProp.BoundedFootprint.mono
    (SepProp.BoundedFootprint.sepConj h1 (SepProp.BoundedFootprint.sepConj h2 h3)) (by omega)

private theorem holds_sepConj_right {P Q : SepProp} {h : Heap}
    (hh : (P ∗ Q).holds h) :
    ∃ h₂, Q.holds h₂ := by
  rw [sepConj_comm] at hh
  exact SepProp.holds_sepConj_left hh

private theorem dynamicRootRegions_fit48 {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st) :
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

/-- Discharges `MallocngIfaceFacts.heap_footprint_bound`. -/
theorem mallocngHeap_footprint_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngIface.MallocngHeap γ A tp brkStart brk b ivs) h) :
    (b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
    (ivs.length ≤ 48 + 2 * b.peakCount ∧
      (ivs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost ∧
      ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48) ∧
    (∃ allIvs : List (BitVec 64 × Nat),
      allIvs.length ≤ 64 + 2 * b.peakCount ∧
      (allIvs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost ∧
      ∀ a : BitVec 64, (h a ≠ none ∨ h.mapped a = true) → MallocngInIntervals allIvs a) ∧
    ∃ dom : List (BitVec 64),
      dom.length ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost ∧
      ∀ a : BitVec 64, (h a ≠ none ∨ h.mapped a = true) → a ∈ dom := by
  have hHolds' : (MallocngHeapImpl γ A tp brkStart brk b ivs).holds h := hHolds
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq] at hHolds'
  have hHoldsIv := hHolds'
  unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState MallocngRuntime at hHoldsIv
  simp only [sepExists_sepConj_left, sepExists_sepConj_right] at hHoldsIv
  obtain ⟨errnoVal, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
  obtain ⟨st, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
  obtain ⟨_, hCoreH⟩ := SepProp.holds_sepConj_left hHoldsIv
  obtain ⟨_, hStH0⟩ := holds_sepConj_right hCoreH
  obtain ⟨hCountIvs, hStH⟩ := SepProp.holds_pure_sepConj hStH0
  obtain ⟨hwf, _⟩ := SepProp.holds_pure_sepConj hStH
  obtain ⟨randPtr, snapVal, auxvSub, hAuxvFp, hHoldsSub⟩ :
      ∃ (randPtr : BitVec 64) (snapVal : Option MallocngAuxvSnap) (auxvSub : SepProp),
        (∀ S : BitVec 64 → Prop,
          (∀ a, InRegion st.auxvPtr 1056 a → S a) →
          (∀ a, InRegion (randPtr + 8#64) 8 a → S a) →
          SepProp.FootprintIn auxvSub S) ∧
        ((MallocngRoTablesA A ∗
          (⌜MallocngCountIvsWF b ivs st⌝ ∗
            (⌜MallocngWFInflight 0 A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
              MallocngLiveAuth γ st.liveMap ∗
              (A.ctx ↦ₛ st.ctx.toBytes) ∗
              (A.lock ↦₃₂ 0#32) ∗
              (A.replaced ↦₃₂ 0#32) ∗
              (A.aaReplaced ↦₃₂ 0#32) ∗
              ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
              (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr snapVal) ∗ auxvSub) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
              MappedSet st.masterDom (OwnedMappedByte st)))) ∗
         ((tp - 0xa4#64) ↦₃₂ errnoVal ∗
          (A.libc + 3#64) ↦₈ 0#8 ∗
          (A.libc + 48#64) ↦₆₄ 4096#64)).holds h := by
    rcases hSnap : st.auxvSnap with _ | ⟨preEntries, randPtr, sufEntries, nullVal, sec⟩
    · rw [hSnap] at hHoldsIv; dsimp only at hHoldsIv; unfold MallocngAuxvAt at hHoldsIv
      simp only [sepExists_sepConj_left, sepExists_sepConj_right] at hHoldsIv
      obtain ⟨preEntries, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
      obtain ⟨sufEntries, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
      obtain ⟨randPtr, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
      obtain ⟨nullVal, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
      obtain ⟨secretBytes, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
      obtain ⟨_, hCoreH1⟩ := SepProp.holds_sepConj_left hHoldsIv
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hCoreH1
      obtain ⟨_, hStH1⟩ := SepProp.holds_pure_sepConj hStH1
      obtain ⟨_, hStH1⟩ := SepProp.holds_pure_sepConj hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hPairH1⟩ := SepProp.holds_sepConj_left hStH1
      obtain ⟨_, hAuxvH1⟩ := holds_sepConj_right hPairH1
      obtain ⟨hPureAuxv, _⟩ := SepProp.holds_pure_sepConj hAuxvH1
      let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v]
      have hSumLe : preEntries.length + sufEntries.length ≤ 64 := hPureAuxv.2.2.1
      have hSecLen : secretBytes.length = 8 := hPureAuxv.2.2.2.2.2
      have hWsLen : ws.length = 2 * (preEntries.length + sufEntries.length + 2) := by
        simp only [ws, flatMap_pair_length, List.length_append, List.length_singleton]; omega
      refine ⟨randPtr, none, _, fun S hAvS hSecS => ?_, hHoldsIv⟩
      exact SepProp.FootprintIn.sepConj SepProp.FootprintIn.pure
        (SepProp.FootprintIn.sepConj
          (FootprintIn_pointsToWords64 st.auxvPtr ws (by omega)
            (fun a ha => hAvS a (by unfold InRegion at ha ⊢; omega)))
          (SepProp.FootprintIn.pointsToBytes (by omega)
            (fun a ha => by rw [hSecLen] at ha; exact hSecS a ha)))
    · rw [hSnap] at hHoldsIv; dsimp only at hHoldsIv
      obtain ⟨_, hCoreH1⟩ := SepProp.holds_sepConj_left hHoldsIv
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hCoreH1
      obtain ⟨_, hStH1⟩ := SepProp.holds_pure_sepConj hStH1
      obtain ⟨_, hStH1⟩ := SepProp.holds_pure_sepConj hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hStH1⟩ := holds_sepConj_right hStH1
      obtain ⟨_, hPairH1⟩ := SepProp.holds_sepConj_left hStH1
      obtain ⟨_, hAuxvH1⟩ := holds_sepConj_right hPairH1
      obtain ⟨hPureAuxv, _⟩ := SepProp.holds_pure_sepConj hAuxvH1
      let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v]
      have hSumLe : preEntries.length + sufEntries.length ≤ 64 := hPureAuxv.2.2.1
      have hWsLen : ws.length = 2 * (preEntries.length + sufEntries.length + 2) := by
        simp only [ws, flatMap_pair_length, List.length_append, List.length_singleton]; omega
      refine ⟨randPtr, some (preEntries, randPtr, sufEntries, nullVal, sec), _,
        fun S hAvS hSecS => ?_, hHoldsIv⟩
      exact SepProp.FootprintIn.sepConj SepProp.FootprintIn.pure
        (SepProp.FootprintIn.sepConj
          (FootprintIn_pointsToWords64 st.auxvPtr ws (by omega)
            (fun a ha => hAvS a (by unfold InRegion at ha ⊢; omega)))
          (SepProp.FootprintIn.pointsTo64 hSecS))
  have hLiveLePeak : b.liveCost ≤ b.peakCost := hwf.live_le_peak
  have hCountLePeak : b.liveCount ≤ b.peakCount := hCountIvs.1
  have hIvsEq : ivs = dynamicRootRegions st := hCountIvs.2.2.1
  have hIvsLen : ivs.length ≤ 48 + 2 * b.peakCount := hCountIvs.2.2.2.1
  have hCtxLen : st.ctx.toBytes.length = 928 :=
    CtxFields.toBytes_length hwf.ctx_lens.1 hwf.ctx_lens.2.1 hwf.ctx_lens.2.2.1
      hwf.ctx_lens.2.2.2.1 (by rw [hwf.ctx_lens.2.2.2.2.1]; simp)
  let staticIvs : List (BitVec 64 × Nat) :=
    [ (A.sizeClasses, 96),
      (A.debruijnFree, 32),
      (A.medCntTab, 4),
      (A.smallCntTab, 27),
      (A.debruijnAlloc, 32),
      (A.ctx, 928),
      (A.lock, 4),
      (A.replaced, 4),
      (A.aaReplaced, 4),
      (A.libc + 8#64, 8),
      (st.auxvPtr, 1056),
      (randPtr + 8#64, 8),
      (tp - 0xa4#64, 4),
      (A.libc + 3#64, 1),
      (A.libc + 48#64, 8) ]
  let allIvs : List (BitVec 64 × Nat) := staticIvs ++ dynamicRootRegions st
  have ⟨_hDynLenBound, hDynSumBound⟩ := dynamicRootRegions_bounds hwf
  have hIvsSum : (ivs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost := by
    rw [hIvsEq]
    simp only [MallocngBaseOverhead]
    omega
  have hIvsFit : ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48 := by
    rw [hIvsEq]
    exact dynamicRootRegions_fit48 hwf
  have hAllIvsLen : allIvs.length ≤ 64 + 2 * b.peakCount := by
    have hSL : staticIvs.length = 15 := rfl
    change (staticIvs ++ dynamicRootRegions st).length ≤ _
    rw [List.length_append, hSL, ← hIvsEq]
    omega
  have hAllIvsSum : (allIvs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost := by
    have hSS : (staticIvs.map Prod.snd).sum = 2216 := by
      change ([96, 32, 4, 27, 32, 928, 4, 4, 4, 8, 1056, 8, 4, 1, 8] : List Nat).sum = 2216; decide
    rw [List.map_append, List.sum_append, hSS]
    simp only [MallocngBaseOverhead]
    omega
  let S : BitVec 64 → Prop := MallocngInIntervals allIvs
  have hInStatic : ∀ (iv : BitVec 64 × Nat), iv ∈ staticIvs → ∀ a, InRegion iv.1 iv.2 a → S a := by
    intro iv hiv a ha
    exact ⟨iv, List.mem_append_left _ hiv, ha⟩
  have hFpRo : SepProp.FootprintIn (MallocngRoTablesA A) S := by
    unfold MallocngRoTablesA MallocngRoTablesAt
    have hR0 : SepProp.FootprintIn (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) S :=
      SepProp.FootprintIn.pointsToBytesRO (by rw [sizeClassBytes_length]; omega)
        (fun a ha => by
          rw [sizeClassBytes_length] at ha
          exact hInStatic (A.sizeClasses, 96) (by simp [staticIvs]) a ha)
    have hR1 : SepProp.FootprintIn (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) S :=
      SepProp.FootprintIn.pointsToBytesRO (by rw [debruijn32Table_length]; omega)
        (fun a ha => by
          rw [debruijn32Table_length] at ha
          exact hInStatic (A.debruijnFree, 32) (by simp [staticIvs]) a ha)
    have hR2 : SepProp.FootprintIn (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) S :=
      SepProp.FootprintIn.pointsToBytesRO (by rw [medCntTabBytes_length]; omega)
        (fun a ha => by
          rw [medCntTabBytes_length] at ha
          exact hInStatic (A.medCntTab, 4) (by simp [staticIvs]) a ha)
    have hR3 : SepProp.FootprintIn (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) S :=
      SepProp.FootprintIn.pointsToBytesRO (by rw [smallCntTabBytes_length]; omega)
        (fun a ha => by
          rw [smallCntTabBytes_length] at ha
          exact hInStatic (A.smallCntTab, 27) (by simp [staticIvs]) a ha)
    have hR4 : SepProp.FootprintIn (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) S :=
      SepProp.FootprintIn.pointsToBytesRO (by rw [debruijn32Table_length]; omega)
        (fun a ha => by
          rw [debruijn32Table_length] at ha
          exact hInStatic (A.debruijnAlloc, 32) (by simp [staticIvs]) a ha)
    exact SepProp.FootprintIn.sepConj hR0
      (SepProp.FootprintIn.sepConj hR1
        (SepProp.FootprintIn.sepConj hR2
          (SepProp.FootprintIn.sepConj hR3 hR4)))
  have hFpAuth : SepProp.FootprintIn (MallocngLiveAuth γ st.liveMap) S :=
    footprintIn_mallocngLiveAuth γ st.liveMap
  have hFpCtx : SepProp.FootprintIn (A.ctx ↦ₛ st.ctx.toBytes) S :=
    SepProp.FootprintIn.pointsToBytes (by rw [hCtxLen]; omega)
      (fun a ha => by
        rw [hCtxLen] at ha
        exact hInStatic (A.ctx, 928) (by simp [staticIvs]) a ha)
  have hFpLk : SepProp.FootprintIn (A.lock ↦₃₂ 0#32) S :=
    SepProp.FootprintIn.pointsTo32 (hInStatic (A.lock, 4) (by simp [staticIvs]))
  have hFpRp : SepProp.FootprintIn (A.replaced ↦₃₂ 0#32) S :=
    SepProp.FootprintIn.pointsTo32 (hInStatic (A.replaced, 4) (by simp [staticIvs]))
  have hFpAa : SepProp.FootprintIn (A.aaReplaced ↦₃₂ 0#32) S :=
    SepProp.FootprintIn.pointsTo32 (hInStatic (A.aaReplaced, 4) (by simp [staticIvs]))
  have hFpAvPtr : SepProp.FootprintIn ((A.libc + 8#64) ↦₆₄ st.auxvPtr) S :=
    SepProp.FootprintIn.pointsTo64 (hInStatic (A.libc + 8#64, 8) (by simp [staticIvs]))
  have hFpAuxvPair :
      SepProp.FootprintIn
        (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr snapVal) ∗ auxvSub) S :=
    SepProp.FootprintIn.sepConj
      (SepProp.FootprintIn.ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr snapVal))
      (hAuxvFp S
        (hInStatic (st.auxvPtr, 1056) (by simp [staticIvs]))
        (hInStatic (randPtr + 8#64, 8) (by simp [staticIvs])))
  have hFpDyn :
      SepProp.FootprintIn
        (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st)) S :=
    SepProp.FootprintIn.mono
      (SepProp.FootprintIn.sepConj (ByteMap_footprintIn st.masterDom (OwnedRwByte st) st.byteVal)
        (SepProp.FootprintIn.sepConj (ProtNoneByteMap_footprintIn st.masterDom (OwnedProtNoneByte st) st.byteVal)
          (MappedSet_footprintIn st.masterDom (OwnedMappedByte st))))
      (fun a haDom => by
        obtain ⟨r, hrMem, hInR⟩ := hwf.masterDom_wf.2.2 a haDom
        exact ⟨r, List.mem_append_right _ hrMem, hInR⟩)
  have hFpErrno : SepProp.FootprintIn ((tp - 0xa4#64) ↦₃₂ errnoVal) S :=
    SepProp.FootprintIn.pointsTo32 (hInStatic (tp - 0xa4#64, 4) (by simp [staticIvs]))
  have hFpNlck : SepProp.FootprintIn ((A.libc + 3#64) ↦₈ 0#8) S :=
    SepProp.FootprintIn.pointsTo8
      (hInStatic (A.libc + 3#64, 1) (by simp [staticIvs]) (A.libc + 3#64) (by simp [InRegion]))
  have hFpPgsz : SepProp.FootprintIn ((A.libc + 48#64) ↦₆₄ 4096#64) S :=
    SepProp.FootprintIn.pointsTo64 (hInStatic (A.libc + 48#64, 8) (by simp [staticIvs]))
  have hIvFoot : ∀ a, (h a ≠ none ∨ h.mapped a = true) → S a :=
    SepProp.FootprintIn.sepConj
      (SepProp.FootprintIn.sepConj hFpRo
        (SepProp.FootprintIn.sepConj SepProp.FootprintIn.pure
          (SepProp.FootprintIn.sepConj SepProp.FootprintIn.pure
            (SepProp.FootprintIn.sepConj hFpAuth
              (SepProp.FootprintIn.sepConj hFpCtx
                (SepProp.FootprintIn.sepConj hFpLk
                  (SepProp.FootprintIn.sepConj hFpRp
                    (SepProp.FootprintIn.sepConj hFpAa
                      (SepProp.FootprintIn.sepConj hFpAvPtr
                        (SepProp.FootprintIn.sepConj hFpAuxvPair hFpDyn))))))))))
      (SepProp.FootprintIn.sepConj hFpErrno (SepProp.FootprintIn.sepConj hFpNlck hFpPgsz))
      h hHoldsSub
  have hRo : SepProp.BoundedFootprint (MallocngRoTablesA A) 200 := by
    unfold MallocngRoTablesA MallocngRoTablesAt
    have hB0 : SepProp.BoundedFootprint (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) 96 := by
      simpa [sizeClassBytes_length] using
        BoundedFootprint_pointsToBytesRO A.sizeClasses mallocngSizeClassBytes
          (by rw [sizeClassBytes_length]; omega)
    have hB1 : SepProp.BoundedFootprint (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) 32 := by
      simpa [debruijn32Table_length] using
        BoundedFootprint_pointsToBytesRO A.debruijnFree mallocngDebruijn32Table
          (by rw [debruijn32Table_length]; omega)
    have hB2 : SepProp.BoundedFootprint (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) 4 := by
      simpa [medCntTabBytes_length] using
        BoundedFootprint_pointsToBytesRO A.medCntTab mallocngMedCntTabBytes
          (by rw [medCntTabBytes_length]; omega)
    have hB3 : SepProp.BoundedFootprint (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) 27 := by
      simpa [smallCntTabBytes_length] using
        BoundedFootprint_pointsToBytesRO A.smallCntTab mallocngSmallCntTabBytes
          (by rw [smallCntTabBytes_length]; omega)
    have hB4 : SepProp.BoundedFootprint (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) 32 := by
      simpa [debruijn32Table_length] using
        BoundedFootprint_pointsToBytesRO A.debruijnAlloc mallocngDebruijn32Table
          (by rw [debruijn32Table_length]; omega)
    exact SepProp.BoundedFootprint.mono
      (SepProp.BoundedFootprint.sepConj hB0
        (SepProp.BoundedFootprint.sepConj hB1
          (SepProp.BoundedFootprint.sepConj hB2
            (SepProp.BoundedFootprint.sepConj hB3 hB4))))
      (by omega)
  have hCoreEx :
      SepProp.BoundedFootprint
        (∃∗ st : MallocngSt,
          ⌜MallocngCountIvsWF b ivs st⌝ ∗
          MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st)
        (30 * 1024 * 1024 + MallocngLinearFactor * b.peakCost + 2012) := by
    refine SepProp.BoundedFootprint.sepExists fun st' => ?_
    refine SepProp.BoundedFootprint.pure_sepConj fun _ => ?_
    unfold MallocngCoreStA MallocngCoreStInflightA
    refine SepProp.BoundedFootprint.pure_sepConj fun hwf' => ?_
    have hCtxLen' : st'.ctx.toBytes.length = 928 :=
      CtxFields.toBytes_length hwf'.ctx_lens.1 hwf'.ctx_lens.2.1 hwf'.ctx_lens.2.2.1
        hwf'.ctx_lens.2.2.2.1 (by rw [hwf'.ctx_lens.2.2.2.2.1]; simp)
    have hDomBound := masterDom_length_le hwf'
    have hAuth := BoundedFootprint_mallocngLiveAuth γ st'.liveMap
    have hCtx : SepProp.BoundedFootprint (A.ctx ↦ₛ st'.ctx.toBytes) 928 := by
      simpa [hCtxLen'] using BoundedFootprint_pointsToBytes A.ctx st'.ctx.toBytes
        (by rw [hCtxLen']; omega)
    have hLk := BoundedFootprint_pointsTo32 A.lock 0#32
    have hRp := BoundedFootprint_pointsTo32 A.replaced 0#32
    have hAa := BoundedFootprint_pointsTo32 A.aaReplaced 0#32
    have hAvPtr := BoundedFootprint_pointsTo64 (A.libc + 8#64) st'.auxvPtr
    have hAv := boundedFootprint_mallocngAuxvState γ st'.auxvPtr st'.auxvSnap
    have hDyn := BoundedFootprint_dynamicMaps st'.masterDom (OwnedRwByte st') (OwnedProtNoneByte st')
      (OwnedMappedByte st') st'.byteVal
    exact SepProp.BoundedFootprint.mono
      (SepProp.BoundedFootprint.sepConj hAuth
        (SepProp.BoundedFootprint.sepConj hCtx
          (SepProp.BoundedFootprint.sepConj hLk
            (SepProp.BoundedFootprint.sepConj hRp
              (SepProp.BoundedFootprint.sepConj hAa
                (SepProp.BoundedFootprint.sepConj hAvPtr
                  (SepProp.BoundedFootprint.sepConj hAv hDyn)))))))
      (by omega)
  have hRt := boundedFootprint_mallocngRuntime A tp
  have hTotal :
      SepProp.BoundedFootprint
        ((MallocngRoTablesA A ∗
          ∃∗ st : MallocngSt,
            ⌜MallocngCountIvsWF b ivs st⌝ ∗
            MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st) ∗
         MallocngRuntime A tp)
        (MallocngBaseOverhead + MallocngLinearFactor * b.peakCost) :=
    SepProp.BoundedFootprint.mono
      (SepProp.BoundedFootprint.sepConj (SepProp.BoundedFootprint.sepConj hRo hCoreEx) hRt)
      (by simp only [MallocngBaseOverhead]; omega)
  exact ⟨⟨hLiveLePeak, hCountLePeak⟩, ⟨hIvsLen, hIvsSum, hIvsFit⟩,
    ⟨allIvs, hAllIvsLen, hAllIvsSum, hIvFoot⟩, hTotal h hHolds'⟩

/-- Count-refined byte-sum bound on `ivs` for `mallocngIface.MallocngHeap`, decomposing dynamic
    mappings into metadata/guard/available pages (`≤ 10 + 6 * ((88 + 8 * b.peakCount) / 101)`),
    empty cached root groups (`≤ 14876672` bytes), and non-empty root groups
    (`≤ b.liveCost + 1048576 * b.liveCount` bytes). -/
theorem mallocngHeap_ivs_tight_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngIface.MallocngHeap γ A tp brkStart brk b ivs) h) :
    (b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
    ivs.length ≤ 48 + 2 * b.peakCount ∧
    (ivs.map Prod.snd).sum ≤
      14917632 + 24576 * ((88 + 8 * b.peakCount) / 101) +
        1048576 * b.liveCount + b.liveCost := by
  have hHoldsIv : (MallocngHeapImpl γ A tp brkStart brk b ivs).holds h := hHolds
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq] at hHoldsIv
  unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState MallocngRuntime at hHoldsIv
  simp only [sepExists_sepConj_left, sepExists_sepConj_right] at hHoldsIv
  obtain ⟨_errnoVal, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
  obtain ⟨st, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
  obtain ⟨_, hCoreH⟩ := SepProp.holds_sepConj_left hHoldsIv
  obtain ⟨_, hStH0⟩ := holds_sepConj_right hCoreH
  obtain ⟨hCountIvs, hStH⟩ := SepProp.holds_pure_sepConj hStH0
  obtain ⟨hwf, _⟩ := SepProp.holds_pure_sepConj hStH
  have hLiveLePeak : b.liveCost ≤ b.peakCost := hwf.live_le_peak
  have hCountLePeak : b.liveCount ≤ b.peakCount := hCountIvs.1
  have hLiveCountLe : totalLiveCount st ≤ b.liveCount := hCountIvs.2.1
  have hIvsEq : ivs = dynamicRootRegions st := hCountIvs.2.2.1
  have hIvsLen : ivs.length ≤ 48 + 2 * b.peakCount := hCountIvs.2.2.2.1
  have hMetaCount : st.metaAreas.length ≤ 1 + (88 + 8 * b.peakCount) / 101 := hCountIvs.2.2.2.2.1
  have hPagesTight :
      st.metaAreas.length + st.guardPages.length + st.availMetaPages.length ≤
        10 + 6 * ((88 + 8 * b.peakCount) / 101) := by
    have ⟨_hMetaLe, hShift0, hShiftPos⟩ := hwf.meta_pages_bound
    by_cases hZero : st.ctx.metaAllocShift = 0#64
    · have ⟨hAvNil, hGdLe⟩ := hShift0 hZero
      have hAvLen : st.availMetaPages.length = 0 := by simp [hAvNil]
      omega
    · have hPos : 1 ≤ st.ctx.metaAllocShift.toNat := by
        have : st.ctx.metaAllocShift.toNat ≠ 0 := fun h0 => hZero (BitVec.eq_of_toNat_eq h0)
        omega
      have ⟨hmLe40, hPowLeMeta, _hSumLe, hGdLe, hAvLe0⟩ :=
        hShiftPos st.ctx.metaAllocShift.toNat hPos rfl
      have hAvLe : st.availMetaPages.length ≤ 2 ^ (st.ctx.metaAllocShift.toNat + 1) - 2 := by
        have : 2 ^ st.ctx.metaAllocShift.toNat ≤ 2 ^ (st.ctx.metaAllocShift.toNat + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hCheck := List.all_eq_true.mp checkMetaShiftBound_true st.ctx.metaAllocShift.toNat
        (List.mem_range.mpr (by omega))
      simp only [hPos, ↓reduceIte, decide_eq_true_eq] at hCheck
      omega
  let rootGs := st.groups.filter (fun g => decide (0 < g.maplen))
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
  let empRootGs := rootGs.filter GroupDesc.isEmpty
  let nonEmpRootGs := rootGs.filter (fun g => !GroupDesc.isEmpty g)
  have hRootSplit :
      (rootGs.map fun g => g.maplen * 4096).sum =
      (empRootGs.map fun g => g.maplen * 4096).sum +
      (nonEmpRootGs.map fun g => g.maplen * 4096).sum :=
    accounting_sum_filter_partition GroupDesc.isEmpty (fun g => g.maplen * 4096) rootGs
  have hEmpNd : (empRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hEmpRootBytes : (empRootGs.map fun g => g.maplen * 4096).sum ≤ 14876672 := by
    let empSmall := empRootGs.filter (fun g => decide (g.sc ≤ 25))
    let empMed := empRootGs.filter (fun g => !decide (g.sc ≤ 25))
    have hSplitEmp := accounting_sum_filter_partition (fun g => decide (g.sc ≤ 25))
      (fun g => g.maplen * 4096) empRootGs
    have hSmallNd : (empSmall.map (·.metaPtr)).Nodup :=
      ((List.filter_sublist).map _).nodup hEmpNd
    have hMedNd : (empMed.map (·.metaPtr)).Nodup :=
      ((List.filter_sublist).map _).nodup hEmpNd
    have hSmallLen : empSmall.length ≤ 19 :=
      empGs_range_length_le hwf empSmall 7 19 hSmallNd
        (fun g hg => by
          have ⟨hgEmp, _⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          exact ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
        (fun g hg => by
          have ⟨hgEmp, hLe25B⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          have hLe25 : g.sc ≤ 25 := of_decide_eq_true hLe25B
          have ⟨_, hGe7, _⟩ := hwf.empty_groups_bound g (List.mem_filter.mp hgRoot).1 hE
          omega)
    have hMedLen : empMed.length ≤ 13 :=
      empGs_range_length_le hwf empMed 26 13 hMedNd
        (fun g hg => by
          have ⟨hgEmp, _⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          exact ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
        (fun g hg => by
          have ⟨hgEmp, hGt25B⟩ := List.mem_filter.mp hg
          have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
          have hNotLe25 : ¬ (g.sc ≤ 25) := of_decide_eq_false (by simpa using hGt25B)
          have ⟨_, _, hLe38, _⟩ := hwf.empty_groups_bound g (List.mem_filter.mp hgRoot).1 hE
          omega)
    have hSmallEach : ∀ g ∈ empSmall, g.maplen * 4096 ≤ 65536 := by
      intro g hg
      have ⟨hgEmp, hLe25B⟩ := List.mem_filter.mp hg
      have ⟨hgRoot, _⟩ := List.mem_filter.mp hgEmp
      have ⟨hgIn, hMapPosB⟩ := List.mem_filter.mp hgRoot
      exact ((hwf.groups_wf g hgIn).2.2.2.2.2.2.2.2.2.2.2.1 (of_decide_eq_true hMapPosB)).2.2.1
        (of_decide_eq_true hLe25B)
    have hMedEach : ∀ g ∈ empMed, g.maplen * 4096 ≤ 1048576 := by
      intro g hg
      have ⟨hgEmp, _⟩ := List.mem_filter.mp hg
      have ⟨hgRoot, hE⟩ := List.mem_filter.mp hgEmp
      exact (hwf.empty_groups_bound g (List.mem_filter.mp hgRoot).1 hE).2.2.2.1
    have hSmallSum := sum_const_bound hSmallEach
    have hMedSum := sum_const_bound hMedEach
    dsimp only [empSmall, empMed] at hSmallLen hMedLen hSmallSum hMedSum
    omega
  let rootMeta : GroupDesc → BitVec 64 := fun g => iterParentMeta st 7 g.metaPtr
  let groupWeightTight : GroupDesc → Nat :=
    fun g => (g.slots.map slotEffCost).sum + 1048576 * (g.slots.map slotLiveCount).sum
  have hClaim0 : totalClaimedSlots st = 0 := by
    have h0 := hwf.inflight_wf; omega
  have hEachNonEmp : ∀ g ∈ nonEmpRootGs,
      g.maplen * 4096 ≤
        ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map groupWeightTight).sum := by
    intro g hg
    have ⟨hgRoot, hgNotEB⟩ := List.mem_filter.mp hg
    have ⟨hgIn, hgMapPosB⟩ := List.mem_filter.mp hgRoot
    have hgMapPos : 0 < g.maplen := of_decide_eq_true hgMapPosB
    have hgNotE : g.isEmpty = false := by simpa using hgNotEB
    have hGWf := hwf.groups_wf g hgIn
    have hParNone : g.parentMeta = none := hGWf.2.2.2.2.2.2.2.2.2.2.1.mp hgMapPos
    have hFixG : parentMetaStep st g.metaPtr = g.metaPtr := by
      simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hgIn, hParNone]
    obtain ⟨leaf, hleaf, d, hdLt8, hLeafDir, hIterD, hGe25Eq⟩ :=
      descend_nonempty_group hwf hgIn hgNotE
    have hRootEq : rootMeta leaf = g.metaPtr := by
      show iterParentMeta st 7 leaf.metaPtr = g.metaPtr
      have hdEq : 7 = d + (7 - d) := by omega
      rw [hdEq, iterParentMeta_add, hIterD]
      exact iterParentMeta_fixed hFixG (7 - d)
    unfold GroupDesc.hasDirectLeaf at hLeafDir
    obtain ⟨s, hsMem, hsDir⟩ := List.any_eq_true.mp hLeafDir
    obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
    have hsNotClaimed := no_claimed_slot_of_zero hClaim0 hleaf hsMem
    rcases hS : s with _ | _ | _ | cm | ⟨userPtr, reqSize, effCost⟩
    · simp [hS] at hsDir
    · simp [hS] at hsDir
    · exact False.elim (hsNotClaimed hS)
    · simp [hS] at hsDir
    · have hSlotEq : leaf.slots[idx]'hIdx = .liveUser userPtr reqSize effCost := hEqS.trans hS
      have hLeafSWf := (hwf.groups_wf leaf hleaf).slot_wf idx hIdx
      rw [hSlotEq] at hLeafSWf
      have hBytesLeTight : g.maplen * 4096 ≤ effCost + 1048576 := by
        rcases hGWf.1 with hScLt48 | hSc63
        · have hLe1M := (hGWf.2.2.2.2.2.2.2.2.2.2.2.1 hgMapPos).2.2.2 hScLt48
          omega
        · have ⟨_, hLeafEqG⟩ := hGe25Eq (by omega)
          subst hLeafEqG
          have h63Le := hLeafSWf.2.2.2.2.2.2.2.2.2.2.2.1 hSc63
          omega
      have hEffInLeaf : effCost ≤ (leaf.slots.map slotEffCost).sum := by
        have hMemC : effCost ∈ leaf.slots.map slotEffCost := by
          rw [hS] at hsMem
          exact List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩
        exact accounting_le_sum_of_mem hMemC
      have hCntInLeaf : 1 ≤ (leaf.slots.map slotLiveCount).sum := by
        have hMemN : 1 ∈ leaf.slots.map slotLiveCount := by
          rw [hS] at hsMem
          exact List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩
        exact accounting_le_sum_of_mem hMemN
      have hLeafInFiber : groupWeightTight leaf ∈
          (st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map groupWeightTight :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨hleaf, beq_iff_eq.mpr hRootEq⟩)
      have hWeightInFiber : groupWeightTight leaf ≤
          ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map groupWeightTight).sum :=
        accounting_le_sum_of_mem hLeafInFiber
      have hWLeaf : groupWeightTight leaf =
          (leaf.slots.map slotEffCost).sum + 1048576 * (leaf.slots.map slotLiveCount).sum := rfl
      have hW1 : g.maplen * 4096 ≤ groupWeightTight leaf := by
        clear hGWf hLeafSWf hGe25Eq
        rw [hWLeaf]; omega
      exact Nat.le_trans hW1 hWeightInFiber
  have hNonEmpMetaNd : (nonEmpRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hFiberBound :
      (nonEmpRootGs.map fun g =>
        ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map groupWeightTight).sum).sum ≤
      (st.groups.map groupWeightTight).sum := by
    have hMapEq :
        (nonEmpRootGs.map fun g =>
          ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map groupWeightTight).sum) =
        ((nonEmpRootGs.map (·.metaPtr)).map fun m =>
          ((st.groups.filter fun h0 => rootMeta h0 == m).map groupWeightTight).sum) := by
      rw [List.map_map]; rfl
    rw [hMapEq]
    exact sum_filter_beq_le_of_nodup rootMeta groupWeightTight st.groups hNonEmpMetaNd
  have hWeightTotal :
      (st.groups.map groupWeightTight).sum = totalLiveEffCost st + 1048576 * totalLiveCount st := by
    unfold totalLiveEffCost totalLiveCount
    dsimp only [groupWeightTight]
    clear hFiberBound hEachNonEmp
    induction st.groups with
    | nil => rfl
    | cons g0 rest ih => simp [ih]; omega
  have hEffLe : totalLiveEffCost st ≤ b.liveCost := hwf.effCost_le_live
  have hNonEmpBytesLe :
      (nonEmpRootGs.map fun g => g.maplen * 4096).sum ≤ b.liveCost + 1048576 * b.liveCount := by
    have h1 := accounting_sum_map_le hEachNonEmp
    omega
  exact ⟨⟨hLiveLePeak, hCountLePeak⟩, hIvsLen, by rw [hIvsEq]; omega⟩

end VerifiedLibraries.Mallocng.Proofs
