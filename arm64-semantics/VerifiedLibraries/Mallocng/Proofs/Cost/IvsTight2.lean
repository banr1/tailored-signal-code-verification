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
# Usage-Indexed Tight `ivs` Byte-Sum Bound

Proves `mallocngHeap_ivs_tight2_bound` and `emptyRoot_sum_le_keptSum`, refining
`mallocngHeap_ivs_tight_bound` via the `GroupsGrpBound (peakCount + 6)` invariant from
`MallocngCountIvsWF`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 ProofLib VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

private def checkMetaShiftBound2 : Bool :=
  (List.range 41).all fun m =>
    if 1 ≤ m then (m + 1) + (2 ^ (m + 1) - 2) ≤ 5 * (2 ^ m - m) + 4 else true

private theorem checkMetaShiftBound2_true : checkMetaShiftBound2 = true := by
  decide +kernel

section
variable {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}

theorem pages_tight_le (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {pc : Nat} (hMetaCount : st.metaAreas.length ≤ 1 + (88 + 8 * pc) / 101) :
    st.metaAreas.length + st.guardPages.length + st.availMetaPages.length ≤
      10 + 6 * ((88 + 8 * pc) / 101) := by
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
    have hCheck := List.all_eq_true.mp checkMetaShiftBound2_true st.ctx.metaAllocShift.toNat
      (List.mem_range.mpr (by omega))
    simp only [hPos, ↓reduceIte, decide_eq_true_eq] at hCheck
    omega

end

private theorem sum_nodup_le_range48 (w : Nat → Nat) {ys : List Nat} (hnd : ys.Nodup)
    (hlt : ∀ y ∈ ys, y < 48) :
    (ys.map w).sum ≤ ((List.range 48).map w).sum := by
  have hFib := sum_filter_beq_le_of_nodup (fun x : Nat => x) w (List.range 48) hnd
  refine Nat.le_trans (accounting_sum_map_le fun y hy => ?_) hFib
  have hMem : w y ∈ ((List.range 48).filter fun x => x == y).map w :=
    List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨List.mem_range.mpr (hlt y hy), by simp⟩, rfl⟩
  exact accounting_le_sum_of_mem hMem

theorem emptyRoot_sum_le_keptSum {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {U : Nat} (hB : GroupsGrpBound U st.groups) (es : List GroupDesc)
    (hMetaNd : (es.map (·.metaPtr)).Nodup)
    (hAllEmp : ∀ g ∈ es, g ∈ st.groups ∧ g.isEmpty = true) :
    (es.map fun g => g.maplen * 4096).sum ≤ keptSum U := by
  have hScNd := empGs_sc_nodup hwf es hMetaNd hAllEmp
  have hEach : ∀ g ∈ es, g.maplen * 4096 ≤ keptMax g.sc U := by
    intro g hg
    have ⟨hgIn, hE⟩ := hAllEmp g hg
    have ⟨hPos, hGe7, hLe38, _⟩ := hwf.empty_groups_bound g hgIn hE
    have hLe := hB g hgIn hPos (by omega)
    unfold keptMax; simp only [hGe7, hLe38, and_self, ↓reduceIte]; exact hLe
  have h1 := accounting_sum_map_le hEach
  have hMapEq : (es.map fun g => keptMax g.sc U) = (es.map (·.sc)).map (keptMax · U) := by
    rw [List.map_map]; rfl
  rw [hMapEq] at h1
  refine Nat.le_trans h1 (sum_nodup_le_range48 (keptMax · U) hScNd ?_)
  intro y hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
  have ⟨hgIn, hE⟩ := hAllEmp g hg
  have ⟨_, _, hLe38, _⟩ := hwf.empty_groups_bound g hgIn hE
  omega

private theorem holds_sepConj_right2 {P Q : SepProp} {h : Heap}
    (hh : (P ∗ Q).holds h) : ∃ h₂, Q.holds h₂ := by
  rw [sepConj_comm] at hh
  exact SepProp.holds_sepConj_left hh

private theorem no_claimed_slot_of_zero2 {st : MallocngSt} (h0 : totalClaimedSlots st = 0)
    {g : GroupDesc} (hg : g ∈ st.groups) {s : SlotState} (hs : s ∈ g.slots) :
    s ≠ .claimed := by
  intro hEq
  have hMemF : s ∈ g.slots.filter SlotState.isClaimed :=
    List.mem_filter.mpr ⟨hs, by simp [hEq, SlotState.isClaimed]⟩
  have hPos : 1 ≤ (g.slots.filter SlotState.isClaimed).length := List.length_pos_of_mem hMemF
  have hLe := accounting_le_sum_of_mem
    (List.mem_map_of_mem (f := fun h => (h.slots.filter SlotState.isClaimed).length) hg)
  unfold totalClaimedSlots at h0
  omega

private theorem sum_snd_const2 {α : Type} (f : α → BitVec 64) (c : Nat) (xs : List α) :
    ((xs.map fun x => (f x, c)).map Prod.snd).sum = c * xs.length := by
  induction xs with
  | nil => simp
  | cons _ rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.mul_succ, Nat.add_comm]

private theorem nonEmpRoot_le_fiber {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} (hwf : MallocngWFInflight 0 base brkStart brk liveCost peakCost st)
    {U G : Nat} (hB : GroupsGrpBound U st.groups) (hG : ∀ sc < 48, grpMax sc U ≤ G)
    (hG63 : 8195 ≤ G) {g : GroupDesc} (hgIn : g ∈ st.groups) (hgMapPos : 0 < g.maplen)
    (hgNotE : g.isEmpty = false) :
    g.maplen * 4096 ≤
      ((st.groups.filter fun h0 => iterParentMeta st 7 h0.metaPtr == g.metaPtr).map
        fun g => (g.slots.map slotEffCost).sum + G * (g.slots.map slotLiveCount).sum).sum := by
  have hClaim0 : totalClaimedSlots st = 0 := by have h0 := hwf.inflight_wf; omega
  have hGWf := hwf.groups_wf g hgIn
  have hParNone : g.parentMeta = none := hGWf.2.2.2.2.2.2.2.2.2.2.1.mp hgMapPos
  have hFixG : parentMetaStep st g.metaPtr = g.metaPtr := by
    simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hgIn, hParNone]
  obtain ⟨leaf, hleaf, d, hdLt8, hLeafDir, hIterD, hGe25Eq⟩ := descend_nonempty_group hwf hgIn hgNotE
  have hRootEq : iterParentMeta st 7 leaf.metaPtr = g.metaPtr := by
    have hdEq : 7 = d + (7 - d) := by omega
    rw [hdEq, iterParentMeta_add, hIterD]
    exact iterParentMeta_fixed hFixG (7 - d)
  unfold GroupDesc.hasDirectLeaf at hLeafDir
  obtain ⟨s, hsMem, hsDir⟩ := List.any_eq_true.mp hLeafDir
  obtain ⟨idx, hIdx, hEqS⟩ := List.getElem_of_mem hsMem
  have hsNotClaimed := no_claimed_slot_of_zero2 hClaim0 hleaf hsMem
  rcases hS : s with _ | _ | _ | cm | ⟨userPtr, reqSize, effCost⟩
  · simp [hS] at hsDir
  · simp [hS] at hsDir
  · exact False.elim (hsNotClaimed hS)
  · simp [hS] at hsDir
  · have hSlotEq : leaf.slots[idx]'hIdx = .liveUser userPtr reqSize effCost := hEqS.trans hS
    have hLeafSWf := (hwf.groups_wf leaf hleaf).slot_wf idx hIdx
    rw [hSlotEq] at hLeafSWf
    have hBytesLe : g.maplen * 4096 ≤ effCost + G := by
      rcases hGWf.1 with hScLt48 | hSc63
      · have := hB g hgIn hgMapPos hScLt48
        have := hG g.sc hScLt48
        omega
      · have ⟨_, hLeafEqG⟩ := hGe25Eq (by omega)
        subst hLeafEqG
        have h63Le := hLeafSWf.2.2.2.2.2.2.2.2.2.2.2.1 hSc63
        omega
    rw [hS] at hsMem
    have hEffIn : effCost ≤ (leaf.slots.map slotEffCost).sum :=
      accounting_le_sum_of_mem (List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩)
    have hCntIn : 1 ≤ (leaf.slots.map slotLiveCount).sum :=
      accounting_le_sum_of_mem (List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩)
    have hGle : G ≤ G * (leaf.slots.map slotLiveCount).sum := Nat.le_mul_of_pos_right G hCntIn
    have hMemF : leaf ∈ st.groups.filter fun h0 => iterParentMeta st 7 h0.metaPtr == g.metaPtr :=
      List.mem_filter.mpr ⟨hleaf, beq_iff_eq.mpr hRootEq⟩
    have hInFib := accounting_le_sum_of_mem (List.mem_map_of_mem
      (f := fun g => (g.slots.map slotEffCost).sum + G * (g.slots.map slotLiveCount).sum) hMemF)
    omega

/-- Usage-indexed `ivs` byte-sum bound for `mallocngIface.MallocngHeap` (`pc = b.peakCount`):
    `(ivs.map Prod.snd).sum <= keptSum (pc + 6) + 24576 * ((88 + 8 * pc) / 101) + 40960 + grpMaxAll (pc + 6) * b.liveCount + b.liveCost`. -/
theorem mallocngHeap_ivs_tight2_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngIface.MallocngHeap γ A tp brkStart brk b ivs) h) :
    (b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
    ivs.length ≤ 48 + 2 * b.peakCount ∧
    (ivs.map Prod.snd).sum ≤
      keptSum (b.peakCount + 6) + 24576 * ((88 + 8 * b.peakCount) / 101) + 40960 +
        grpMaxAll (b.peakCount + 6) * b.liveCount + b.liveCost := by
  have hHoldsIv : (MallocngHeapImpl γ A tp brkStart brk b ivs).holds h := hHolds
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq] at hHoldsIv
  unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState MallocngRuntime at hHoldsIv
  simp only [sepExists_sepConj_left, sepExists_sepConj_right] at hHoldsIv
  obtain ⟨_errnoVal, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
  obtain ⟨st, hHoldsIv⟩ := SepProp.holds_sepExists hHoldsIv
  obtain ⟨_, hCoreH⟩ := SepProp.holds_sepConj_left hHoldsIv
  obtain ⟨_, hStH0⟩ := holds_sepConj_right2 hCoreH
  obtain ⟨hCountIvs, hStH⟩ := SepProp.holds_pure_sepConj hStH0
  obtain ⟨hwf, _⟩ := SepProp.holds_pure_sepConj hStH
  obtain ⟨hCountLePeak, hLiveCountLe, hIvsEq, hIvsLen, hMetaCount, hB⟩ := hCountIvs
  have hLiveLePeak : b.liveCost ≤ b.peakCost := hwf.live_le_peak
  have hPages := pages_tight_le hwf hMetaCount
  let U := b.peakCount + 6
  let G := grpMaxAll U
  let rootGs := st.groups.filter (fun g => decide (0 < g.maplen))
  have hDynSum :
      ((dynamicRootRegions st).map Prod.snd).sum =
      4096 * (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length) +
      (rootGs.map fun g => g.maplen * 4096).sum := by
    unfold dynamicRootRegions
    simp only [List.map_append, List.sum_append, sum_snd_const2]
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
  have hEmpBytes : (empRootGs.map fun g => g.maplen * 4096).sum ≤ keptSum U :=
    emptyRoot_sum_le_keptSum hwf hB empRootGs hEmpNd (fun g hg => by
      have ⟨hgRoot, hE⟩ := List.mem_filter.mp hg
      exact ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
  let rootMeta : GroupDesc → BitVec 64 := fun g => iterParentMeta st 7 g.metaPtr
  let w : GroupDesc → Nat :=
    fun g => (g.slots.map slotEffCost).sum + G * (g.slots.map slotLiveCount).sum
  have hEachNonEmp : ∀ g ∈ nonEmpRootGs,
      g.maplen * 4096 ≤ ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map w).sum := by
    intro g hg
    have ⟨hgRoot, hgNotEB⟩ := List.mem_filter.mp hg
    have ⟨hgIn, hgMapPosB⟩ := List.mem_filter.mp hgRoot
    exact nonEmpRoot_le_fiber hwf hB (fun sc hsc => grpMax_le_grpMaxAll hsc U) (grpMaxAll_ge U)
      hgIn (of_decide_eq_true hgMapPosB) (by simpa using hgNotEB)
  have hNonEmpMetaNd : (nonEmpRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hFiberBound :
      (nonEmpRootGs.map fun g => ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map w).sum).sum ≤
      (st.groups.map w).sum := by
    have hMapEq :
        (nonEmpRootGs.map fun g => ((st.groups.filter fun h0 => rootMeta h0 == g.metaPtr).map w).sum) =
        ((nonEmpRootGs.map (·.metaPtr)).map fun m =>
          ((st.groups.filter fun h0 => rootMeta h0 == m).map w).sum) := by
      rw [List.map_map]; rfl
    rw [hMapEq]
    exact sum_filter_beq_le_of_nodup rootMeta w st.groups hNonEmpMetaNd
  have hWeightTotal : (st.groups.map w).sum = totalLiveEffCost st + G * totalLiveCount st := by
    unfold totalLiveEffCost totalLiveCount
    dsimp only [w]
    clear hFiberBound hEachNonEmp
    induction st.groups with
    | nil => rfl
    | cons g0 rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]; omega
  have hEffLe : totalLiveEffCost st ≤ b.liveCost := hwf.effCost_le_live
  have hGCnt : G * totalLiveCount st ≤ G * b.liveCount := Nat.mul_le_mul_left G hLiveCountLe
  have h1 := accounting_sum_map_le hEachNonEmp
  refine ⟨⟨hLiveLePeak, hCountLePeak⟩, hIvsLen, ?_⟩
  rw [hIvsEq, hDynSum]
  change _ ≤ keptSum U + _ + _ + G * b.liveCount + _
  omega

end VerifiedLibraries.Mallocng.Proofs.Cost
