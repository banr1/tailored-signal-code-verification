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
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers

/-!
# Invariant and Accounting Helpers for Placed `__libc_realloc`

Pure `MallocngWF`, `MallocngCountIvsWF`, `MallocngMappedDelta`, `MallocngNoOrphanMappings`,
`ByteMap` slot fusion and re-splitting, and ghost-token `|==>` helpers for `__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Mapped-delta, orphan-mapping, and budget composition -/

theorem mappedDelta_zero_imp_mapped {m0 m1 : Memory}
    (h0 : MallocngMappedDelta 0 0 m0 m1) {a : BitVec 64}
    (hm : (m1.perm a).mapped = true) : (m0.perm a).mapped = true := by
  obtain ⟨ivs, hLen, _, hCov⟩ := h0
  rcases hCov a hm with hOk | ⟨iv, hiv, _⟩
  · exact hOk
  · cases ivs with
    | nil => cases hiv
    | cons _ _ => simp at hLen

theorem mappedDelta_zero_trans_left {k B : Nat} {m0 m1 m2 : Memory}
    (h01 : MallocngMappedDelta 0 0 m0 m1)
    (h12 : MallocngMappedDelta k B m1 m2) :
    MallocngMappedDelta k B m0 m2 := by
  obtain ⟨ivs, hLen, hSum, hCov⟩ := h12
  refine ⟨ivs, hLen, hSum, fun a hm => ?_⟩
  rcases hCov a hm with hm1 | hIn
  · exact Or.inl (mappedDelta_zero_imp_mapped h01 hm1)
  · exact Or.inr hIn

theorem mappedDelta_trans_zero_right {k B : Nat} {m0 m1 m2 : Memory}
    (h01 : MallocngMappedDelta k B m0 m1)
    (h12 : MallocngMappedDelta 0 0 m1 m2) :
    MallocngMappedDelta k B m0 m2 := by
  obtain ⟨ivs, hLen, hSum, hCov⟩ := h01
  exact ⟨ivs, hLen, hSum, fun a hm => hCov a (mappedDelta_zero_imp_mapped h12 hm)⟩

theorem mappedDelta_mono_bounds {k1 k2 B1 B2 : Nat} {m0 m1 : Memory}
    (hk : k1 ≤ k2) (hB : B1 ≤ B2)
    (h : MallocngMappedDelta k1 B1 m0 m1) :
    MallocngMappedDelta k2 B2 m0 m1 := by
  obtain ⟨ivs, hLen, hSum, hCov⟩ := h
  exact ⟨ivs, Nat.le_trans hLen hk, Nat.le_trans hSum hB, hCov⟩

theorem noOrphanMappings_refl_of_delta_zero {ivs : List (BitVec 64 × Nat)} {m0 m1 : Memory}
    (h01 : MallocngMappedDelta 0 0 m0 m1) :
    MallocngNoOrphanMappings ivs ivs m0 m1 := by
  intro a hm1 hOr
  rcases hOr with hm0False | hIn
  · exfalso
    rw [mappedDelta_zero_imp_mapped h01 hm1] at hm0False
    cases hm0False
  · exact hIn

theorem noOrphanMappings_of_delta_zero_left {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m1 mf : Memory}
    (h01 : MallocngMappedDelta 0 0 m0 m1)
    (h1f : MallocngNoOrphanMappings ivs0 ivsf m1 mf) :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  intro a hmf hOr
  refine h1f a hmf ?_
  rcases hOr with hm0False | hIn
  · left
    cases h1 : (m1.perm a).mapped with
    | false => rfl
    | true =>
      rw [mappedDelta_zero_imp_mapped h01 h1] at hm0False
      cases hm0False
  · exact Or.inr hIn

theorem noOrphanMappings_of_perm_eq_right {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 m1 m2 : Memory}
    (h01 : MallocngNoOrphanMappings ivs0 ivsf m0 m1)
    (hPerm : m2.perm = m1.perm) :
    MallocngNoOrphanMappings ivs0 ivsf m0 m2 := by
  intro a hm2 hOr
  rw [hPerm] at hm2
  exact h01 a hm2 hOr

theorem noOrphanMappings_chain_alloc_free {ivs0 ivs1 ivs2 : List (BitVec 64 × Nat)}
    {m0 m1 m2 m3 : Memory}
    (h01 : MallocngNoOrphanMappings ivs0 ivs1 m0 m1)
    (hPerm12 : m2.perm = m1.perm)
    (hDelta23 : MallocngMappedDelta 0 0 m2 m3)
    (h23 : MallocngNoOrphanMappings ivs1 ivs2 m2 m3) :
    MallocngNoOrphanMappings ivs0 ivs2 m0 m3 := by
  intro a hm3 hOr
  have hm2 : (m2.perm a).mapped = true := mappedDelta_zero_imp_mapped hDelta23 hm3
  have hm1 : (m1.perm a).mapped = true := by rw [← hPerm12]; exact hm2
  have hIn1 : MallocngInIntervals ivs1 a := h01 a hm1 hOr
  exact h23 a hm3 (Or.inr hIn1)

theorem realloc_outOfPlace_budget_eq (oldSz newSz : Nat) (oldBs : List (BitVec 8))
    (b : MallocngBudget)
    (hOldLe : max oldSz MallocngMinBlockCost ≤ b.liveCost) :
    mallocngFreeBudget false oldSz (mallocngAllocBudget true newSz b) =
      mallocngReallocBudget true (some (oldSz, oldBs)) newSz b := by
  simp only [mallocngFreeBudget, mallocngAllocBudget, mallocngReallocBudget,
    MallocngMinBlockCost, Bool.false_eq_true, ↓reduceIte] at hOldLe ⊢
  congr 1 <;> omega

/-! ## Live-slot lookup and accounting bounds -/

theorem list_sum_ge_of_mem {xs : List Nat} {x : Nat} (hx : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hMem
    · omega
    · have := ih hMem; omega

theorem liveUser_cost_count_le_totals {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff) :
    oldEff ≤ totalLiveEffCost st ∧ 1 ≤ totalLiveCount st := by
  have hMemSlot : SlotState.liveUser p oldSz oldEff ∈ g.slots := by
    rw [← hSlot]; exact List.getElem_mem hIdx
  have hEffG : oldEff ≤ (g.slots.map slotEffCost).sum :=
    list_sum_ge_of_mem (x := slotEffCost (.liveUser p oldSz oldEff))
      (List.mem_map_of_mem hMemSlot)
  have hEffTot : (g.slots.map slotEffCost).sum ≤ totalLiveEffCost st :=
    list_sum_ge_of_mem (List.mem_map_of_mem hg)
  have hCntG : 1 ≤ (g.slots.map slotLiveCount).sum :=
    list_sum_ge_of_mem (x := slotLiveCount (.liveUser p oldSz oldEff))
      (List.mem_map_of_mem hMemSlot)
  have hCntTot : (g.slots.map slotLiveCount).sum ≤ totalLiveCount st :=
    list_sum_ge_of_mem (List.mem_map_of_mem hg)
  exact ⟨Nat.le_trans hEffG hEffTot, Nat.le_trans hCntG hCntTot⟩

theorem realloc_live_slot_info {γ : GhostName} {base brkStart brk : BitVec 64}
    {b : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)} {st : MallocngSt}
    {p : BitVec 64} {oldSz : Nat} {m : Memory} {R : SepProp}
    (hCount : MallocngCountIvsWF b ivs0 st)
    (hwf : MallocngWF base brkStart brk b.liveCost b.peakCost st)
    (hMem : m ⊨ MallocngLiveAuth γ st.liveMap ∗ mallocngIface.Block γ p oldSz ∗ R) :
    st.liveMap p = some oldSz ∧
    st.reservedMetas = [] ∧
    max oldSz MallocngMinBlockCost ≤ b.liveCost ∧
    1 ≤ b.liveCount ∧
    ∃ g ∈ st.groups, ∃ idx : Nat, ∃ hIdx : idx < g.slots.length, ∃ oldEff : Nat,
      g.slots[idx]'hIdx = .liveUser p oldSz oldEff := by
  have hNoRes : st.reservedMetas = [] := by
    have hInf := hwf.inflight_wf
    cases hL : st.reservedMetas with
    | nil => rfl
    | cons _ _ => simp [hL] at hInf
  have hAuthPt : m ⊨ (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p oldSz) ∗ R := by
    show m ⊨ (MallocngLiveAuth γ st.liveMap ∗ mallocngIface.Block γ p oldSz) ∗ R
    rw [sepConj_assoc]; exact hMem
  have hLookup : st.liveMap p = some oldSz := by
    have hPure := Satisfies.mono (sepConj_mono_left (mallocngBlock_lookup γ st.liveMap p oldSz)) hAuthPt
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hPure
    exact hPure.1.2
  obtain ⟨g, hg, idx, hIdx, oldEff, hSlot⟩ := (hwf.liveMap_wf p oldSz).mp hLookup
  obtain ⟨hEffLeTot, hCntGe1⟩ := liveUser_cost_count_le_totals hg hIdx hSlot
  have hSWf := (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  rw [hSlot] at hSWf
  have hMaxLeEff : max oldSz MallocngMinBlockCost ≤ oldEff := hSWf.2.2.2.2.2.2.2.1
  have hEffLeLive : totalLiveEffCost st ≤ b.liveCost := hwf.effCost_le_live
  have hCntLeLive : totalLiveCount st ≤ b.liveCount := hCount.2.1
  exact ⟨hLookup, hNoRes, by omega, by omega, g, hg, idx, hIdx, oldEff, hSlot⟩

/-! ## Group replacement and slot-list helpers -/

def replaceGroup (gs : List GroupDesc) (m : BitVec 64) (g' : GroupDesc) : List GroupDesc :=
  gs.map fun x => if x.metaPtr == m then g' else x

theorem replaceGroup_id_of_ne (gs : List GroupDesc) (m : BitVec 64) (g' : GroupDesc)
    (hNe : ∀ y ∈ gs, y.metaPtr ≠ m) :
    replaceGroup gs m g' = gs := by
  induction gs with
  | nil => rfl
  | cons hd tl ih =>
    have h1 : (hd.metaPtr == m) = false := beq_false_of_ne (hNe hd List.mem_cons_self)
    have h2 : replaceGroup tl m g' = tl := ih fun y hy => hNe y (List.mem_cons_of_mem _ hy)
    show (if (hd.metaPtr == m) = true then g' else hd) :: replaceGroup tl m g' = hd :: tl
    rw [h1, h2]; rfl

theorem replaceGroup_props (gs : List GroupDesc) (g g' : GroupDesc)
    (hg : g ∈ gs) (hNodup : (gs.map (·.metaPtr)).Nodup)
    (hMetaEq : g'.metaPtr = g.metaPtr) :
    g' ∈ replaceGroup gs g.metaPtr g' ∧
    (∀ x ∈ replaceGroup gs g.metaPtr g', (x = g' ∨ (x.metaPtr ≠ g.metaPtr ∧ x ∈ gs))) ∧
    (∀ x ∈ gs, x.metaPtr ≠ g.metaPtr → x ∈ replaceGroup gs g.metaPtr g') ∧
    (replaceGroup gs g.metaPtr g').map (·.metaPtr) = gs.map (·.metaPtr) ∧
    (findGroupByMeta { emptyMallocngSt 0#64 with groups := replaceGroup gs g.metaPtr g' } g.metaPtr = some g') ∧
    (∀ m, m ≠ g.metaPtr →
      (replaceGroup gs g.metaPtr g').find? (·.metaPtr == m) = gs.find? (·.metaPtr == m)) := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hg with hEqHd | hMemTl
    · subst hd
      have hNotInTl : ∀ y ∈ tl, y.metaPtr ≠ g.metaPtr :=
        fun y hy hE => hNodup.1 (hE ▸ List.mem_map_of_mem hy)
      have hTlId : replaceGroup tl g.metaPtr g' = tl := replaceGroup_id_of_ne tl g.metaPtr g' hNotInTl
      have hCons : replaceGroup (g :: tl) g.metaPtr g' = g' :: tl := by
        show (if (g.metaPtr == g.metaPtr) = true then g' else g) :: replaceGroup tl g.metaPtr g' = g' :: tl
        rw [BEq.rfl, hTlId]; rfl
      rw [hCons]
      refine ⟨List.mem_cons_self, ?_, ?_, by simp [hMetaEq], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxTl
        · exact Or.inl rfl
        · exact Or.inr ⟨hNotInTl x hxTl, List.mem_cons_of_mem _ hxTl⟩
      · intro x hx hNe
        rcases List.mem_cons.mp hx with rfl | hxTl
        · exact absurd rfl hNe
        · exact List.mem_cons_of_mem _ hxTl
      · simp [findGroupByMeta, hMetaEq]
      · intro m hmNe
        have hFalse1 : (g'.metaPtr == m) = false :=
          beq_false_of_ne fun h => hmNe (h.symm.trans hMetaEq)
        have hFalse2 : (g.metaPtr == m) = false := beq_false_of_ne hmNe.symm
        simp only [List.find?_cons, hFalse1, hFalse2]
    · have hHdNe : hd.metaPtr ≠ g.metaPtr :=
        fun hE => hNodup.1 (hE ▸ List.mem_map_of_mem hMemTl)
      have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
        rw [beq_false_of_ne hHdNe]; rfl
      obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ := ih hMemTl hNodup.2
      rw [hCons]
      refine ⟨List.mem_cons_of_mem _ ih1, ?_, ?_, congrArg (hd.metaPtr :: ·) ih4, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hxTl
        · exact Or.inr ⟨hHdNe, List.mem_cons_self⟩
        · rcases ih2 x hxTl with rfl | ⟨hNe, hxIn⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hNe, List.mem_cons_of_mem _ hxIn⟩
      · intro x hx hNe
        rcases List.mem_cons.mp hx with rfl | hxTl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih3 x hxTl hNe)
      · simp [findGroupByMeta, beq_false_of_ne hHdNe]; exact ih5
      · intro m hmNe
        simp only [List.find?_cons]
        cases (hd.metaPtr == m)
        · exact ih6 m hmNe
        · rfl

theorem replaceGroup_sum_eq (gs : List GroupDesc) (g g' : GroupDesc)
    (hg : g ∈ gs) (hNodup : (gs.map (·.metaPtr)).Nodup) (f : GroupDesc → Nat) :
    ((replaceGroup gs g.metaPtr g').map f).sum + f g = (gs.map f).sum + f g' := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hg with hEqHd | hMemTl
    · subst hd
      have hTlId : replaceGroup tl g.metaPtr g' = tl :=
        replaceGroup_id_of_ne tl g.metaPtr g' fun y hy hE => hNodup.1 (hE ▸ List.mem_map_of_mem hy)
      have hCons : replaceGroup (g :: tl) g.metaPtr g' = g' :: tl := by
        show (if (g.metaPtr == g.metaPtr) = true then g' else g) :: replaceGroup tl g.metaPtr g' = g' :: tl
        rw [BEq.rfl, hTlId]; rfl
      rw [hCons]; simp only [List.map_cons, List.sum_cons]; omega
    · have hHdNe : hd.metaPtr ≠ g.metaPtr :=
        fun hE => hNodup.1 (hE ▸ List.mem_map_of_mem hMemTl)
      have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
        rw [beq_false_of_ne hHdNe]; rfl
      have hSpec := ih hMemTl hNodup.2
      rw [hCons]; simp only [List.map_cons, List.sum_cons]; omega

theorem replaceGroup_filter_sc_cnt_sum (gs : List GroupDesc) (g g' : GroupDesc)
    (hg : g ∈ gs) (hNodup : (gs.map (·.metaPtr)).Nodup)
    (hSc : g'.sc = g.sc) (hCnt : g'.cnt = g.cnt) (sc : Nat) :
    (((replaceGroup gs g.metaPtr g').filter (·.sc == sc)).map GroupDesc.cnt).sum =
      ((gs.filter (·.sc == sc)).map GroupDesc.cnt).sum := by
  have hMapEq : ((replaceGroup gs g.metaPtr g').filter (·.sc == sc)).map GroupDesc.cnt =
      (gs.filter (·.sc == sc)).map GroupDesc.cnt := by
    induction gs with
    | nil => cases hg
    | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hNodup
      rcases List.mem_cons.mp hg with hEqHd | hMemTl
      · subst hd
        have hTlId : replaceGroup tl g.metaPtr g' = tl :=
          replaceGroup_id_of_ne tl g.metaPtr g' fun y hy hE => hNodup.1 (hE ▸ List.mem_map_of_mem hy)
        have hCons : replaceGroup (g :: tl) g.metaPtr g' = g' :: tl := by
          show (if (g.metaPtr == g.metaPtr) = true then g' else g) :: replaceGroup tl g.metaPtr g' = g' :: tl
          rw [BEq.rfl, hTlId]; rfl
        rw [hCons, List.filter_cons, List.filter_cons, hSc]
        cases (g.sc == sc) <;> simp [hCnt]
      · have hHdNe : hd.metaPtr ≠ g.metaPtr :=
          fun hE => hNodup.1 (hE ▸ List.mem_map_of_mem hMemTl)
        have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
          show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
          rw [beq_false_of_ne hHdNe]; rfl
        rw [hCons, List.filter_cons, List.filter_cons]
        cases (hd.sc == sc) <;> simp [ih hMemTl hNodup.2]
  rw [hMapEq]

/-! ## In-place `liveUser` slot-slice fusion and `set_size` well-formedness -/

theorem list_set_liveUser_props (xs : List SlotState) (idx : Nat) (hIdx : idx < xs.length)
    (p1 p2 : BitVec 64) (sz1 eff1 sz2 eff2 : Nat)
    (hOld : xs[idx]'hIdx = .liveUser p1 sz1 eff1) :
    let xs' := xs.set idx (.liveUser p2 sz2 eff2)
    (xs'.filter SlotState.isClaimed).length = (xs.filter SlotState.isClaimed).length ∧
    (xs'.map slotEffCost).sum + eff1 = (xs.map slotEffCost).sum + eff2 ∧
    (xs'.map slotLiveCount).sum = (xs.map slotLiveCount).sum ∧
    xs'.all SlotState.isFree = xs.all SlotState.isFree := by
  induction xs generalizing idx with
  | nil => cases hIdx
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp only [List.getElem_cons_zero] at hOld
      subst hd
      simp [List.set_cons_zero, SlotState.isClaimed, slotEffCost, slotLiveCount, SlotState.isFree]
      omega
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hIdx
      simp only [List.getElem_cons_succ] at hOld
      obtain ⟨h1, h2, h3, h4⟩ := ih k hk hOld
      simp only [List.set_cons_succ, List.filter_cons, List.map_cons, List.sum_cons, List.all_cons]
      refine ⟨?_, by omega, by rw [h3], by rw [h4]⟩
      cases hd.isClaimed <;> simp [h1]

def mkLiveUserSlotBs (val : BitVec 64 → BitVec 8) (g : GroupDesc) (idx sz : Nat)
    (p : BitVec 64) (userBs : List (BitVec 8)) : List (BitVec 8) :=
  let start := g.slotStart idx
  let off := p.toNat - start.toNat
  readBytesFromMap val (start - 4#64) (off + 4) ++
    userBs ++
    readBytesFromMap val (p + BitVec.ofNat 64 sz) ((g.slotEnd idx).toNat - (p.toNat + sz))

theorem liveUser_slotSlice_split {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {sz eff : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p sz eff)
    (userBs : List (BitVec 8)) (hUserLen : userBs.length = sz) :
    let start := g.slotStart idx
    let slotBs := mkLiveUserSlotBs st.byteVal g idx sz p userBs
    slotBs.length = g.stride ∧
    (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ (p ↦ₛ userBs)) =
      (ByteMap st.masterDom
         (fun a => OwnedRwByte st a ∧ ¬ InRegion (start - 4#64) g.stride a) st.byteVal ∗
       ((start - 4#64) ↦ₛ slotBs)) := by
  intro start slotBs
  dsimp only [start]
  have hNoRes : st.reservedMetas = [] := by
    have hInf := hwf.inflight_wf
    cases hL : st.reservedMetas with
    | nil => rfl
    | cons _ _ => simp [hL] at hInf
  have hGWf := hwf.groups_wf g hg
  have ⟨_, _, hSt, hSub4, hEn, hEndLe, h48G, _, _⟩ := group_slot_bounds hGWf hIdx
  have ⟨hStrPos, _⟩ := group_stride_pos_and_align hGWf
  have hSWf := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  rw [hSlot] at hSWf
  have hLo : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
  have hHi : p.toNat + sz ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hLenEq : (p.toNat - (g.slotStart idx).toNat + 4) + sz +
      ((g.slotEnd idx).toNat - (p.toNat + sz)) = g.stride := by omega
  have hSlotLen : slotBs.length = g.stride := by
    simp only [slotBs, mkLiveUserSlotBs, List.length_append, readBytesFromMap_length, hUserLen]
    exact hLenEq
  obtain ⟨rg, hrg, hMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
  have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
  have hPAddSz : (p + BitVec.ofNat 64 sz).toNat = p.toNat + sz :=
    bv64_add_toNat (a := p) (n := sz) (by omega)
  have hSliceRw : ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a →
      a ∈ st.masterDom ∧ (OwnedRwByte st a ↔ ¬ InRegion p sz a) := by
    intro a ha
    have ⟨hALo, hAHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    have hInRg : InRegion rg.mem (rg.maplen * 4096) a :=
      (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    have hMapped : OwnedMappedByte st a := Or.inr (Or.inr (Or.inr ⟨rg, hrg, hMp, hInRg⟩))
    have hDom : a ∈ st.masterDom := hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMapped))
    refine ⟨hDom, ⟨fun hRw hInU => hRw.2.1 ⟨g, hg, .liveUser p sz eff, ?_, hInU⟩, fun hNotU => ?_⟩⟩
    · rw [← hSlot]; exact List.getElem_mem hIdx
    · refine ⟨Or.inr ⟨rg, hrg, hMp, hInRg⟩, ?_, by simp [CarvedMetaByte, hNoRes]⟩
      rintro ⟨g', hg', s', hs', hSub⟩
      obtain ⟨idx', hIdx', hEqS'⟩ := List.getElem_of_mem hs'
      cases hS' : s' with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS'] at hSub
      | liveUser u' r' c' =>
        simp only [hS'] at hSub
        have hSlot' : g'.slots[idx']'hIdx' = .liveUser u' r' c' := hEqS'.trans hS'
        by_cases hSame : g = g' ∧ idx = idx'
        · obtain ⟨rfl, rfl⟩ := hSame
          rw [hSlot] at hSlot'; injection hSlot' with h1 h2 _
          subst h1 h2; exact hNotU hSub
        · have hGWf' := hwf.groups_wf g' hg'
          have ⟨_, _, hSt', hSub4', hEn', _, h48', _, _⟩ := group_slot_bounds hGWf' hIdx'
          have hSWf' := hGWf'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx' hIdx'
          rw [hSlot'] at hSWf'
          have hLo' : (g'.slotStart idx').toNat ≤ u'.toNat := hSWf'.2.2.2.2.2.1
          have hHi' : u'.toNat + r' ≤ (g'.slotEnd idx').toNat := hSWf'.2.2.2.2.2.2.1
          have hSM' : (idx' + 1) * g'.stride = idx' * g'.stride + g'.stride :=
            Nat.succ_mul idx' g'.stride
          have ⟨hULo, hUHi⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
          have ha' : InRegion (g'.slotStart idx' - 4#64) g'.stride a :=
            (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
          exact nonNested_slotSlice_disjoint hwf hg hIdx (by rw [hSlot]; intro _ h; cases h)
            hg' hIdx' (by rw [hSlot']; intro _ h; cases h)
            (by by_cases hG : g = g'; exact Or.inr fun hI => hSame ⟨hG, hI⟩; exact Or.inl hG) ha ha'
  have hPreSub : ∀ a, InRegion (g.slotStart idx - 4#64) (p.toNat - (g.slotStart idx).toNat + 4) a →
      InRegion (g.slotStart idx - 4#64) g.stride a ∧ ¬ InRegion p sz a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
      fun hU => by have ⟨h3, _⟩ := (inRegion_iff_toNat (by omega) a).mp hU; omega⟩
  have hPostSub : ∀ a, InRegion (p + BitVec.ofNat 64 sz) ((g.slotEnd idx).toNat - (p.toNat + sz)) a →
      InRegion (g.slotStart idx - 4#64) g.stride a ∧ ¬ InRegion p sz a ∧
        ¬ InRegion (g.slotStart idx - 4#64) (p.toNat - (g.slotStart idx).toNat + 4) a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    refine ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
      fun hU => by have ⟨_, h4⟩ := (inRegion_iff_toNat (by omega) a).mp hU; omega,
      fun hP => by have ⟨_, h4⟩ := (inRegion_iff_toNat (by omega) a).mp hP; omega⟩
  have hExt1 := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st) st.byteVal
    (g.slotStart idx - 4#64) (n := p.toNat - (g.slotStart idx).toNat + 4) (by omega)
    (fun a ha => (hSliceRw a (hPreSub a ha).1).1)
    (fun a ha => (hSliceRw a (hPreSub a ha).1).2.mpr (hPreSub a ha).2)
  have hExt2 := ByteMap_extract_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧
      ¬ InRegion (g.slotStart idx - 4#64) (p.toNat - (g.slotStart idx).toNat + 4) a) st.byteVal
    (p + BitVec.ofNat 64 sz) (n := (g.slotEnd idx).toNat - (p.toNat + sz)) (by omega)
    (fun a ha => (hSliceRw a (hPostSub a ha).1).1)
    (fun a ha => ⟨(hSliceRw a (hPostSub a ha).1).2.mpr (hPostSub a ha).2.1, (hPostSub a ha).2.2⟩)
  have hKeepEq : ByteMap st.masterDom
      (fun a => (OwnedRwByte st a ∧
          ¬ InRegion (g.slotStart idx - 4#64) (p.toNat - (g.slotStart idx).toNat + 4) a) ∧
        ¬ InRegion (p + BitVec.ofNat 64 sz) ((g.slotEnd idx).toNat - (p.toNat + sz)) a) st.byteVal =
      ByteMap st.masterDom
        (fun a => OwnedRwByte st a ∧ ¬ InRegion (start - 4#64) g.stride a) st.byteVal := by
    unfold ByteMap
    refine SetSep_congr (fun a _ => ⟨fun ⟨⟨hRw, hNP⟩, hNPo⟩ => ⟨hRw, fun hInS => ?_⟩,
      fun ⟨hRw, hNS⟩ => ⟨⟨hRw, fun hP => hNS (hPreSub a hP).1⟩, fun hPo => hNS (hPostSub a hPo).1⟩⟩)
      (fun _ _ _ => rfl)
    dsimp only [start] at hInS
    have hNotU : ¬ InRegion p sz a := (hSliceRw a hInS).2.mp hRw
    have ⟨hSLo, hSHi⟩ := (inRegion_iff_toNat (by omega) a).mp hInS
    by_cases hLtP : a.toNat < p.toNat
    · exact hNP ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    · have hGeEnd : p.toNat + sz ≤ a.toNat :=
        Classical.byContradiction fun hLt =>
          hNotU ((inRegion_iff_toNat (base := p) (n := sz) (by omega) a).mpr ⟨by omega, by omega⟩)
      exact hNPo ((inRegion_iff_toNat
        (base := p + BitVec.ofNat 64 sz) (n := (g.slotEnd idx).toNat - (p.toNat + sz))
        (by omega) a).mpr ⟨by omega, by omega⟩)
  have hAddr1 : (g.slotStart idx - 4#64) +
      BitVec.ofNat 64 (p.toNat - (g.slotStart idx).toNat + 4) = p := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_add_toNat (a := g.slotStart idx - 4#64)
      (n := p.toNat - (g.slotStart idx).toNat + 4) (by omega)]
    omega
  refine ⟨hSlotLen, ?_⟩
  rw [hExt1, hExt2, hKeepEq]
  have hSlotEq : ((start - 4#64) ↦ₛ slotBs) =
      (((g.slotStart idx - 4#64) ↦ₛ
          readBytesFromMap st.byteVal (g.slotStart idx - 4#64) (p.toNat - (g.slotStart idx).toNat + 4)) ∗
       (p ↦ₛ userBs) ∗
       ((p + BitVec.ofNat 64 sz) ↦ₛ
          readBytesFromMap st.byteVal (p + BitVec.ofNat 64 sz) ((g.slotEnd idx).toNat - (p.toNat + sz)))) := by
    dsimp only [start, slotBs, mkLiveUserSlotBs]
    rw [List.append_assoc, pointsToBytes_append (g.slotStart idx - 4#64) _ (userBs ++ _),
      readBytesFromMap_length, hAddr1, pointsToBytes_append p userBs _, hUserLen]
  rw [hSlotEq]
  ac_rfl

theorem protNone_disjoint_slotWriteMod {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length) :
    (∀ ap ∈ st.availMetaPages, ∀ a, InRegion ap 4096 a → ¬ SlotWriteMod g idx a) ∧
    (∀ gp ∈ st.guardPages, ∀ a, InRegion gp 4096 a → ¬ SlotWriteMod g idx a) := by
  have hmAll : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  obtain ⟨maM, hmaM, _, _, _, hmNat, hmFit, hMaM48⟩ := metaSlot_in_metaArea hwf hmAll
  obtain ⟨rgG, hrgG, hrgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have ⟨_, _, _, hSub4, hEn, hEndLe, h48G, _, _⟩ := group_slot_bounds (hwf.groups_wf g hg) hIdx
  have hStr := (group_stride_pos_and_align (hwf.groups_wf g hg)).1
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hRg48 : rgG.mem.toNat + rgG.maplen * 4096 ≤ 2 ^ 48 := by
    have h := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1; simp [GroupDesc.totalBytes, hrgMp] at h; exact h
  obtain ⟨hP123, _, hC123Rg⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
  obtain ⟨hP12, _, hC12Ap⟩ := pairwiseDisjoint_append hP123
  obtain ⟨_, _, hCMaGp⟩ := pairwiseDisjoint_append hP12
  have hRgMem : (rgG.mem, rgG.maplen * 4096) ∈
      (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgG, decide_eq_true hrgMp⟩)
  have hModIn : ∀ a, SlotWriteMod g idx a →
      InRegion maM.base 4096 a ∨ InRegion rgG.mem (rgG.maplen * 4096) a := fun a hMod => by
    rcases hMod with hM | ⟨hS, _⟩
    · have haN := (inRegion_iff_toNat (base := g.metaPtr) (n := 40) (by omega) a).mp hM
      exact Or.inl ((inRegion_iff_toNat (base := maM.base) (n := 4096) (by omega) a).mpr ⟨by omega, by omega⟩)
    · have haN := (inRegion_iff_toNat (base := g.slotStart idx - 4#64) (n := g.stride) (by omega) a).mp hS
      exact Or.inr ((inRegion_iff_toNat (base := rgG.mem) (n := rgG.maplen * 4096) (by omega) a).mpr ⟨by omega, by omega⟩)
  refine ⟨fun ap hap a haAp hMod => ?_, fun gp hgp a haGp hMod => ?_⟩
  · rcases hModIn a hMod with haMa | haRg
    · exact not_both_inRegion_of_disjointRegions
        (hC12Ap _ (List.mem_append_left _ (List.mem_map_of_mem hmaM)) _ (List.mem_map_of_mem hap)) haMa haAp
    · exact not_both_inRegion_of_disjointRegions
        (hC123Rg _ (List.mem_append_right _ (List.mem_map_of_mem hap)) _ hRgMem) haAp haRg
  · rcases hModIn a hMod with haMa | haRg
    · exact not_both_inRegion_of_disjointRegions
        (hCMaGp _ (List.mem_map_of_mem hmaM) _ (List.mem_map_of_mem hgp)) haMa haGp
    · exact not_both_inRegion_of_disjointRegions
        (hC123Rg _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))) _ hRgMem) haGp haRg

theorem slotWf_congr_local {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {h h' : GroupDesc} (hh : h ∈ st.groups) {j : Nat} (hj : j < h.slots.length)
    (hMeta : h'.metaPtr = h.metaPtr) (hMem : h'.mem = h.mem)
    (hLast : h'.lastIdx = h.lastIdx) (hSc : h'.sc = h.sc) (hMap : h'.maplen = h.maplen)
    (hAct : h'.activeIdx = h.activeIdx)
    (hAvailJ : h'.availMask.getLsbD j = h.availMask.getLsbD j)
    (hFreedJ : h'.freedMask.getLsbD j = h.freedMask.getLsbD j)
    (hGroups : ∀ cg ∈ st.groups, ∃ cg' ∈ st'.groups,
      cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
      cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap)
    (hNonNest : (∀ cm, h.slots[j]'hj ≠ .liveNested cm) →
      ∀ a, InRegion (h.slotStart j - 4#64) h.stride a → st'.byteVal a = st.byteVal a)
    (hNest : ∀ cm cg, h.slots[j]'hj = .liveNested cm → cg ∈ st.groups → cg.metaPtr = cm →
      cg.parentMeta = some h.metaPtr →
      st'.byteVal (h.slotStart j - 4#64) = st.byteVal (h.slotStart j - 4#64) ∧
      ∀ a, InRegion (cg.mem - 4#64) 4 a → st'.byteVal a = st.byteVal a)
    (hOv : ∀ u r e, h.slots[j]'hj = .liveUser u r e → st'.liveMap.ov u = st.liveMap.ov u := by
      intros; rfl) :
    SlotWf st' h' j (h.slots[j]'hj) := by
  have hgw := hwf.groups_wf h hh
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
  have ⟨_, hStorH, hStH, hSub4H, hEnH, hEndLeH, h48H, _, _⟩ := group_slot_bounds hgw hj
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hStridePos := (group_stride_pos_and_align hgw).1
  have hSMH : (j + 1) * h.stride = j * h.stride + h.stride := Nat.succ_mul j h.stride
  have hSubS4 : (h.slotStart j - 4#64).toNat = (h.slotStart j).toNat - 4 := bv64_sub_toNat (by omega)
  have hStrideEq : h'.stride = h.stride := by simp [GroupDesc.stride, hLast, hMap, hSc]
  have hStorEq : h'.storage = h.storage := by simp [GroupDesc.storage, hMem]
  have hStartEq : h'.slotStart j = h.slotStart j := by simp [GroupDesc.slotStart, hStorEq, hStrideEq]
  have hEndEq : h'.slotEnd j = h.slotEnd j := by simp [GroupDesc.slotEnd, hStartEq, hStrideEq]
  have hInSl : ∀ a : BitVec 64, (h.slotStart j).toNat - 4 ≤ a.toNat → a.toNat < (h.slotEnd j).toNat →
      InRegion (h.slotStart j - 4#64) h.stride a := fun a hLo hHi =>
    (inRegion_iff_toNat (base := h.slotStart j - 4#64) (n := h.stride) (by omega) a).mpr ⟨by omega, by omega⟩
  unfold SlotWf at hsw ⊢
  rw [hStartEq, hEndEq, hStorEq, hSc, hMap, hMeta, hAct, hAvailJ, hFreedJ]
  cases hS : h.slots[j]'hj with
  | freeAvail | freeInactive | claimed =>
    rw [hS] at hsw
    have hEqB := hNonNest (by simp [hS]) (h.slotStart j - 4#64) (hInSl _ (by omega) (by omega))
    exact ⟨hEqB.trans hsw.1, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1, trivial⟩
  | liveNested cm =>
    rw [hS] at hsw
    obtain ⟨hb0, hb1, hb2, hb3, hSc48, cg, hcg, hCm, hPm, hCgLo, hCgAl, hCgHi, hCgCap,
      hTot, hCgB4, hCgB3, hCgB2⟩ := hsw
    obtain ⟨hB0Eq, hCgEq⟩ := hNest cm cg hS hcg hCm hPm
    obtain ⟨cg', hcg', hCm', hPm', hCgMem', hCgCap'⟩ := hGroups cg hcg
    have hSub2N : (cg.mem - 2#64).toNat = cg.mem.toNat - 2 := bv64_sub_toNat (by omega)
    have hSub4N : (cg.mem - 4#64).toNat = cg.mem.toNat - 4 := bv64_sub_toNat (by omega)
    have hSub3N : (cg.mem - 3#64).toNat = cg.mem.toNat - 3 := bv64_sub_toNat (by omega)
    have hInCg : ∀ a : BitVec 64, cg.mem.toNat - 4 ≤ a.toNat → a.toNat < cg.mem.toNat →
        InRegion (cg.mem - 4#64) 4 a := fun a hLo hHi =>
      (inRegion_iff_toNat (base := cg.mem - 4#64) (n := 4) (by omega) a).mpr ⟨by omega, by omega⟩
    have hR2 : readBytesFromMap st'.byteVal (cg.mem - 2#64) 2 = readBytesFromMap st.byteVal (cg.mem - 2#64) 2 :=
      readBytesFromMap_congr_pred (W := fun a => ¬ InRegion (cg.mem - 4#64) 4 a)
        (by decide)
        (fun a ha => by
          have haN := (inRegion_iff_toNat (base := cg.mem - 2#64) (n := 2) (by omega) a).mp ha
          exact fun hN => hN (hInCg a (by omega) (by omega)))
        (fun a hNotW => hCgEq a (Decidable.of_not_not hNotW))
    refine ⟨hB0Eq.trans hb0, hb1, hb2, hb3, hSc48, cg', hcg', hCm'.trans hCm, hPm'.trans hPm, ?_⟩
    rw [hCgMem', hCgCap']
    exact ⟨hCgLo, hCgAl, hCgHi, hCgCap, hTot,
      (hCgEq _ (hInCg _ (by omega) (by omega))).trans hCgB4,
      (hCgEq _ (hInCg _ (by omega) (by omega))).trans hCgB3,
      hR2.trans hCgB2⟩
  | liveUser u rq ef =>
    rw [hS] at hsw
    have hEqSl := hNonNest (by simp [hS])
    obtain ⟨hb0, hb1, hb2, hb3, hBWf, hULo, hUHi, hEf1, hEf2, hResLt, hSc2, hSc63,
      hUB3, hOffCase, hRes1, hRes5⟩ := hsw
    have hEqAt : ∀ a : BitVec 64, (h.slotStart j).toNat - 4 ≤ a.toNat → a.toNat < (h.slotEnd j).toNat →
        st'.byteVal a = st.byteVal a := fun a hLo hHi => hEqSl a (hInSl a hLo hHi)
    have hReadEq : ∀ (b : BitVec 64) (n : Nat),
        (h.slotStart j).toNat - 4 ≤ b.toNat → b.toNat + n ≤ (h.slotEnd j).toNat →
        readBytesFromMap st'.byteVal b n = readBytesFromMap st.byteVal b n := fun b n hBLo hBHi =>
      readBytesFromMap_congr_pred (W := fun a => ¬ InRegion (h.slotStart j - 4#64) h.stride a)
        (by omega)
        (fun a ha => by
          have haN := (inRegion_iff_toNat (base := b) (n := n) (by omega) a).mp ha
          exact fun hN => hN (hInSl a (by omega) (by omega)))
        (fun a hNotW => hEqSl a (Decidable.of_not_not hNotW))
    have hSubU3 : (u - 3#64).toNat = u.toNat - 3 := bv64_sub_toNat (by omega)
    have hSubU4 : (u - 4#64).toNat = u.toNat - 4 := bv64_sub_toNat (by omega)
    have hSubU2 : (u - 2#64).toNat = u.toNat - 2 := bv64_sub_toNat (by omega)
    refine ⟨(hEqAt _ (by omega) (by omega)).trans hb0, hb1, hb2, hb3, hBWf, hULo, hUHi,
      hEf1, by rw [hOv u rq ef hS]; exact hEf2, hResLt, hSc2, hSc63,
      (hEqAt _ (by omega) (by omega)).trans hUB3, ?_, ?_, ?_⟩
    · by_cases hC : (u.toNat - h.storage.toNat) / 16 ≤ 0xffff
      · simp only [hC, ↓reduceIte] at hOffCase ⊢
        exact ⟨(hEqAt _ (by omega) (by omega)).trans hOffCase.1,
          (hReadEq _ 2 (by omega) (by omega)).trans hOffCase.2⟩
      · simp only [hC, ↓reduceIte] at hOffCase ⊢
        have hJ0 : j = 0 := hOffCase.2.1
        have hSubU8 : (u - 8#64).toNat = u.toNat - 8 := bv64_sub_toNat (by omega)
        have hSt0 : (h.slotStart j).toNat = h.storage.toNat := by subst hJ0; simp [GroupDesc.slotStart]
        exact ⟨hOffCase.1, hJ0, hOffCase.2.2.1,
          (hEqAt _ (by omega) (by omega)).trans hOffCase.2.2.2.1,
          (hReadEq _ 2 (by omega) (by omega)).trans hOffCase.2.2.2.2.1,
          (hReadEq _ 4 (by omega) (by omega)).trans hOffCase.2.2.2.2.2⟩
    · intro hR1
      have hAddN : (u + BitVec.ofNat 64 rq).toNat = u.toNat + rq := bv64_add_toNat (by omega)
      exact (hEqAt _ (by omega) (by omega)).trans (hRes1 hR1)
    · intro hR5
      have hSubE5 : (h.slotEnd j - 5#64).toNat = (h.slotEnd j).toNat - 5 := bv64_sub_toNat (by omega)
      have hSubE4 : (h.slotEnd j - 4#64).toNat = (h.slotEnd j).toNat - 4 := bv64_sub_toNat (by omega)
      exact ⟨(hEqAt _ (by omega) (by omega)).trans (hRes5 hR5).1,
        (hReadEq _ 4 (by omega) (by omega)).trans (hRes5 hR5).2⟩

theorem replaceGroup_preserves_mem_and_roots (gs : List GroupDesc) (g g' : GroupDesc)
    (hg : g ∈ gs) (hNodup : (gs.map (·.metaPtr)).Nodup)
    (hMem : g'.mem = g.mem) (hMap : g'.maplen = g.maplen) :
    (replaceGroup gs g.metaPtr g').map (·.mem) = gs.map (·.mem) ∧
    ((replaceGroup gs g.metaPtr g').filter (fun x => decide (0 < x.maplen))).map
        (fun x => (x.mem, x.maplen * 4096)) =
      (gs.filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) := by
  induction gs with
  | nil => cases hg
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hg with hEqHd | hMemTl
    · subst hd
      have hTlId : replaceGroup tl g.metaPtr g' = tl :=
        replaceGroup_id_of_ne tl g.metaPtr g' fun y hy hE => hNodup.1 (hE ▸ List.mem_map_of_mem hy)
      have hCons : replaceGroup (g :: tl) g.metaPtr g' = g' :: tl := by
        show (if (g.metaPtr == g.metaPtr) = true then g' else g) :: replaceGroup tl g.metaPtr g' = g' :: tl
        rw [BEq.rfl, hTlId]; rfl
      rw [hCons, List.map_cons, hMem, List.filter_cons, List.filter_cons, hMap]
      refine ⟨rfl, ?_⟩
      cases decide (0 < g.maplen) <;> simp [hMem, hMap]
    · have hHdNe : hd.metaPtr ≠ g.metaPtr :=
        fun hE => hNodup.1 (hE ▸ List.mem_map_of_mem hMemTl)
      have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
        rw [beq_false_of_ne hHdNe]; rfl
      obtain ⟨ih1, ih2⟩ := ih hMemTl hNodup.2
      rw [hCons, List.map_cons, ih1, List.filter_cons, List.filter_cons]
      refine ⟨rfl, ?_⟩
      cases decide (0 < hd.maplen) <;> simp [ih2]

theorem inPlace_sc_eff_bound {sc newSz extraEff : Nat}
    (hNewMax : newSz ≤ 131051)
    (hScCases : sc < 48 ∨ sc = 63)
    (hScLe : sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1) :
    sc < 48 ∧
    (2 ≤ sc → nominalSlotCap (sc - 2) < extraEff + max newSz MallocngMinBlockCost) := by
  obtain ⟨hNew48, _, hMin⟩ := sizeToClass_spec hNewMax
  have hSc48 : sc < 48 := by omega
  refine ⟨hSc48, fun h2 => ?_⟩
  rcases hMin with hZero | hGt
  · omega
  · have hSubLe : sc - 2 ≤ sizeToClassUnits ((newSz + 3) / 16) - 1 := by omega
    rcases Nat.lt_or_eq_of_le hSubLe with hLt | hEq
    · have hMono := sizeClass_strictMono hLt (by omega)
      unfold nominalSlotCap MallocngMinBlockCost at *; omega
    · rw [hEq]; unfold MallocngMinBlockCost at *; omega

theorem reallocInPlace_slotWf {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {val' : BitVec 64 → BitVec 8} {liveMap' : MallocngLiveMap}
    (hOvP : st.liveMap.ov p ≤ liveMap'.ov p)
    (hPreEq : ∀ a : BitVec 64, (g.slotStart idx - 4#64).toNat ≤ a.toNat →
      a.toNat < p.toNat → a ≠ p - 3#64 → val' a = st.byteVal a)
    (hHdrP3 : val' (p - 3#64) =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (hRes1 : 1 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      val' (p + BitVec.ofNat 64 newSz) = 0#8)
    (hRes5 : 5 ≤ (g.slotEnd idx).toNat - (p.toNat + newSz) →
      val' (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap val' (g.slotEnd idx - 4#64) 4 =
        unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (p.toNat + newSz)))) :
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    let g' := { g with slots := g.slots.set idx (.liveUser p newSz newEff) }
    let st' := { st with groups := replaceGroup st.groups g.metaPtr g', byteVal := val', liveMap := liveMap' }
    g.sc < 48 ∧
    MallocngBlockWf p newSz ∧
    SlotWf st' g' idx (.liveUser p newSz newEff) := by
  intro newEff g' st'
  have hgw := hwf.groups_wf g hg
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  rw [hSlot] at hsw
  obtain ⟨hb0, hb1, hb2, hb3, ⟨hpNe0, hpDvd16, _, _⟩, hULo, _, hEf1, hEf2, _,
    ⟨_, hScOff⟩, _, _, hOffCase, _, _⟩ := hsw
  have ⟨_, _, hSt, hSub4, hEn, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hStrPos := (group_stride_pos_and_align hgw).1
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  obtain ⟨hSc48, hSc2New⟩ := inPlace_sc_eff_bound (extraEff := oldEff - max oldSz MallocngMinBlockCost)
    hNewMax hgw.1 hScLe
  have hTotSmall : g.totalBytes ≤ 1048576 := by
    by_cases hMp : 0 < g.maplen
    · have hM := ((hgw.2.2.2.2.2.2.2.2.2.2.2.1 hMp).2.2.2 hSc48).1
      simp [GroupDesc.totalBytes, hMp, hM]
    · have hM0 : g.maplen = 0 := by omega
      obtain ⟨_, pg, _, _, _, _, hPg48, _, _, _, _, _, hNCap⟩ := hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
      obtain ⟨hPgLo, hPgHi, _, _⟩ := sizeClass_bounds hPg48
      simp only [GroupDesc.totalBytes, hM0, Nat.lt_irrefl, ↓reduceIte, hNCap, slotStride]
      omega
  have hMaxVal : MallocngMaxAllocSize = 9223372036854771710 := rfl
  have hNewBWf : MallocngBlockWf p newSz := ⟨hpNe0, hpDvd16, by omega, by omega⟩
  have hSubP3 : (p - 3#64).toNat = p.toNat - 3 := bv64_sub_toNat (by omega)
  have hSubP4 : (p - 4#64).toNat = p.toNat - 4 := bv64_sub_toNat (by omega)
  have hSubP2 : (p - 2#64).toNat = p.toNat - 2 := bv64_sub_toNat (by omega)
  have hStartEq : g'.slotStart idx = g.slotStart idx := rfl
  have hEndEq : g'.slotEnd idx = g.slotEnd idx := rfl
  refine ⟨hSc48, hNewBWf, ?_⟩
  unfold SlotWf
  rw [hStartEq, hEndEq, show g'.sc = g.sc from rfl]
  refine ⟨(hPreEq _ (by omega) (by omega) (fun hE => by have := congrArg BitVec.toNat hE; omega)).trans hb0,
    by simpa using hb1, by simpa using hb2, fun hLt => False.elim (by cases hb3 hLt),
    hNewBWf, hULo, hFit, by dsimp only [newEff]; omega,
    ⟨by dsimp only [newEff]; omega, by dsimp only [newEff]; omega,
      by have := hEf2.2.2; dsimp only [newEff, st']; omega⟩, by omega,
    ⟨fun ⟨h2, _⟩ => hSc2New h2, hScOff⟩, fun h63 => by omega, hHdrP3, ?_, hRes1, hRes5⟩
  by_cases hC : (p.toNat - g.storage.toNat) / 16 ≤ 0xffff
  · simp only [show g'.storage = g.storage from rfl, hC, ↓reduceIte] at hOffCase ⊢
    refine ⟨(hPreEq _ (by omega) (by omega) (fun hE => by have := congrArg BitVec.toNat hE; omega)).trans hOffCase.1,
      (readBytesFromMap_congr_pred (W := fun a => ¬ ((g.slotStart idx - 4#64).toNat ≤ a.toNat ∧
          a.toNat < p.toNat ∧ a ≠ p - 3#64)) (by decide)
        (fun a ha => by
          have haN := (inRegion_iff_toNat (base := p - 2#64) (n := 2) (by omega) a).mp ha
          exact fun hN => hN ⟨by omega, by omega, fun hE => by have := congrArg BitVec.toNat hE; omega⟩)
        (fun a hNotW => by
          have ⟨h1, h2, h3⟩ := Decidable.of_not_not hNotW
          exact hPreEq a h1 h2 h3)).trans hOffCase.2⟩
  · simp only [hC, ↓reduceIte] at hOffCase
    exact False.elim (by have := hOffCase.1; omega)

end VerifiedLibraries.Mallocng.Proofs
