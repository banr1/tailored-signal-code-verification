/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Internal

/-!
# `enframe`, Slot-Slice Disjointness, and Large `mmap` Helpers

Arithmetic, bitmask, and group-forest disjointness lemmas for `enframe`, large (`sc = 63`) `mmap`
sizing, `OwnedRwByte` containment, and `SlotWriteMod` framing.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Large `mmap` Sizing and `enframe` Bitmask Reduction -/

theorem mallocngMaxAllocSize_eq : MallocngMaxAllocSize = 9223372036854771710 := rfl

theorem large_rawLen_bounds {req peakCost : Nat} (hReq : req ≤ MallocngMaxAllocSize) :
    req + 20 ≤ 9223372036854771730 ∧
    pageAlignUp (req + 20) ≤ MallocngStepBound req peakCost := by
  have hMax : MallocngMaxAllocSize = 9223372036854771710 := rfl
  refine ⟨by omega, ?_⟩
  unfold MallocngStepBound
  have hMono : pageAlignUp (req + 20) ≤ pageAlignUp (req + 8192) := by
    unfold pageAlignUp PAGE_SIZE
    omega
  omega

theorem large_packed_maplen_eq {req : Nat} :
    ((req + 4115) / 4096) * 4096 = pageAlignUp (req + 20) := by
  unfold pageAlignUp PAGE_SIZE
  have hEq : req + 4115 = req + 20 + 4095 := by omega
  rw [hEq]

private theorem enframeMaskReduce8 (m c : BitVec 8) (hgt : m.ult c = true) :
    let m1 := m ||| (m >>> 1)
    let m2 := m1 ||| (m1 >>> 2)
    let m3 := m2 ||| (m2 >>> 4)
    let r0 := c &&& m3
    let r := if m.ult r0 then r0 + ~~~m else r0
    r.ule m = true := by
  revert hgt
  bv_robdd

private theorem lift8_to_32_64 (m c : BitVec 8) :
    let x5 : BitVec 64 := m.zeroExtend 64
    let w1 : BitVec 32 := c.zeroExtend 32
    let x3_1 := x5 ||| (x5 >>> 1)
    let w7 := ~~~(x5.truncate 32)
    let x3_2 := x3_1 ||| (x3_1 >>> 2)
    let x3_3 := x3_2 ||| (x3_2 >>> 4)
    let w8 := w1 &&& x3_3.truncate 32
    let m1 := m ||| (m >>> 1)
    let m2 := m1 ||| (m1 >>> 2)
    let m3 := m2 ||| (m2 >>> 4)
    let r0 := c &&& m3
    let r := if m.ult r0 then r0 + ~~~m else r0
    let w1' := if x5.ult (w8.zeroExtend 64) then w8 + w7 else w8
    (x5.ult (w1.signExtend 64) = m.ult c) ∧
    (r.ule m = true →
      w1' = r.zeroExtend 32 ∧
      x5.ult (w1'.signExtend 64) = false ∧
      w1' &&& 255#32 = w1' ∧
      (w1'.zeroExtend 64).ule x5 = true) := by
  bv_robdd

/-- Exact hardware bitmask reduction in `enframe` (`+0x398 .. +0x3c0`) when `w1 &&& 255#32 = w1`
    and `(x3 >>> 4).ult (w1.signExtend 64) = true`: produces `w1' &&& 255#32 = w1'` with
    `¬ (x3 >>> 4).ult (w1'.signExtend 64)` and `(w1'.zeroExtend 64).ule (x3 >>> 4)` (discharging
    the unreachable `b.lo a_crash` at `+0x3c0`). -/
theorem enframeMaskReduce_spec (x3 : BitVec 64) (w1 : BitVec 32)
    (hw1 : w1 &&& 255#32 = w1)
    (hgt : (x3 >>> 4).ult (w1.signExtend 64) = true) :
    let x5 := x3 >>> 4
    let x3_1 := x5 ||| (x3 >>> 5)
    let w7 := ~~~(x5.truncate 32)
    let x3_2 := x3_1 ||| (x3_1 >>> 2)
    let x3_3 := x3_2 ||| (x3_2 >>> 4)
    let w8 := w1 &&& x3_3.truncate 32
    let w1' := if x5.ult (w8.zeroExtend 64) then w8 + w7 else w8
    x5.ult (w1'.signExtend 64) = false ∧
    w1' &&& 255#32 = w1' ∧
    (w1'.zeroExtend 64).ule x5 = true := by
  have hShift5 : x3 >>> 5 = (x3 >>> 4) >>> 1 := by bv_bits
  have hw1Eq : w1 = (w1.truncate 8).zeroExtend 32 := by
    revert hw1; bv_bits
  have hw1Sext : w1.signExtend 64 = (w1.truncate 8).zeroExtend 64 := by
    rw [hw1Eq]; bv_bits
  have hx5Eq : x3 >>> 4 = ((x3 >>> 4).truncate 8).zeroExtend 64 := by
    rw [hw1Sext] at hgt
    revert hgt; bv_robdd
  dsimp only
  rw [hShift5]
  rw [hx5Eq, hw1Eq] at hgt ⊢
  have ⟨hEqUlt, hImp⟩ := lift8_to_32_64 ((x3 >>> 4).truncate 8) (w1.truncate 8)
  rw [hEqUlt] at hgt
  have ⟨_, h1, h2, h3⟩ := hImp (enframeMaskReduce8 _ _ hgt)
  exact ⟨h1, h2, h3⟩

/-! ## Address Arithmetic and Group Slot-Slice Geometry -/

theorem bv64_add_toNat {a : BitVec 64} {n : Nat} (h : a.toNat + n < 2 ^ 64) :
    (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, hn]
  exact Nat.mod_eq_of_lt h

theorem bv64_sub_toNat {a : BitVec 64} {n : Nat} (hle : n ≤ a.toNat) :
    (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  have hlt64 : a.toNat < 2 ^ 64 := a.isLt
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  let m := a.toNat - n
  have hm : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hA : BitVec.ofNat 64 m + BitVec.ofNat 64 n = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hm, hn]
    have : m + n = a.toNat := by omega
    rw [this]
    exact Nat.mod_eq_of_lt hlt64
  have hSub : a - BitVec.ofNat 64 n = BitVec.ofNat 64 m := by
    rw [← hA]
    bv_arith
  rw [hSub, hm]

theorem inRegion_iff_toNat {base : BitVec 64} {n : Nat} (hNoWrap : base.toNat + n ≤ 2 ^ 64)
    (a : BitVec 64) :
    InRegion base n a ↔ base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + n := by
  unfold InRegion
  bv_omega

theorem group_stride_pos_and_align {st : MallocngSt} {g : GroupDesc} (hGWf : GroupWf st g) :
    16 ≤ g.stride ∧ g.stride % 16 = 0 := by
  unfold GroupDesc.stride
  by_cases hCond : (g.lastIdx == 0 && decide (0 < g.maplen)) = true
  · simp only [hCond, ↓reduceIte]
    have hMapPos : 0 < g.maplen := of_decide_eq_true (Bool.and_eq_true_iff.mp hCond).2
    have hAlign : g.mem.toNat % 4096 = 0 := (hGWf.2.2.2.2.2.2.2.2.2.2.2.1 hMapPos).1
    omega
  · simp only [hCond, Bool.false_eq_true, ↓reduceIte]
    rcases hGWf.1 with hSc48 | hSc63
    · have hB := (sizeClass_bounds hSc48).1
      unfold slotStride
      omega
    · exfalso
      have ⟨hL0, hMP, _⟩ := hGWf.2.2.2.1 hSc63
      apply hCond
      simp [hL0, hMP]

theorem group_slot_bounds {st : MallocngSt} {g : GroupDesc} (hGWf : GroupWf st g)
    {idx : Nat} (hIdx : idx < g.slots.length) :
    let start := g.slotStart idx
    let slotEnd := g.slotEnd idx
    idx < g.cnt ∧
    g.storage.toNat = g.mem.toNat + 16 ∧
    start.toNat = g.mem.toNat + 16 + idx * g.stride ∧
    (start - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride ∧
    slotEnd.toNat = g.mem.toNat + 12 + (idx + 1) * g.stride ∧
    slotEnd.toNat ≤ g.mem.toNat + g.totalBytes ∧
    g.mem.toNat + g.totalBytes ≤ 2 ^ 48 ∧
    start.toNat % 16 = 0 ∧
    slotEnd.toNat % 16 = 12 := by
  have ⟨hStrideGe16, hStrideMod⟩ := group_stride_pos_and_align hGWf
  have hLenCnt : g.slots.length = g.cnt := hGWf.2.2.1
  have hIdxCnt : idx < g.cnt := hLenCnt ▸ hIdx
  have hMemGe : 4096 ≤ g.mem.toNat := hGWf.2.2.2.2.1
  have hMemMod : g.mem.toNat % 16 = 0 := hGWf.2.2.2.2.2.1
  have hTot48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := hGWf.2.2.2.2.2.2.1
  have hFit : 12 + g.cnt * g.stride ≤ g.totalBytes := hGWf.2.2.2.2.2.2.2.1
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMulLe : (idx + 1) * g.stride ≤ g.cnt * g.stride :=
    Nat.mul_le_mul_right g.stride (by omega)
  have hSuccMul : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hStorage : g.storage.toNat = g.mem.toNat + 16 := by
    unfold GroupDesc.storage
    exact bv64_add_toNat (n := 16) (by omega)
  have hStart : (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride := by
    unfold GroupDesc.slotStart
    have h1 := bv64_add_toNat (a := g.storage) (n := idx * g.stride) (by omega)
    omega
  have hStartSub4 : (g.slotStart idx - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride := by
    change (g.slotStart idx - BitVec.ofNat 64 4).toNat = _
    have h1 := bv64_sub_toNat (a := g.slotStart idx) (n := 4) (by omega)
    omega
  have hEnd : (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride := by
    unfold GroupDesc.slotEnd
    have h1 := bv64_add_toNat (a := g.slotStart idx) (n := g.stride - 4) (by omega)
    omega
  have hMulMod : (idx * g.stride) % 16 = 0 := by
    rw [Nat.mul_mod, hStrideMod, Nat.mul_zero, Nat.zero_mod]
  have hMulSuccMod : ((idx + 1) * g.stride) % 16 = 0 := by
    rw [Nat.mul_mod, hStrideMod, Nat.mul_zero, Nat.zero_mod]
  refine ⟨hIdxCnt, hStorage, hStart, hStartSub4, hEnd, by omega, hTot48, ?_, ?_⟩
  · omega
  · omega

/-! ## Forest Containment, Slot-Slice Disjointness, and `liveMap` Freshness -/

theorem disjointRegions_symm {b₁ : BitVec 64} {n₁ : Nat} {b₂ : BitVec 64} {n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) : DisjointRegions b₂ n₂ b₁ n₁ :=
  ⟨h.2, h.1⟩

theorem not_both_inRegion_of_disjointRegions {b₁ : BitVec 64} {n₁ : Nat}
    {b₂ : BitVec 64} {n₂ : Nat}
    (hd : DisjointRegions b₁ n₁ b₂ n₂) {a : BitVec 64}
    (h₁ : InRegion b₁ n₁ a) (h₂ : InRegion b₂ n₂ a) : False := by
  unfold DisjointRegions InRegion at *
  bv_omega

theorem pairwiseDisjoint_append {xs ys : List (BitVec 64 × Nat)}
    (h : PairwiseDisjointRegions (xs ++ ys)) :
    PairwiseDisjointRegions xs ∧
    PairwiseDisjointRegions ys ∧
    (∀ x ∈ xs, ∀ y ∈ ys, DisjointRegions x.1 x.2 y.1 y.2) := by
  induction xs with
  | nil =>
    exact ⟨trivial, h, fun _ hx => by cases hx⟩
  | cons hd tl ih =>
    simp only [List.cons_append, PairwiseDisjointRegions] at h
    obtain ⟨hHdRest, hTl⟩ := h
    obtain ⟨hTlP, hYsP, hCross⟩ := ih hTl
    refine ⟨⟨fun z hz => hHdRest z (List.mem_append_left _ hz), hTlP⟩, hYsP, ?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hx with rfl | hxTl
    · exact hHdRest y (List.mem_append_right _ hy)
    · exact hCross x hxTl y hy

theorem pairwiseDisjoint_map_ne {α : Type} {xs : List α} {f : α → BitVec 64 × Nat}
    (hP : PairwiseDisjointRegions (xs.map f))
    {x y : α} (hx : x ∈ xs) (hy : y ∈ xs) (hNe : (f x).1 ≠ (f y).1) :
    DisjointRegions (f x).1 (f x).2 (f y).1 (f y).2 := by
  induction xs with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [List.map_cons, PairwiseDisjointRegions] at hP
    rcases List.mem_cons.mp hx with rfl | hxTl <;> rcases List.mem_cons.mp hy with rfl | hyTl
    · exact False.elim (hNe rfl)
    · exact hP.1 (f y) (List.mem_map_of_mem hyTl)
    · exact disjointRegions_symm (hP.1 (f x) (List.mem_map_of_mem hxTl))
    · exact ih hP.2 hxTl hyTl

theorem root_groups_disjoint {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g₁ g₂ : GroupDesc} (hg₁ : g₁ ∈ st.groups) (hg₂ : g₂ ∈ st.groups)
    (hmp₁ : 0 < g₁.maplen) (hmp₂ : 0 < g₂.maplen) (hNe : g₁ ≠ g₂) :
    DisjointRegions g₁.mem (g₁.maplen * 4096) g₂.mem (g₂.maplen * 4096) := by
  have hP := hwf.regions_disjoint.1
  unfold dynamicRootRegions at hP
  rw [List.append_assoc, List.append_assoc] at hP
  have ⟨_, hP2, _⟩ := pairwiseDisjoint_append hP
  have ⟨_, hP3, _⟩ := pairwiseDisjoint_append hP2
  have ⟨_, hPG, _⟩ := pairwiseDisjoint_append hP3
  have hMemNd := hwf.groups_nodup.2
  have hMemNe : g₁.mem ≠ g₂.mem := by
    intro hEq
    apply hNe
    generalize st.groups = gs at hg₁ hg₂ hMemNd
    induction gs with
    | nil => cases hg₁
    | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hMemNd
      rcases List.mem_cons.mp hg₁ with rfl | h1 <;> rcases List.mem_cons.mp hg₂ with rfl | h2
      · rfl
      · exact False.elim (hMemNd.1 (hEq ▸ List.mem_map_of_mem h2))
      · exact False.elim (hMemNd.1 (hEq.symm ▸ List.mem_map_of_mem h1))
      · exact ih h1 h2 hMemNd.2
  exact pairwiseDisjoint_map_ne hPG
    (List.mem_filter.mpr ⟨hg₁, decide_eq_true hmp₁⟩)
    (List.mem_filter.mpr ⟨hg₂, decide_eq_true hmp₂⟩)
    hMemNe

theorem metaArea_disjoint_root_group {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ma : MetaAreaDesc} (hma : ma ∈ st.metaAreas)
    {rg : GroupDesc} (hrg : rg ∈ st.groups) (hmp : 0 < rg.maplen) :
    DisjointRegions ma.base 4096 rg.mem (rg.maplen * 4096) := by
  have hP := hwf.regions_disjoint.1
  unfold dynamicRootRegions at hP
  rw [List.append_assoc, List.append_assoc] at hP
  have ⟨_, _, hCross⟩ := pairwiseDisjoint_append hP
  exact hCross (ma.base, 4096) (List.mem_map_of_mem hma)
    (rg.mem, rg.maplen * 4096)
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hmp⟩))))

private def groupRank (g : GroupDesc) : Nat :=
  if 0 < g.maplen then 50 else g.sc

private theorem group_in_root_aux {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ (fuel : Nat) {g : GroupDesc}, g ∈ st.groups → 50 - groupRank g ≤ fuel →
      ∃ rg ∈ st.groups,
        0 < rg.maplen ∧
        rg.mem.toNat ≤ g.mem.toNat ∧
        g.mem.toNat + g.totalBytes ≤ rg.mem.toNat + rg.maplen * 4096
  | 0, g, hg, hFuel => by
    by_cases hmp : 0 < g.maplen
    · refine ⟨g, hg, hmp, Nat.le_refl _, ?_⟩
      simp [GroupDesc.totalBytes, hmp]
    · have hMap0 : g.maplen = 0 := by omega
      have hGWf := hwf.groups_wf g hg
      have ⟨_, pg, _, _, _, _, hPgSc48, hGLtPg, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
      unfold groupRank at hFuel
      simp [hmp] at hFuel
      omega
  | fuel + 1, g, hg, hFuel => by
    by_cases hmp : 0 < g.maplen
    · refine ⟨g, hg, hmp, Nat.le_refl _, ?_⟩
      simp [GroupDesc.totalBytes, hmp]
    · have hMap0 : g.maplen = 0 := by omega
      have hGWf := hwf.groups_wf g hg
      have ⟨_, pg, hpg, pIdx, hpIdx, _, hPgSc48, hGLtPg, _, _, hLo, hHi, _⟩ :=
        hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
      have hPgWf := hwf.groups_wf pg hpg
      have ⟨_, _, hPgStart, _, hPgEnd, hPgEndLe, _, _, _⟩ := group_slot_bounds hPgWf hpIdx
      have hGTot : g.totalBytes = g.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
      have hPgFuel : 50 - groupRank pg ≤ fuel := by
        unfold groupRank at hFuel ⊢
        simp only [hmp, ↓reduceIte] at hFuel
        split <;> omega
      obtain ⟨rg, hrg, hRgMp, hRgLo, hRgHi⟩ := group_in_root_aux hwf fuel hpg hPgFuel
      exact ⟨rg, hrg, hRgMp, by omega, by omega⟩

theorem group_in_root_region {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    ∃ rg ∈ st.groups,
      0 < rg.maplen ∧
      rg.mem.toNat ≤ g.mem.toNat ∧
      g.mem.toNat + g.totalBytes ≤ rg.mem.toNat + rg.maplen * 4096 :=
  group_in_root_aux hwf 50 hg (by omega)

private def InSlotTagged (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (tag : Option (BitVec 64)) (a : BitVec 64) : Prop :=
  g ∈ st.groups ∧
  ∃ hIdx : idx < g.slots.length,
    InRegion (g.slotStart idx - 4#64) g.stride a ∧
    match tag with
    | none => ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm
    | some cm => g.slots[idx]'hIdx = .liveNested cm

private theorem inSlotTagged_step {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} {i : Nat} {t : Option (BitVec 64)} {a : BitVec 64}
    (h1 : InSlotTagged st g i t a) (hMap0 : g.maplen = 0) :
    ∃ pg : GroupDesc, ∃ pIdx : Nat,
      pg ∈ st.groups ∧
      groupRank g < groupRank pg ∧
      InSlotTagged st pg pIdx (some g.metaPtr) a := by
  obtain ⟨hg, hi, hReg, _⟩ := h1
  have hGWf := hwf.groups_wf g hg
  have ⟨_, _, _, hSub4, hEnd, hEndLe, hTot48, _, _⟩ := group_slot_bounds hGWf hi
  have ⟨hStrideGe16, _⟩ := group_stride_pos_and_align hGWf
  have hSuccMul : (i + 1) * g.stride = i * g.stride + g.stride := Nat.succ_mul i g.stride
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have ⟨hLoA, hHiA⟩ := (inRegion_iff_toNat (by omega) a).mp hReg
  have ⟨_, pg, hpg, pIdx, hpIdx, _, hPgSc48, hGLtPg, _, hSlotN, hPgStartLe, hPgEndGe, _⟩ :=
    hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
  have hGTot : g.totalBytes = g.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
  have hPgWf := hwf.groups_wf pg hpg
  have ⟨_, _, hPgStart, hPgSub4, hPgEnd, hPgEndLe, hPgTot48, _, _⟩ := group_slot_bounds hPgWf hpIdx
  have ⟨hPgStrideGe16, _⟩ := group_stride_pos_and_align hPgWf
  have hPgSuccMul : (pIdx + 1) * pg.stride = pIdx * pg.stride + pg.stride :=
    Nat.succ_mul pIdx pg.stride
  have hPgReg : InRegion (pg.slotStart pIdx - 4#64) pg.stride a := by
    rw [inRegion_iff_toNat (by omega)]
    omega
  have hRankLt : groupRank g < groupRank pg := by
    unfold groupRank
    have hNmp : ¬ 0 < g.maplen := by omega
    simp only [hNmp, ↓reduceIte]
    split <;> omega
  exact ⟨pg, pIdx, hpg, hRankLt, hpg, hpIdx, hPgReg, hSlotN⟩

private theorem slotTagged_disjoint_aux {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ (fuel : Nat) {g₁ : GroupDesc} {i₁ : Nat} {t₁ : Option (BitVec 64)}
      {g₂ : GroupDesc} {i₂ : Nat} {t₂ : Option (BitVec 64)} {a : BitVec 64},
      (50 - groupRank g₁) + (50 - groupRank g₂) ≤ fuel →
      InSlotTagged st g₁ i₁ t₁ a →
      InSlotTagged st g₂ i₂ t₂ a →
      (g₁, i₁, t₁) ≠ (g₂, i₂, t₂) →
      t₁ ≠ some g₂.metaPtr →
      t₂ ≠ some g₁.metaPtr →
      (∀ c ∈ st.groups, t₁ = some c.metaPtr → groupRank c ≤ groupRank g₂) →
      (∀ c ∈ st.groups, t₂ = some c.metaPtr → groupRank c ≤ groupRank g₁) →
      False
  | 0, g₁, i₁, t₁, g₂, i₂, t₂, a, hFuel, h1, h2, hNe, _, _, _, _ => by
    obtain ⟨hg₁, hi₁, hReg₁, hTag₁⟩ := h1
    obtain ⟨hg₂, hi₂, hReg₂, hTag₂⟩ := h2
    by_cases hEqG : g₁ = g₂
    · subst hEqG
      have hGWf := hwf.groups_wf g₁ hg₁
      have ⟨_, _, _, hSub1, hEnd1, hLe1, h48, _, _⟩ := group_slot_bounds hGWf hi₁
      have ⟨_, _, _, hSub2, hEnd2, _, _, _, _⟩ := group_slot_bounds hGWf hi₂
      have ⟨hStrideGe16, _⟩ := group_stride_pos_and_align hGWf
      have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
      have hSM1 : (i₁ + 1) * g₁.stride = i₁ * g₁.stride + g₁.stride := Nat.succ_mul i₁ g₁.stride
      have hSM2 : (i₂ + 1) * g₁.stride = i₂ * g₁.stride + g₁.stride := Nat.succ_mul i₂ g₁.stride
      have ⟨hL1, hR1⟩ := (inRegion_iff_toNat (by omega) a).mp hReg₁
      have ⟨hL2, hR2⟩ := (inRegion_iff_toNat (by omega) a).mp hReg₂
      by_cases hEqI : i₁ = i₂
      · subst hEqI
        apply hNe
        cases ht1 : t₁ <;> cases ht2 : t₂
        · rfl
        · rw [ht1] at hTag₁; rw [ht2] at hTag₂; exact False.elim (hTag₁ _ hTag₂)
        · rw [ht1] at hTag₁; rw [ht2] at hTag₂; exact False.elim (hTag₂ _ hTag₁)
        · rw [ht1] at hTag₁; rw [ht2] at hTag₂
          rw [hTag₁] at hTag₂; cases hTag₂; rfl
      · rcases Nat.lt_or_gt_of_ne hEqI with hLt | hGt
        · have : (i₁ + 1) * g₁.stride ≤ i₂ * g₁.stride := Nat.mul_le_mul_right _ hLt
          omega
        · have : (i₂ + 1) * g₁.stride ≤ i₁ * g₁.stride := Nat.mul_le_mul_right _ hGt
          omega
    · have hR1 : 50 ≤ groupRank g₁ := by omega
      have hR2 : 50 ≤ groupRank g₂ := by omega
      have hMp1 : 0 < g₁.maplen := by
        unfold groupRank at hR1
        by_cases h : 0 < g₁.maplen
        · exact h
        · exfalso
          have hGWf := hwf.groups_wf g₁ hg₁
          have ⟨_, _, _, _, _, _, hPg48, hLt, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
          simp [h] at hR1; omega
      have hMp2 : 0 < g₂.maplen := by
        unfold groupRank at hR2
        by_cases h : 0 < g₂.maplen
        · exact h
        · exfalso
          have hGWf := hwf.groups_wf g₂ hg₂
          have ⟨_, _, _, _, _, _, hPg48, hLt, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
          simp [h] at hR2; omega
      have hDisj := root_groups_disjoint hwf hg₁ hg₂ hMp1 hMp2 hEqG
      have hGWf1 := hwf.groups_wf g₁ hg₁
      have hGWf2 := hwf.groups_wf g₂ hg₂
      have ⟨_, _, _, hSub1, hEnd1, hLe1, h48_1, _, _⟩ := group_slot_bounds hGWf1 hi₁
      have ⟨_, _, _, hSub2, hEnd2, hLe2, h48_2, _, _⟩ := group_slot_bounds hGWf2 hi₂
      have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
      have hSM1 : (i₁ + 1) * g₁.stride = i₁ * g₁.stride + g₁.stride := Nat.succ_mul i₁ g₁.stride
      have hSM2 : (i₂ + 1) * g₂.stride = i₂ * g₂.stride + g₂.stride := Nat.succ_mul i₂ g₂.stride
      have ⟨hL1, hU1⟩ := (inRegion_iff_toNat (by omega) a).mp hReg₁
      have ⟨hL2, hU2⟩ := (inRegion_iff_toNat (by omega) a).mp hReg₂
      have hTot1 : g₁.totalBytes = g₁.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp1]
      have hTot2 : g₂.totalBytes = g₂.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp2]
      exact not_both_inRegion_of_disjointRegions hDisj
        ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
        ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  | fuel + 1, g₁, i₁, t₁, g₂, i₂, t₂, a, hFuel, h1, h2, hNe, ht1Ne, ht2Ne, hB1, hB2 => by
    by_cases hEqG : g₁ = g₂
    · exact slotTagged_disjoint_aux hwf 0 (by
        subst hEqG
        obtain ⟨hg₁, hi₁, hReg₁, hTag₁⟩ := h1
        obtain ⟨_, hi₂, hReg₂, hTag₂⟩ := h2
        exfalso
        have hGWf := hwf.groups_wf g₁ hg₁
        have ⟨_, _, _, hSub1, hEnd1, hLe1, h48, _, _⟩ := group_slot_bounds hGWf hi₁
        have ⟨_, _, _, hSub2, hEnd2, _, _, _, _⟩ := group_slot_bounds hGWf hi₂
        have ⟨hStrideGe16, _⟩ := group_stride_pos_and_align hGWf
        have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
        have hSM1 : (i₁ + 1) * g₁.stride = i₁ * g₁.stride + g₁.stride := Nat.succ_mul i₁ g₁.stride
        have hSM2 : (i₂ + 1) * g₁.stride = i₂ * g₁.stride + g₁.stride := Nat.succ_mul i₂ g₁.stride
        have ⟨hL1, hR1⟩ := (inRegion_iff_toNat (by omega) a).mp hReg₁
        have ⟨hL2, hR2⟩ := (inRegion_iff_toNat (by omega) a).mp hReg₂
        by_cases hEqI : i₁ = i₂
        · subst hEqI
          apply hNe
          cases ht1 : t₁ <;> cases ht2 : t₂
          · rfl
          · rw [ht1] at hTag₁; rw [ht2] at hTag₂; exact False.elim (hTag₁ _ hTag₂)
          · rw [ht1] at hTag₁; rw [ht2] at hTag₂; exact False.elim (hTag₂ _ hTag₁)
          · rw [ht1] at hTag₁; rw [ht2] at hTag₂
            rw [hTag₁] at hTag₂; cases hTag₂; rfl
        · rcases Nat.lt_or_gt_of_ne hEqI with hLt | hGt
          · have : (i₁ + 1) * g₁.stride ≤ i₂ * g₁.stride := Nat.mul_le_mul_right _ hLt
            omega
          · have : (i₂ + 1) * g₁.stride ≤ i₁ * g₁.stride := Nat.mul_le_mul_right _ hGt
            omega) h1 h2 hNe ht1Ne ht2Ne hB1 hB2
    · by_cases hBothRoot : 0 < g₁.maplen ∧ 0 < g₂.maplen
      · exact slotTagged_disjoint_aux hwf 0 (by
          unfold groupRank; simp [hBothRoot.1, hBothRoot.2])
          h1 h2 hNe ht1Ne ht2Ne hB1 hB2
      · by_cases hLeRank : groupRank g₁ ≤ groupRank g₂
        · have hMap0 : g₁.maplen = 0 := by
            by_cases hMp1 : 0 < g₁.maplen
            · exfalso; apply hBothRoot; refine ⟨hMp1, ?_⟩
              by_cases hMp2 : 0 < g₂.maplen
              · exact hMp2
              · unfold groupRank at hLeRank
                have hGWf2 := hwf.groups_wf g₂ h2.1
                have ⟨_, _, _, _, _, _, hPg48, hLt, _⟩ := hGWf2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
                simp [hMp1, hMp2] at hLeRank; omega
            · omega
          obtain ⟨pg₁, pIdx₁, hpg₁, hRankLt, hStep₁⟩ := inSlotTagged_step hwf h1 hMap0
          have hRankPgLe50 : groupRank pg₁ ≤ 50 := by
            unfold groupRank
            by_cases hMp : 0 < pg₁.maplen
            · simp [hMp]
            · have hGWf := hwf.groups_wf pg₁ hpg₁
              have ⟨_, _, _, _, _, _, hPg48, hLt, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
              simp [hMp]; omega
          exact slotTagged_disjoint_aux hwf fuel (by omega) hStep₁ h2
            (fun hEq => ht2Ne (Prod.mk.inj (Prod.mk.inj hEq).2).2.symm)
            (fun hEq => hEqG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 h1.1 h2.1 (Option.some.inj hEq)))
            (fun hEq => by have := hB2 pg₁ hpg₁ hEq; omega)
            (fun c hc hEq => by
              have hEqC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc h1.1 (Option.some.inj hEq).symm
              subst hEqC; exact hLeRank)
            (fun c hc hEq => Nat.le_trans (hB2 c hc hEq) (Nat.le_of_lt hRankLt))
        · have hLeRank2 : groupRank g₂ ≤ groupRank g₁ := by omega
          have hMap0 : g₂.maplen = 0 := by
            by_cases hMp2 : 0 < g₂.maplen
            · exfalso; apply hBothRoot; refine ⟨?_, hMp2⟩
              by_cases hMp1 : 0 < g₁.maplen
              · exact hMp1
              · unfold groupRank at hLeRank2
                have hGWf1 := hwf.groups_wf g₁ h1.1
                have ⟨_, _, _, _, _, _, hPg48, hLt, _⟩ := hGWf1.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
                simp [hMp1, hMp2] at hLeRank2; omega
            · omega
          obtain ⟨pg₂, pIdx₂, hpg₂, hRankLt, hStep₂⟩ := inSlotTagged_step hwf h2 hMap0
          have hRankPgLe50 : groupRank pg₂ ≤ 50 := by
            unfold groupRank
            by_cases hMp : 0 < pg₂.maplen
            · simp [hMp]
            · have hGWf := hwf.groups_wf pg₂ hpg₂
              have ⟨_, _, _, _, _, _, hPg48, hLt, _⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
              simp [hMp]; omega
          exact slotTagged_disjoint_aux hwf fuel (by omega) h1 hStep₂
            (fun hEq => ht1Ne (Prod.mk.inj (Prod.mk.inj hEq).2).2)
            (fun hEq => by have := hB1 pg₂ hpg₂ hEq; omega)
            (fun hEq => hEqG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 h1.1 h2.1 (Option.some.inj hEq).symm))
            (fun c hc hEq => Nat.le_trans (hB1 c hc hEq) (Nat.le_of_lt hRankLt))
            (fun c hc hEq => by
              have hEqC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc h2.1 (Option.some.inj hEq).symm
              subst hEqC; exact hLeRank2)

/-- Any two distinct non-`.liveNested` slots `(g₁, i₁) ≠ (g₂, i₂)` in `st.groups` have completely
    disjoint `SlotSlice` byte intervals `[slotStart - 4, slotEnd)`. -/
theorem nonNested_slotSlice_disjoint {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g₁ : GroupDesc} (hg₁ : g₁ ∈ st.groups) {i₁ : Nat} (hi₁ : i₁ < g₁.slots.length)
    (hn₁ : ∀ cm, g₁.slots[i₁]'hi₁ ≠ .liveNested cm)
    {g₂ : GroupDesc} (hg₂ : g₂ ∈ st.groups) {i₂ : Nat} (hi₂ : i₂ < g₂.slots.length)
    (hn₂ : ∀ cm, g₂.slots[i₂]'hi₂ ≠ .liveNested cm)
    (hNe : g₁ ≠ g₂ ∨ i₁ ≠ i₂)
    {a : BitVec 64}
    (ha₁ : InRegion (g₁.slotStart i₁ - 4#64) g₁.stride a)
    (ha₂ : InRegion (g₂.slotStart i₂ - 4#64) g₂.stride a) : False := by
  exact slotTagged_disjoint_aux (t₁ := none) (t₂ := none) hwf 100 (by omega)
    ⟨hg₁, hi₁, ha₁, hn₁⟩ ⟨hg₂, hi₂, ha₂, hn₂⟩
    (fun hEq => by
      rcases hNe with hG | hI
      · exact hG (Prod.mk.inj hEq).1
      · exact hI (Prod.mk.inj (Prod.mk.inj hEq).2).1)
    (by simp) (by simp)
    (fun _ _ h => by simp at h) (fun _ _ h => by simp at h)

/-- When `g.slots[idx] = .claimed`, no live allocation in `st.liveMap` can already occupy any
    16-byte-aligned user address `p ∈ [g.slotStart idx, g.slotEnd idx]` (even for `req = 0`). -/
theorem liveMap_fresh_of_claimed {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    {p : BitVec 64} (hAlign : 16 ∣ p.toNat)
    (hLo : (g.slotStart idx).toNat ≤ p.toNat)
    (hHi : p.toNat ≤ (g.slotEnd idx).toNat) :
    st.liveMap p = none := by
  cases hLp : st.liveMap p with
  | none => rfl
  | some n =>
    exfalso
    obtain ⟨g', hg', idx', hIdx', eff', hSlot'⟩ := (hwf.liveMap_wf p n).mp hLp
    have hGWf := hwf.groups_wf g hg
    have hGWf' := hwf.groups_wf g' hg'
    have ⟨_, _, hStart, hSub4, hEnd, hEndLe, h48, _, hEndMod⟩ := group_slot_bounds hGWf hIdx
    have ⟨_, _, hStart', hSub4', hEnd', hEndLe', h48', _, hEndMod'⟩ := group_slot_bounds hGWf' hIdx'
    have hSWf' := hGWf'.slot_wf idx' hIdx'
    rw [hSlot'] at hSWf'
    have hLo' : (g'.slotStart idx').toNat ≤ p.toNat := hSWf'.2.2.2.2.2.1
    have hHi' : p.toNat + n ≤ (g'.slotEnd idx').toNat := hSWf'.2.2.2.2.2.2.1
    have hpMod : p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hAlign
    have hStrict : p.toNat < (g.slotEnd idx).toNat := by omega
    have hStrict' : p.toNat < (g'.slotEnd idx').toNat := by omega
    have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
    have hSM' : (idx' + 1) * g'.stride = idx' * g'.stride + g'.stride := Nat.succ_mul idx' g'.stride
    have ha : InRegion (g.slotStart idx - 4#64) g.stride p :=
      (inRegion_iff_toNat (by omega) p).mpr ⟨by omega, by omega⟩
    have ha' : InRegion (g'.slotStart idx' - 4#64) g'.stride p :=
      (inRegion_iff_toNat (by omega) p).mpr ⟨by omega, by omega⟩
    have hNe : g ≠ g' ∨ idx ≠ idx' := by
      by_cases hG : g = g'
      · right
        intro hI
        subst hG; subst hI
        rw [hClaimed] at hSlot'
        cases hSlot'
      · exact Or.inl hG
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by rw [hClaimed]; intro _ h; cases h)
      hg' hIdx' (by rw [hSlot']; intro _ h; cases h) hNe ha ha'

/-! ## `meta` Slot and Claimed `SlotSlice` `OwnedRwByte` Containment -/

theorem metaSlot_in_metaArea {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hm : m ∈ allMetaSlots st) :
    ∃ ma ∈ st.metaAreas, ∃ k : Nat,
      k < 101 ∧ m = ma.slotAddr k ∧
      m.toNat = ma.base.toNat + 24 + 40 * k ∧
      m.toNat + 40 ≤ ma.base.toNat + 4096 ∧
      ma.base.toNat + 4096 ≤ 2 ^ 48 := by
  unfold allMetaSlots at hm
  obtain ⟨ma, hma, hmMap⟩ := List.mem_flatMap.mp hm
  obtain ⟨k, hkR, rfl⟩ := List.mem_map.mp hmMap
  have hk : k < 101 := List.mem_range.mp hkR
  have ⟨_, _, hMa48, _⟩ := hwf.metaAreas_wf.2.1 ma hma
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hToNat : (ma.slotAddr k).toNat = ma.base.toNat + 24 + 40 * k := by
    unfold MetaAreaDesc.slotAddr
    have := bv64_add_toNat (a := ma.base) (n := 24 + 40 * k) (by omega)
    omega
  exact ⟨ma, hma, k, hk, rfl, hToNat, by omega, hMa48⟩

theorem metaSlots_disjoint {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {m₁ m₂ : BitVec 64} (hm₁ : m₁ ∈ allMetaSlots st) (hm₂ : m₂ ∈ allMetaSlots st)
    (hNe : m₁ ≠ m₂) {a : BitVec 64}
    (ha₁ : InRegion m₁ 40 a) (ha₂ : InRegion m₂ 40 a) : False := by
  obtain ⟨ma₁, hma₁, k₁, hk₁, rfl, hN₁, hLe₁, h48_1⟩ := metaSlot_in_metaArea hwf hm₁
  obtain ⟨ma₂, hma₂, k₂, hk₂, rfl, hN₂, hLe₂, h48_2⟩ := metaSlot_in_metaArea hwf hm₂
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  by_cases hEqMa : ma₁ = ma₂
  · subst hEqMa
    have hkNe : k₁ ≠ k₂ := fun h => hNe (by rw [h])
    have ⟨hLo1, hHi1⟩ := (inRegion_iff_toNat (by omega) a).mp ha₁
    have ⟨hLo2, hHi2⟩ := (inRegion_iff_toNat (by omega) a).mp ha₂
    omega
  · have hBaseNe : ma₁.base ≠ ma₂.base := by
      intro hB
      apply hEqMa
      have hNd := hwf.metaAreas_wf.1
      generalize st.metaAreas = mas at hma₁ hma₂ hNd
      induction mas with
      | nil => cases hma₁
      | cons hd tl ih =>
        simp only [List.map_cons, List.nodup_cons] at hNd
        rcases List.mem_cons.mp hma₁ with rfl | h1 <;> rcases List.mem_cons.mp hma₂ with rfl | h2
        · rfl
        · exact False.elim (hNd.1 (hB ▸ List.mem_map_of_mem h2))
        · exact False.elim (hNd.1 (hB.symm ▸ List.mem_map_of_mem h1))
        · exact ih h1 h2 hNd.2
    have hP := hwf.regions_disjoint.1
    unfold dynamicRootRegions at hP
    rw [List.append_assoc, List.append_assoc] at hP
    have ⟨hPMa, _, _⟩ := pairwiseDisjoint_append hP
    have hDisj := pairwiseDisjoint_map_ne hPMa hma₁ hma₂ hBaseNe
    dsimp only at hDisj
    have ⟨hLo1, hHi1⟩ := (inRegion_iff_toNat (by omega) a).mp ha₁
    have ⟨hLo2, hHi2⟩ := (inRegion_iff_toNat (by omega) a).mp ha₂
    exact not_both_inRegion_of_disjointRegions hDisj
      ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
      ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)

theorem group_meta_and_claimed_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hNoRes : st.reservedMetas = [])
    {g : GroupDesc} (hg : g ∈ st.groups) :
    (∀ a : BitVec 64, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    (∀ idx : Nat, (hIdx : idx < g.slots.length) →
      (∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm) →
      (∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c) →
      (∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a →
        OwnedRwByte st a ∧ a ∈ st.masterDom ∧ ¬ InRegion g.metaPtr 40 a)) := by
  have hmAll : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hg))))
  obtain ⟨ma, hma, k, hk, _, hN, hLe, h48⟩ := metaSlot_in_metaArea hwf hmAll
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMetaInMa : ∀ a : BitVec 64, InRegion g.metaPtr 40 a → InRegion ma.base 4096 a := by
    intro a ha
    have ⟨hLo, hHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hMetaNotUser : ∀ a : BitVec 64, InRegion g.metaPtr 40 a → ¬ CarvedUserByte st a := by
    intro a ha ⟨g', hg', s', hs', hSub⟩
    obtain ⟨idx', hIdx', hEqS'⟩ := List.getElem_of_mem hs'
    cases hS' : s' with
    | freeAvail | freeInactive | claimed | liveNested _ => simp [hS'] at hSub
    | liveUser u' r' c' =>
      simp only [hS'] at hSub
      have hSlot' : g'.slots[idx']'hIdx' = .liveUser u' r' c' := hEqS'.trans hS'
      have hGWf' := hwf.groups_wf g' hg'
      have ⟨_, _, hStart', _, hEnd', hEndLe', h48', _, _⟩ := group_slot_bounds hGWf' hIdx'
      have hSWf' := hGWf'.slot_wf idx' hIdx'
      rw [hSlot'] at hSWf'
      have hLo' : (g'.slotStart idx').toNat ≤ u'.toNat := hSWf'.2.2.2.2.2.1
      have hHi' : u'.toNat + r' ≤ (g'.slotEnd idx').toNat := hSWf'.2.2.2.2.2.2.1
      obtain ⟨rg', hrg', hMp', hRgLo', hRgHi'⟩ := group_in_root_region hwf hg'
      have hRg48' := (hwf.groups_wf rg' hrg').2.2.2.2.2.2.1
      have hRgTot' : rg'.totalBytes = rg'.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp']
      have ⟨hALo, hAHi⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
      have hInRg : InRegion rg'.mem (rg'.maplen * 4096) a :=
        (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
      exact not_both_inRegion_of_disjointRegions
        (metaArea_disjoint_root_group hwf hma hrg' hMp') (hMetaInMa a ha) hInRg
  refine ⟨fun a ha => ?_, fun idx hIdx hNotN hNotU a ha => ?_⟩
  · have hRw : OwnedRwByte st a :=
      ⟨Or.inl ⟨ma, hma, hMetaInMa a ha⟩, hMetaNotUser a ha,
        by simp [CarvedMetaByte, hNoRes]⟩
    exact ⟨hRw, hwf.masterDom_wf.2.1 a (Or.inl hRw)⟩
  · obtain ⟨rg, hrg, hMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
    have hGWf := hwf.groups_wf g hg
    have ⟨_, _, _, hSub4, hEnd, hEndLe, h48G, _, _⟩ := group_slot_bounds hGWf hIdx
    have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
    have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
    have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
    have ⟨hALo, hAHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    have hInRg : InRegion rg.mem (rg.maplen * 4096) a :=
      (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    have hNotUser : ¬ CarvedUserByte st a := by
      rintro ⟨g', hg', s', hs', hSub⟩
      obtain ⟨idx', hIdx', hEqS'⟩ := List.getElem_of_mem hs'
      cases hS' : s' with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS'] at hSub
      | liveUser u' r' c' =>
        simp only [hS'] at hSub
        have hSlot' : g'.slots[idx']'hIdx' = .liveUser u' r' c' := hEqS'.trans hS'
        have hGWf' := hwf.groups_wf g' hg'
        have ⟨_, _, hStart', hSub4', hEnd', _, h48', _, _⟩ := group_slot_bounds hGWf' hIdx'
        have hSWf' := hGWf'.slot_wf idx' hIdx'
        rw [hSlot'] at hSWf'
        have hLo' : (g'.slotStart idx').toNat ≤ u'.toNat := hSWf'.2.2.2.2.2.1
        have hHi' : u'.toNat + r' ≤ (g'.slotEnd idx').toNat := hSWf'.2.2.2.2.2.2.1
        have hSM' : (idx' + 1) * g'.stride = idx' * g'.stride + g'.stride :=
          Nat.succ_mul idx' g'.stride
        have ⟨hULo, hUHi⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
        have ha' : InRegion (g'.slotStart idx' - 4#64) g'.stride a :=
          (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
        have hNe : g ≠ g' ∨ idx ≠ idx' := by
          by_cases hG : g = g'
          · right
            intro hI
            subst hG; subst hI
            exact hNotU u' r' c' hSlot'
          · exact Or.inl hG
        exact nonNested_slotSlice_disjoint hwf hg hIdx hNotN
          hg' hIdx' (by rw [hSlot']; intro _ h; cases h) hNe ha ha'
    have hRw : OwnedRwByte st a :=
      ⟨Or.inr ⟨rg, hrg, hMp, hInRg⟩, hNotUser, by simp [CarvedMetaByte, hNoRes]⟩
    have hNotMeta : ¬ InRegion g.metaPtr 40 a := fun hM =>
      not_both_inRegion_of_disjointRegions
        (metaArea_disjoint_root_group hwf hma hrg hMp) (hMetaInMa a hM) hInRg
    exact ⟨hRw, hwf.masterDom_wf.2.1 a (Or.inl hRw), hNotMeta⟩

/-! ## Forest-Wide Disjointness of `SlotWriteMod` -/

theorem readBytesFromMap_congr_pred {v₁ v₂ : BitVec 64 → BitVec 8}
    {b : BitVec 64} {n : Nat} {W : BitVec 64 → Prop}
    (hn : n ≤ 2 ^ 64)
    (hOut : ∀ a : BitVec 64, InRegion b n a → ¬ W a)
    (hEqOut : ∀ a : BitVec 64, ¬ W a → v₁ a = v₂ a) :
    readBytesFromMap v₁ b n = readBytesFromMap v₂ b n := by
  unfold readBytesFromMap
  apply List.map_congr_left
  intro a ha
  exact hEqOut a (hOut a ((mem_rangeAddrs_iff_inRegion b hn a).mp ha))

private theorem nested_contains_aux {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {h cg : GroupDesc} {j : Nat} {b : BitVec 64}
    (hcg : cg ∈ st.groups) (hParentCg : cg.parentMeta = some h.metaPtr)
    (hSub1 : InSlotTagged st h j (some cg.metaPtr) b) :
    ∀ (fuel : Nat) {x : GroupDesc} {i : Nat} {t : Option (BitVec 64)},
      51 - groupRank x ≤ fuel →
      InSlotTagged st x i t b →
      (t = none ∨ ∃ c ∈ st.groups, t = some c.metaPtr ∧ groupRank c < groupRank cg) →
      cg = x ∨
        ∃ k : Nat, ∃ _hk : k < cg.slots.length,
          (cg.slotStart k).toNat ≤ x.mem.toNat ∧
          x.mem.toNat + x.totalBytes ≤ (cg.slotEnd k).toNat
  | 0, x, _, _, hFuel, hSubX, _ => by
    have hHWf := hwf.groups_wf x hSubX.1
    unfold groupRank at hFuel
    split at hFuel
    · omega
    · next hNotMp =>
      rcases hHWf.1 with h48 | h63
      · omega
      · exact False.elim (hNotMp (hHWf.2.2.2.1 h63).2.1)
  | fuel + 1, x, i, t, hFuel, hSubX, hTag => by
    by_cases hEq : cg = x
    · exact Or.inl hEq
    · have hh : h ∈ st.groups := hSub1.1
      have hCgWf := hwf.groups_wf cg hcg
      have hCgMap0 : cg.maplen = 0 :=
        Classical.byContradiction fun hNe0 => by
          have hNone := hCgWf.2.2.2.2.2.2.2.2.2.2.1.mp (by omega)
          rw [hNone] at hParentCg; cases hParentCg
      have ⟨_, ph, hph, _, _, hP, hPhSc48, hCgLtPh, _, _, _, _, _⟩ :=
        hCgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hCgMap0
      have hPhEqH : ph = h := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hph hh
        (Option.some.inj (hP.symm.trans hParentCg))
      subst hPhEqH
      have hCgRankLtH : groupRank cg < groupRank ph := by
        unfold groupRank
        simp only [hCgMap0, Nat.lt_irrefl, ↓reduceIte]
        split <;> omega
      have hCgRankLt50 : groupRank cg < 50 := by
        unfold groupRank; simp only [hCgMap0, Nat.lt_irrefl, ↓reduceIte]; omega
      by_cases hRankLe : groupRank cg ≤ groupRank x
      · exfalso
        exact slotTagged_disjoint_aux hwf ((50 - groupRank ph) + (50 - groupRank x))
          (Nat.le_refl _) hSub1 hSubX
          (fun hTup => by
            have hT : some cg.metaPtr = t := congrArg (·.2.2) hTup
            rcases hTag with rfl | ⟨c, hc, rfl, hRc⟩
            · cases hT
            · have hEqC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hc (Option.some.inj hT)
              subst hEqC; omega)
          (fun hS => hEq (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hSubX.1 (Option.some.inj hS)))
          (fun hS => by
            rcases hTag with rfl | ⟨c, hc, rfl, hRc⟩
            · cases hS
            · have hEqC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc hh (Option.some.inj hS)
              subst hEqC; omega)
          (fun c hc hS => by
            have hEqC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hc (Option.some.inj hS)
            subst hEqC; exact hRankLe)
          (fun c hc hS => by
            rcases hTag with rfl | ⟨c', hc', rfl, hRc⟩
            · cases hS
            · have hEqC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc' hc (Option.some.inj hS)
              subst hEqC; omega)
      · have hXMap0 : x.maplen = 0 := by
          cases hMp : x.maplen
          · rfl
          · have hR50 : groupRank x = 50 := by simp [groupRank, hMp]
            omega
        have hXWf := hwf.groups_wf x hSubX.1
        have hXTot : x.totalBytes = x.nestedCap := by simp [GroupDesc.totalBytes, hXMap0]
        obtain ⟨px, pIdx, hpx, hRankPx, hSubPx⟩ := inSlotTagged_step hwf hSubX hXMap0
        have hPxWf := hwf.groups_wf px hpx
        have hSWfPx := hPxWf.slot_wf pIdx hSubPx.2.1
        rw [hSubPx.2.2.2] at hSWfPx
        obtain ⟨_, cg2, hcg2, hEqMeta2, _, hPxLo, _, hPxHi, _⟩ := hSWfPx.2.2.2.2
        have hCg2EqX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg2 hSubX.1 hEqMeta2
        subst hCg2EqX
        rcases nested_contains_aux hwf hcg hParentCg hSub1 fuel (by omega) hSubPx
          (Or.inr ⟨cg2, hcg2, rfl, by omega⟩) with rfl | ⟨k, hk, hKLo, hKHi⟩
        · exact Or.inr ⟨pIdx, hSubPx.2.1, hPxLo, hXTot ▸ hPxHi⟩
        · have ⟨_, _, hPxSt, _, hPxEn, hPxEndLe, _, _, _⟩ := group_slot_bounds hPxWf hSubPx.2.1
          have ⟨hPxStride, _⟩ := group_stride_pos_and_align hPxWf
          exact Or.inr ⟨k, hk, by omega, by omega⟩

private theorem inSlotTagged_to_root {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) {b : BitVec 64} :
    ∀ (fuel : Nat) {x : GroupDesc} {i : Nat} {t : Option (BitVec 64)},
      50 - groupRank x ≤ fuel →
      InSlotTagged st x i t b →
      x.maplen = 0 →
      ∃ rg : GroupDesc, ∃ k : Nat, ∃ c : GroupDesc,
        0 < rg.maplen ∧ c ∈ st.groups ∧ c.parentMeta = some rg.metaPtr ∧
        InSlotTagged st rg k (some c.metaPtr) b
  | 0, x, _, _, hFuel, hSubX, hMap0 => by
    have hXWf := hwf.groups_wf x hSubX.1
    unfold groupRank at hFuel
    simp only [hMap0, Nat.lt_irrefl, ↓reduceIte] at hFuel
    rcases hXWf.1 with h48 | h63
    · omega
    · have := (hXWf.2.2.2.1 h63).2.1; omega
  | fuel + 1, x, _, _, hFuel, hSubX, hMap0 => by
    obtain ⟨px, pIdx, hpx, hRankPx, hSubPx⟩ := inSlotTagged_step hwf hSubX hMap0
    have hPxWf := hwf.groups_wf px hpx
    have hSWf := hPxWf.slot_wf pIdx hSubPx.2.1
    rw [hSubPx.2.2.2] at hSWf
    obtain ⟨_, cg, hcg, hEqM, hParent, _⟩ := hSWf.2.2.2.2
    have hEqCg := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hSubX.1 hEqM
    subst hEqCg
    by_cases hMp : 0 < px.maplen
    · exact ⟨px, pIdx, cg, hMp, hcg, hParent, hSubPx⟩
    · exact inSlotTagged_to_root hwf fuel (by omega) hSubPx (by omega)

/-- Footprint of bytes potentially modified by claiming or `enframe`-ing slot `idx` of `g`:
    `[g.metaPtr, +40)` plus `(g.slotStart idx - 4, g.slotEnd idx)` (`start[-4] == 0` stays `0`). -/
def SlotWriteMod (g : GroupDesc) (idx : Nat) (a : BitVec 64) : Prop :=
  InRegion g.metaPtr 40 a ∨
    (InRegion (g.slotStart idx - 4#64) g.stride a ∧ a ≠ g.slotStart idx - 4#64)

private theorem slotWriteMod_disjoint_otherSlot {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm)
    {maG : MetaAreaDesc} (hmaG : maG ∈ st.metaAreas)
    (hGMetaInMa : ∀ a, InRegion g.metaPtr 40 a → InRegion maG.base 4096 a)
    {h : GroupDesc} (hh : h ∈ st.groups) {j : Nat} (hj : j < h.slots.length)
    (hDiff : h.metaPtr ≠ g.metaPtr ∨ j ≠ idx) :
    ((∀ cm, h.slots[j]'hj ≠ .liveNested cm) →
      ∀ a, InRegion (h.slotStart j - 4#64) h.stride a → ¬ SlotWriteMod g idx a) ∧
    (∀ cm cg, h.slots[j]'hj = .liveNested cm → cg ∈ st.groups → cg.metaPtr = cm →
      cg.parentMeta = some h.metaPtr →
      ¬ SlotWriteMod g idx (h.slotStart j - 4#64) ∧
        ∀ a, InRegion (cg.mem - 4#64) 4 a → ¬ SlotWriteMod g idx a) := by
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  obtain ⟨rgH, hrgH, hMpRgH, hRgLoH, hRgHiH⟩ := group_in_root_region hwf hh
  have hRg48H : rgH.mem.toNat + rgH.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgH hrgH).2.2.2.2.2.2.1
  have hRgTotH : rgH.totalBytes = rgH.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRgH]
  have ⟨_, _, hHSt, hHSub4, hHEn, hHEndLe, hH48, _, _⟩ := group_slot_bounds (hwf.groups_wf h hh) hj
  have ⟨hHStride, _⟩ := group_stride_pos_and_align (hwf.groups_wf h hh)
  have ⟨_, _, hGSt, hGSub4, hGEn, hGEndLe, hG48, _, _⟩ := group_slot_bounds (hwf.groups_wf g hg) hIdx
  have ⟨hGStride, _⟩ := group_stride_pos_and_align (hwf.groups_wf g hg)
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSMH : (j + 1) * h.stride = j * h.stride + h.stride := Nat.succ_mul j h.stride
  have hInRgH : ∀ a, InRegion (h.slotStart j - 4#64) h.stride a → InRegion rgH.mem (rgH.maplen * 4096) a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  refine ⟨fun hNN a ha hMod => ?_, fun cm cg hSlotN hcg hCgM hParCg => ?_⟩
  · rcases hMod with hM | ⟨hS, _⟩
    · exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrgH hMpRgH)
        (hGMetaInMa a hM) (hInRgH a ha)
    · exact nonNested_slotSlice_disjoint hwf hh hj hNN hg hIdx hNotNested
        (hDiff.imp_left fun hNeM hE => hNeM (congrArg GroupDesc.metaPtr hE)) ha hS
  · have hSWfN0 := (hwf.groups_wf h hh).slot_wf j hj; rw [hSlotN] at hSWfN0
    obtain ⟨_, cg2, hcg2, hEqM2, _, hLoCg, _, hHiCg, _⟩ := hSWfN0.2.2.2.2; clear hSWfN0
    have hEqCg2 := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg2 hcg (hEqM2.trans hCgM.symm); subst hEqCg2
    have ⟨hCgMemGe, hCg48, hCgMap0, hCapGe⟩ :
        4096 ≤ cg2.mem.toNat ∧ cg2.mem.toNat + cg2.totalBytes ≤ 2 ^ 48 ∧ cg2.maplen = 0 ∧ 12 ≤ cg2.nestedCap := by
      have hCgWf := hwf.groups_wf cg2 hcg2
      have hM0 : cg2.maplen = 0 := Classical.byContradiction fun hP => by
        have hNone := hCgWf.2.2.2.2.2.2.2.2.2.2.1.mp (by omega); rw [hNone] at hParCg; cases hParCg
      have hCT : cg2.totalBytes = cg2.nestedCap := by simp [GroupDesc.totalBytes, hM0]
      exact ⟨hCgWf.2.2.2.2.1, hCgWf.2.2.2.2.2.2.1, hM0, by have := hCgWf.2.2.2.2.2.2.2.1; omega⟩
    have hCgTot : cg2.totalBytes = cg2.nestedCap := by simp [GroupDesc.totalBytes, hCgMap0]
    have hSubHelper : ∀ a : BitVec 64, a.toNat < cg2.mem.toNat →
        InRegion (h.slotStart j - 4#64) h.stride a → ¬ SlotWriteMod g idx a := fun a hLtCg ha hMod => by
      rcases hMod with hM | ⟨hS, _⟩
      · exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrgH hMpRgH)
          (hGMetaInMa a hM) (hInRgH a ha)
      · have ⟨hSLo, _⟩ := (inRegion_iff_toNat (by omega) a).mp hS
        rcases nested_contains_aux (t := none) hwf hcg2 hParCg ⟨hh, hj, ha, hCgM ▸ hSlotN⟩
          (51 - groupRank g) (Nat.le_refl _) ⟨hg, hIdx, hS, hNotNested⟩ (Or.inl rfl) with rfl | ⟨k, hk, hKLo, _⟩
        · omega
        · have ⟨_, _, hCSt, _, _, _, _, _, _⟩ := group_slot_bounds (hwf.groups_wf cg2 hcg2) hk
          omega
    refine ⟨hSubHelper _ (by omega) ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩), fun a ha => ?_⟩
    have hSubCg4 := bv64_sub_toNat (a := cg2.mem) (n := 4) (by omega)
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact hSubHelper a (by omega) ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)

set_option maxHeartbeats 400000 in
theorem slotWriteMod_disjoint {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm) :
    (∀ ma ∈ st.metaAreas, ∀ a, InRegion ma.base 24 a → ¬ SlotWriteMod g idx a) ∧
    (∀ m ∈ allMetaSlots st, m ≠ g.metaPtr → ∀ a, InRegion m 40 a → ¬ SlotWriteMod g idx a) ∧
    (∀ h ∈ st.groups, (∀ a, InRegion h.mem 9 a → ¬ SlotWriteMod g idx a) ∧
      ¬ SlotWriteMod g idx (h.slotEnd h.lastIdx)) ∧
    (∀ h ∈ st.groups, ∀ (j : Nat) (hj : j < h.slots.length), (h.metaPtr ≠ g.metaPtr ∨ j ≠ idx) →
      ((∀ cm, h.slots[j]'hj ≠ .liveNested cm) →
        ∀ a, InRegion (h.slotStart j - 4#64) h.stride a → ¬ SlotWriteMod g idx a) ∧
      (∀ cm cg, h.slots[j]'hj = .liveNested cm → cg ∈ st.groups → cg.metaPtr = cm →
        cg.parentMeta = some h.metaPtr →
        ¬ SlotWriteMod g idx (h.slotStart j - 4#64) ∧
          ∀ a, InRegion (cg.mem - 4#64) 4 a → ¬ SlotWriteMod g idx a)) := by
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hmAll : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hg))))
  obtain ⟨maG, hmaG, kG, hkG, _, hNG, hLeG, h48G⟩ := metaSlot_in_metaArea hwf hmAll
  have hGMetaInMa : ∀ a, InRegion g.metaPtr 40 a → InRegion maG.base 4096 a := fun a hM => by
    have ⟨hMLo, hMHi⟩ := (inRegion_iff_toNat (by omega) a).mp hM
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  obtain ⟨rgG, hrgG, hMpRgG, hRgLoG, hRgHiG⟩ := group_in_root_region hwf hg
  have hRg48G : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
  have hRgTotG : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRgG]
  have ⟨_, _, hGSt, hGSub4, hGEn, hGEndLe, hG48, _, _⟩ := group_slot_bounds (hwf.groups_wf g hg) hIdx
  have ⟨hGStride, _⟩ := group_stride_pos_and_align (hwf.groups_wf g hg)
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSlotInRgG : ∀ a, InRegion (g.slotStart idx - 4#64) g.stride a →
      InRegion rgG.mem (rgG.maplen * 4096) a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hNotSlotOfMeta : ∀ ma ∈ st.metaAreas, ∀ a, InRegion ma.base 4096 a →
      ¬ InRegion (g.slotStart idx - 4#64) g.stride a := fun ma hma a ha hS =>
    not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hma hrgG hMpRgG) ha (hSlotInRgG a hS)
  refine ⟨?_, ?_, ?_, fun h hh j hj hDiff =>
    slotWriteMod_disjoint_otherSlot hwf hg hIdx hNotNested hmaG hGMetaInMa hh hj hDiff⟩
  · intro ma hma a ha hMod
    have ⟨_, hAlMa, h48Ma, _⟩ := hwf.metaAreas_wf.2.1 ma hma
    have ⟨_, hAlMaG, _, _⟩ := hwf.metaAreas_wf.2.1 maG hmaG
    have ⟨hLo1, hHi1⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    rcases hMod with hM | ⟨hS, _⟩
    · have ⟨hLo2, hHi2⟩ := (inRegion_iff_toNat (by omega) a).mp hM
      by_cases hB : ma.base.toNat = maG.base.toNat <;> omega
    · exact hNotSlotOfMeta ma hma a ((inRegion_iff_toNat (by omega) a).mpr ⟨hLo1, by omega⟩) hS
  · intro m hm hNe a ha hMod
    obtain ⟨maM, hmaM, _, _, _, hNM, hLeM, h48M⟩ := metaSlot_in_metaArea hwf hm
    have ⟨hLo1, hHi1⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    rcases hMod with hM | ⟨hS, _⟩
    · exact metaSlots_disjoint hwf hm hmAll hNe ha hM
    · exact hNotSlotOfMeta maM hmaM a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) hS
  · intro h hh
    obtain ⟨rgH, hrgH, hMpRgH, hRgLoH, hRgHiH⟩ := group_in_root_region hwf hh
    have ⟨hRg48H, hRgAl4096⟩ : rgH.mem.toNat + rgH.totalBytes ≤ 2 ^ 48 ∧ rgH.mem.toNat % 4096 = 0 := by
      have hRWf := hwf.groups_wf rgH hrgH
      exact ⟨hRWf.2.2.2.2.2.2.1, (hRWf.2.2.2.2.2.2.2.2.2.2.2.1 hMpRgH).1⟩
    have hRgTotH : rgH.totalBytes = rgH.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRgH]
    have ⟨hHLen, hHTotGe12, hHSlotsEq⟩ :
        h.lastIdx < h.slots.length ∧ 12 ≤ h.totalBytes ∧ h.slots.length = h.cnt := by
      have hHWf := hwf.groups_wf h hh
      exact ⟨by rw [hHWf.2.2.1]; unfold GroupDesc.cnt; omega,
        by have := hHWf.2.2.2.2.2.2.2.1; omega, hHWf.2.2.1⟩
    have ⟨_, _, _, _, hHEndLast, hHEndLe, hH48, _, hHEndMod12⟩ := group_slot_bounds (hwf.groups_wf h hh) hHLen
    have ⟨hHStride, _⟩ := group_stride_pos_and_align (hwf.groups_wf h hh)
    have hEndStrict : (h.slotEnd h.lastIdx).toNat < rgH.mem.toNat + rgH.maplen * 4096 := by omega
    have hCore : ∀ a : BitVec 64, (InRegion h.mem 9 a ∨ a = h.slotEnd h.lastIdx) → ¬ SlotWriteMod g idx a := by
      intro a hCase hMod
      have hBounds : h.mem.toNat ≤ a.toNat ∧ a.toNat < h.mem.toNat + 9 ∨ a = h.slotEnd h.lastIdx := by
        rcases hCase with hR | rfl
        · exact Or.inl ((inRegion_iff_toNat (by omega) a).mp hR)
        · exact Or.inr rfl
      have hInRgH : InRegion rgH.mem (rgH.maplen * 4096) a := by
        rw [inRegion_iff_toNat (by omega)]; rcases hBounds with ⟨h1, h2⟩ | rfl <;> omega
      rcases hMod with hM | ⟨hS, hNeStart4⟩
      · exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrgH hMpRgH)
          (hGMetaInMa a hM) hInRgH
      · have ⟨hSLo, hSHi⟩ := (inRegion_iff_toNat (by omega) a).mp hS
        have hSLt : (g.slotStart idx - 4#64).toNat < a.toNat :=
          Nat.lt_of_le_of_ne hSLo (fun hE => hNeStart4 (BitVec.eq_of_toNat_eq hE.symm))
        by_cases hEqH : h = g
        · subst hEqH
          have hMono : (idx + 1) * h.stride ≤ (h.lastIdx + 1) * h.stride :=
            Nat.mul_le_mul_right _ (by rw [hHSlotsEq] at hIdx; unfold GroupDesc.cnt at hIdx; omega)
          rcases hBounds with ⟨_, h2⟩ | rfl <;> omega
        · by_cases hMpH : 0 < h.maplen
          · have hHAl4096 : h.mem.toNat % 4096 = 0 := ((hwf.groups_wf h hh).2.2.2.2.2.2.2.2.2.2.2.1 hMpH).1
            have hHTot : h.totalBytes = h.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpH]
            have hInH : InRegion h.mem (h.maplen * 4096) a :=
              (inRegion_iff_toNat (by omega) a).mpr (by rcases hBounds with ⟨h1, h2⟩ | rfl <;> omega)
            by_cases hEqRg : h.metaPtr = rgG.metaPtr
            · have hEqHRg := (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hrgG hEqRg).symm; subst hEqHRg
              have hGMap0 : g.maplen = 0 := Classical.byContradiction fun hPos => by
                have hPos' : 0 < g.maplen := Nat.pos_of_ne_zero hPos
                have hGTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hPos']
                exact not_both_inRegion_of_disjointRegions (root_groups_disjoint hwf hh hg hMpH hPos' hEqH)
                  hInH ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
              obtain ⟨rg', k, c, hMp', hc, hParC, hSubR⟩ :=
                inSlotTagged_to_root (t := none) hwf (50 - groupRank g) (Nat.le_refl _) ⟨hg, hIdx, hS, hNotNested⟩ hGMap0
              have hRgEq : rg' = rgG := Classical.byContradiction fun hNeR =>
                not_both_inRegion_of_disjointRegions (root_groups_disjoint hwf hSubR.1 hh hMp' hMpH hNeR)
                  (by
                    have ⟨_, _, _, hSub4R, hEnR, hLeR, h48R, _, _⟩ := group_slot_bounds (hwf.groups_wf rg' hSubR.1) hSubR.2.1
                    have ⟨hStrR, _⟩ := group_stride_pos_and_align (hwf.groups_wf rg' hSubR.1)
                    have hSMR : (k + 1) * rg'.stride = k * rg'.stride + rg'.stride := Nat.succ_mul k rg'.stride
                    have hTotR : rg'.totalBytes = rg'.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp']
                    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hSubR.2.2.1
                    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) hInH
              rw [hRgEq] at hSubR hParC
              have ⟨_, _, hKSt, _, hKEn, _, _, _, _⟩ := group_slot_bounds (hwf.groups_wf rgG hh) hSubR.2.1
              have hMonoK : (k + 1) * rgG.stride ≤ (rgG.lastIdx + 1) * rgG.stride :=
                Nat.mul_le_mul_right _ (by have := hSubR.2.1; rw [hHSlotsEq] at this; unfold GroupDesc.cnt at this; omega)
              have hSWfK := (hwf.groups_wf rgG hh).slot_wf k hSubR.2.1; rw [hSubR.2.2.2] at hSWfK
              obtain ⟨_, cgK, hcgK, hEqMK, _, hLoK, _, hHiK, _⟩ := hSWfK.2.2.2.2; clear hSWfK
              have hEqCgC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcgK hc hEqMK; subst hEqCgC
              rcases nested_contains_aux (t := none) hwf hcgK hParC hSubR (51 - groupRank g) (Nat.le_refl _)
                ⟨hg, hIdx, hS, hNotNested⟩ (Or.inl rfl) with rfl | ⟨k2, hk2, hK2Lo, hK2Hi⟩
              · have hCTot : cgK.totalBytes = cgK.nestedCap := by simp [GroupDesc.totalBytes, hGMap0]
                rcases hBounds with ⟨_, h2⟩ | rfl <;> omega
              · have hCMap0 : cgK.maplen = 0 := Classical.byContradiction fun hP => by
                  have hNone := (hwf.groups_wf cgK hcgK).2.2.2.2.2.2.2.2.2.2.1.mp (by omega); rw [hNone] at hParC; cases hParC
                have hCTot : cgK.totalBytes = cgK.nestedCap := by simp [GroupDesc.totalBytes, hCMap0]
                have ⟨_, _, hCSt, _, hCEn, hCEndLe, _, _, _⟩ := group_slot_bounds (hwf.groups_wf cgK hcgK) hk2
                have ⟨hCStr, _⟩ := group_stride_pos_and_align (hwf.groups_wf cgK hcgK)
                rcases hBounds with ⟨_, h2⟩ | rfl <;> omega
            · exact not_both_inRegion_of_disjointRegions
                (root_groups_disjoint hwf hh hrgG hMpH hMpRgG (fun hE => hEqRg (congrArg GroupDesc.metaPtr hE))) hInH (hSlotInRgG a hS)
          · have hHMap0 : h.maplen = 0 := by omega
            obtain ⟨_, ph, hph, pIdx, hpIdx, hPhMeta, _, _, _, hPhSlot, hPhLo, hPhHi, _⟩ :=
              (hwf.groups_wf h hh).2.2.2.2.2.2.2.2.2.2.2.2.1 hHMap0
            have hHTot : h.totalBytes = h.nestedCap := by simp [GroupDesc.totalBytes, hHMap0]
            have ⟨_, _, hPhSt, hPhSub4, hPhEn, hPhEndLe, hPh48, _, _⟩ := group_slot_bounds (hwf.groups_wf ph hph) hpIdx
            have ⟨hPhStr, _⟩ := group_stride_pos_and_align (hwf.groups_wf ph hph)
            have hSMPh : (pIdx + 1) * ph.stride = pIdx * ph.stride + ph.stride := Nat.succ_mul pIdx ph.stride
            let b : BitVec 64 := if a = h.slotEnd h.lastIdx then a - 1#64 else a
            have hBNat : b.toNat = if a = h.slotEnd h.lastIdx then a.toNat - 1 else a.toNat := by
              by_cases hEqA : a = h.slotEnd h.lastIdx <;> simp only [b, hEqA, ↓reduceIte]
              · subst hEqA; exact bv64_sub_toNat (by omega)
            have hSubG : InSlotTagged st g idx none b :=
              ⟨hg, hIdx, (inRegion_iff_toNat (by omega) b).mpr ⟨by split at hBNat <;> omega, by split at hBNat <;> omega⟩, hNotNested⟩
            have hSubPh : InSlotTagged st ph pIdx (some h.metaPtr) b :=
              ⟨hph, hpIdx, (inRegion_iff_toNat (by omega) b).mpr ⟨by
                rcases hBounds with ⟨h1, h2⟩ | rfl <;> split at hBNat <;> first | contradiction | omega, by
                rcases hBounds with ⟨h1, h2⟩ | rfl <;> split at hBNat <;> first | contradiction | omega⟩, hPhSlot⟩
            rcases nested_contains_aux (t := none) hwf hh hPhMeta hSubPh (51 - groupRank g) (Nat.le_refl _) hSubG (Or.inl rfl) with
              rfl | ⟨k, hk, hKLo, hKHi⟩
            · exact hEqH rfl
            · have ⟨_, _, hHKSt, _, hHKEn, _, _, _, _⟩ := group_slot_bounds (hwf.groups_wf h hh) hk
              have hMonoK : (k + 1) * h.stride ≤ (h.lastIdx + 1) * h.stride :=
                Nat.mul_le_mul_right _ (by rw [hHSlotsEq] at hk; unfold GroupDesc.cnt at hk; omega)
              rcases hBounds with ⟨_, h2⟩ | rfl <;> omega
    exact ⟨fun a ha => hCore a (Or.inl ha), hCore _ (Or.inr rfl)⟩

end VerifiedLibraries.Mallocng.Proofs
