/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.Footprint
public import LibsignalBinary.Heap.Fine.AllocGroupFine

/-!
# Fine-Grained Allocation and Free Commit Lemmas

Full `MallocngFineInv` commit transitions from `AllocSlotInvPres` and `GroupsSubGeometry`:
- Slab `.claimed → .liveUser` commits (`sc < 48`), incrementing `pk[sc]` and discharging
  `req < Guaranteed63Threshold` via `no_slab_slot_ge_guaranteed63`.
- Direct `sc = 63` `mmap` group commits, routing `Guaranteed63Threshold ≤ req` to `large63Groups`
  and `req < Guaranteed63Threshold` to `straddle63Groups`.
- Deallocation (`FreeGroupsSub`), crediting `declCost63 req (max align 16)` when
  `Guaranteed63Threshold ≤ req`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine

open Arm64 ProofLib SepProp
open VerifiedLibraries.Mallocng
open VerifiedLibraries.Mallocng.Proofs

/-! ## Linear-Form and Coarse-Weight Lemmas -/

theorem list_getD_set_eq {xs : List Nat} {sc v k : Nat} (hsc : sc < xs.length) :
    (xs.set sc v).getD k 0 = if k = sc then v else xs.getD k 0 := by
  induction xs generalizing sc k with
  | nil => exact False.elim (Nat.not_lt_zero sc hsc)
  | cons hd tl ih =>
    cases sc with
    | zero =>
      cases k <;> simp [List.getD]
    | succ sc' =>
      have hsc' : sc' < tl.length := Nat.lt_of_succ_lt_succ hsc
      cases k with
      | zero => simp [List.getD]
      | succ k' =>
        have hIh := ih (k := k') hsc'
        simp only [List.set_cons_succ, List.getD, List.getElem?_cons_succ] at hIh ⊢
        rw [hIh]
        by_cases hEq : k' = sc' <;> simp [hEq]

theorem list_set_succ_le_getD {pk : List Nat} {sc : Nat} (hsc : sc < pk.length) (k : Nat) :
    pk.getD k 0 ≤ (pk.set sc (pk.getD sc 0 + 1)).getD k 0 := by
  rw [list_getD_set_eq hsc]
  by_cases hEq : k = sc <;> simp [hEq]

private theorem map_range_add_sum (n : Nat) (f g : Nat → Nat) :
    ((List.range n).map fun i => f i + g i).sum =
      ((List.range n).map f).sum + ((List.range n).map g).sum := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.map_append,
        List.sum_append, List.sum_append, List.sum_append, ih]
    simp only [List.map, List.sum_cons, List.sum_nil]
    omega

private theorem sum_indicator_range {sc n : Nat} (hsc : sc < n) (v : Nat) :
    ((List.range n).map fun j => if j = sc then v else 0).sum = v := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_zero sc hsc)
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hEq : m = sc
    · subst hEq
      have hZero : ((List.range m).map fun j => if j = m then v else 0).sum = 0 := by
        have hMapZero : ((List.range m).map fun j => if j = m then v else 0) =
            (List.range m).map fun _ => 0 := by
          refine List.map_congr_left fun j hj => ?_
          have hjNe : j ≠ m := Nat.ne_of_lt (List.mem_range.mp hj)
          simp [hjNe]
        rw [hMapZero]
        clear hsc ih hMapZero
        induction m with
        | zero => rfl
        | succ k ihk => rw [List.range_succ, List.map_append, List.sum_append, ihk]; rfl
      simp [hZero]
    · have hsc' : sc < m := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hsc) (Ne.symm hEq)
      simp [hEq, ih hsc']

theorem linForm_set_succ (c : Nat → Nat) {pk : List Nat} {sc : Nat}
    (hLen : pk.length = 48) (hsc : sc < 48) :
    linForm c (pk.set sc (pk.getD sc 0 + 1)) = linForm c pk + c sc := by
  have hscLen : sc < pk.length := hLen ▸ hsc
  unfold linForm
  have hMapEq :
      (List.range 48).map (fun j => c j * (pk.set sc (pk.getD sc 0 + 1)).getD j 0) =
      (List.range 48).map (fun j => c j * pk.getD j 0 + (if j = sc then c sc else 0)) := by
    refine List.map_congr_left fun j _ => ?_
    rw [list_getD_set_eq hscLen]
    by_cases hj : j = sc
    · subst hj
      simp [Nat.mul_add, Nat.mul_one]
    · simp [hj]
  rw [hMapEq, map_range_add_sum, sum_indicator_range hsc (c sc)]

theorem coarse_wt_ge_of_alt {sc sc0 : Nat}
    (hAlt : sc = sc0 ∨ sc = coarseAlt sc0) :
    slotWt sc ≤ coarseSlotWt sc0 ∧ grpWtS sc ≤ coarseGrpWtS sc0 := by
  unfold coarseSlotWt coarseGrpWtS
  rcases hAlt with rfl | rfl
  · exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩
  · exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-! ## Initializing `AllocSlotInvPres` -/

theorem allocSlotInvPres_of_witness {b : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 : MallocngSt}
    (hInv : MallocngFineInv 0 b ivs alignMap st0)
    {pk : List Nat} {pkSC pkSB : Nat}
    (hPk :
      pk.length = 48 ∧
      (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
      (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
      (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
      (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
      (straddle63Groups st0).length ≤ pkSC ∧
      straddle63Bytes st0 ≤ pkSB ∧
      linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
      linForm slotWt pk + pkSB ≤ b.cumSmallBytes)
    (sc : Nat) :
    AllocSlotInvPres sc pk alignMap st0 st0 :=
  AllocSlotInvPres.refl (sc := sc) hInv.groups_geom hInv.alignMap_wf.2
    hPk.2.2.1 hPk.2.2.2.1 hPk.2.2.2.2.1

/-! ## Slab `.claimed → .liveUser` Commit -/

private theorem filter_liveUser_set_claimed {xs : List SlotState} {idx : Nat}
    (hIdx : idx < xs.length)
    (hOld : ∀ p req eff, xs[idx]'hIdx ≠ .liveUser p req eff)
    (p : BitVec 64) (req eff : Nat) :
    ((xs.set idx (.liveUser p req eff)).filter isLiveUserSlot).length =
      (xs.filter isLiveUserSlot).length + 1 := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hIdx)
  | cons hd tl ih =>
    cases idx with
    | zero =>
      have hHd : isLiveUserSlot hd = false := by
        cases hd with
        | liveUser p0 r0 e0 => exact False.elim (hOld p0 r0 e0 rfl)
        | _ => rfl
      have hNew : isLiveUserSlot (.liveUser p req eff) = true := rfl
      simp only [List.set_cons_zero, List.filter_cons, hHd, hNew, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
    | succ idx' =>
      have hIdx' : idx' < tl.length := Nat.lt_of_succ_lt_succ hIdx
      have ihEq := ih hIdx' hOld
      simp only [List.set_cons_succ, List.filter_cons]
      cases isLiveUserSlot hd <;> simp [ihEq]

private theorem map_eq_self_of_mem {α : Type} {xs : List α} {f : α → α}
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

private theorem map_sum_replace_unique_meta {gs : List GroupDesc} {g1 g1' : GroupDesc}
    (hnd : (gs.map GroupDesc.metaPtr).Nodup) (hg1 : g1 ∈ gs)
    (f : GroupDesc → GroupDesc)
    (hfHit : f g1 = g1')
    (hfMiss : ∀ g, g.metaPtr ≠ g1.metaPtr → f g = g)
    {k : Nat} (hg1Sc : g1.sc = k) (hg1'Sc : g1'.sc = k) :
    (((gs.map f).filter (·.sc == k)).map groupLiveUserCount).sum + groupLiveUserCount g1 =
      ((gs.filter (·.sc == k)).map groupLiveUserCount).sum + groupLiveUserCount g1' := by
  induction gs with
  | nil => cases hg1
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hg1 with rfl | hTl
    · have hTailEq : tl.map f = tl :=
        map_eq_self_of_mem fun x hx => hfMiss x fun hEq =>
          hnd.1 (hEq ▸ List.mem_map_of_mem hx)
      have hSc1 : (g1.sc == k) = true := beq_iff_eq.mpr hg1Sc
      have hSc1' : (g1'.sc == k) = true := beq_iff_eq.mpr hg1'Sc
      simp only [List.map_cons, hfHit, hTailEq, List.filter_cons, hSc1, hSc1', ↓reduceIte,
        List.sum_cons]
      omega
    · have hNe : hd.metaPtr ≠ g1.metaPtr := fun hEq =>
        hnd.1 (hEq.symm ▸ List.mem_map_of_mem hTl)
      have ihEq := ih hnd.2 hTl
      simp only [List.map_cons, hfMiss hd hNe, List.filter_cons]
      cases hd.sc == k
      · exact ihEq
      · simp only [↓reduceIte, List.map_cons, List.sum_cons]
        omega

private theorem slotDecl63_congr_update {alignMap : BitVec 64 → Option Nat}
    {p : BitVec 64} {alNew : Option Nat} {s : SlotState}
    (hNotP : ∀ req eff, s ≠ .liveUser p req eff) :
    slotDecl63 (fun k => if k = p then alNew else alignMap k) s = slotDecl63 alignMap s := by
  cases s with
  | liveUser p0 req0 eff0 =>
    have hNe : p0 ≠ p := fun hEq => hNotP req0 eff0 (hEq ▸ rfl)
    simp [slotDecl63, hNe]
  | _ => rfl

/-- Updating `alignMap` at a fresh pointer `p` (`st.liveMap p = none` in a `MallocngWFInflight`
    state) leaves `large63DeclBytes st` unchanged. -/
theorem large63DeclBytes_update_fresh {inflight : Nat}
    {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} {alignMap : BitVec 64 → Option Nat}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {p : BitVec 64} (hFresh : st.liveMap p = none) (alNew : Option Nat) :
    large63DeclBytes st (fun k => if k = p then alNew else alignMap k) =
      large63DeclBytes st alignMap := by
  unfold large63DeclBytes large63Groups groups63
  congr 1
  refine List.map_congr_left fun g hg => ?_
  have hgMem : g ∈ st.groups := (List.mem_filter.mp (List.mem_filter.mp hg).1).1
  congr 1
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨idx, hIdx, rfl⟩ := List.getElem_of_mem hs
  refine slotDecl63_congr_update fun req eff hSlot => ?_
  have hLive := (hwf.liveMap_wf p req).mpr ⟨g, hgMem, idx, hIdx, eff, hSlot⟩
  rw [hFresh] at hLive
  cases hLive

/-- General slab `.claimed → .liveUser p req eff` commit into `MallocngFineInv 0 b'`. -/
theorem commit_claimed_slab_slot_general
    {base brkStart brk1 brk' : BitVec 64} {live1 peak1 live' peak' : Nat}
    {b b' : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 st' : MallocngSt}
    {pk : List Nat} {pkSC pkSB : Nat}
    {sc idx req eff effAlign : Nat} {p : BitVec 64}
    {g1 g1' : GroupDesc}
    (hsc : sc < 48)
    (hHal : 16 ≤ effAlign)
    (hFresh0 : st0.liveMap p = none)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hPk :
      pk.length = 48 ∧
      (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
      (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
      (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
      (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
      (straddle63Groups st0).length ≤ pkSC ∧
      straddle63Bytes st0 ≤ pkSB ∧
      linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
      linForm slotWt pk + pkSB ≤ b.cumSmallBytes)
    (hPres : AllocSlotInvPres sc pk alignMap st0 st1)
    (hwf1 : MallocngWFInflight 1 base brkStart brk1 live1 peak1 st1)
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hg1Mem : g1 ∈ st1.groups) (hg1Sc : g1.sc = sc)
    (hIdx : idx < g1.slots.length) (hClaimed : g1.slots[idx]'hIdx = .claimed)
    (hg1Same : FineGroupSameGeom g1' g1)
    (hg1'Slots : g1'.slots = g1.slots.set idx (.liveUser p req eff))
    (hGroups' : st'.groups = st1.groups.map fun g =>
      if g.metaPtr == g1.metaPtr then g1' else g)
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some req else st0.liveMap k)
    (hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas b')
    (hBudSmallB : b.cumSmallBytes + slotWt sc ≤ b'.cumSmallBytes)
    (hBudSmallG : b.cumSmallGroupsS + grpWtS sc ≤ b'.cumSmallGroupsS)
    (hBud63Eq : b.live63Bytes = b'.live63Bytes ∧ b.live63Count = b'.live63Count)
    (hBud63Peak : b'.live63Bytes ≤ b'.peak63Bytes ∧ b'.live63Count ≤ b'.peak63Count) :
    let alignMap' := fun k => if k = p then some effAlign else alignMap k
    MallocngFineInv 0 b' (dynamicRootRegions st') alignMap' st' := by
  intro alignMap'
  let f (g : GroupDesc) : GroupDesc := if g.metaPtr == g1.metaPtr then g1' else g
  have hGroupsF : st'.groups = st1.groups.map f := hGroups'
  have hNodup1 : (st1.groups.map GroupDesc.metaPtr).Nodup := hwf1.groups_nodup.1
  have hfHit : f g1 = g1' := by simp [f]
  have hfMiss : ∀ g, g.metaPtr ≠ g1.metaPtr → f g = g := fun g hNe => by simp [f, hNe]
  have hg1'Mem : g1' ∈ st'.groups := by
    rw [hGroupsF]
    exact hfHit ▸ List.mem_map_of_mem hg1Mem
  have hGeom' : ∀ g' ∈ st'.groups, GroupFineGeom g' := by
    intro g' hg'
    rw [hGroupsF] at hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    by_cases hEq : g.metaPtr = g1.metaPtr
    · have hgEq : g = g1 := nodup_metaPtr_eq hNodup1 hg hg1Mem hEq
      subst hgEq
      rw [hfHit]
      exact hg1Same.groupFineGeom_iff.mpr (hPres.groups_geom g hg)
    · rw [hfMiss g hEq]
      exact hPres.groups_geom g hg
  have hIdx' : idx < g1'.slots.length := by rw [hg1'Slots, List.length_set]; exact hIdx
  have hSlot' : g1'.slots[idx]'hIdx' = .liveUser p req eff := by
    cases g1'
    dsimp only at hg1'Slots hIdx' ⊢
    subst hg1'Slots
    exact List.getElem_set_self hIdx'
  have hg1'Sc : g1'.sc = sc := hg1Same.2.1.trans hg1Sc
  have hReqLt63 : ¬ Guaranteed63Threshold ≤ req := by
    intro hBig
    have h63 := no_slab_slot_ge_guaranteed63 (hwf'.groups_wf g1' hg1'Mem)
      (hGeom' g1' hg1'Mem) hIdx' hSlot' hBig
    omega
  have hNoP1 : ∀ g ∈ st1.groups, ∀ j (hj : j < g.slots.length) r0 e0,
      g.slots[j]'hj ≠ .liveUser p r0 e0 := by
    intro g hg j hj r0 e0 hEq
    obtain ⟨al, hAl, _⟩ := hPres.user_slots_wf g hg j hj p r0 e0 hEq
    obtain ⟨_, n, hLive0⟩ := hInv0.alignMap_wf.1 p al hAl
    rw [hFresh0] at hLive0
    cases hLive0
  have hAlignWf' : FineAlignWf st' alignMap' := by
    refine ⟨?_, ?_⟩
    · intro q al hAl
      dsimp only [alignMap'] at hAl
      by_cases hq : q = p
      · subst hq
        simp only [↓reduceIte, Option.some.injEq] at hAl
        subst hAl
        exact ⟨hHal, req, by simp [hLiveMap']⟩
      · simp only [hq, ↓reduceIte] at hAl
        obtain ⟨h16, n, hL0⟩ := hInv0.alignMap_wf.1 q al hAl
        exact ⟨h16, n, by simp [hLiveMap', hq, hL0]⟩
    · intro g' hg' j hj q r0 e0 hS
      rw [hGroupsF] at hg'
      obtain ⟨g, hg, hg'Eq⟩ := List.mem_map.mp hg'
      by_cases hMeta : g.metaPtr = g1.metaPtr
      · have hgEq : g = g1 := nodup_metaPtr_eq hNodup1 hg hg1Mem hMeta
        subst hgEq
        have hg'Eq1 : g' = g1' := hg'Eq.symm.trans hfHit
        subst hg'Eq1
        by_cases hjEq : j = idx
        · subst hjEq
          rw [hSlot'] at hS
          injection hS with hq hr he
          subst hq hr he
          exact ⟨effAlign, by simp [alignMap'], fun h63 => by omega⟩
        · have hj1 : j < g.slots.length := by rwa [hg1'Slots, List.length_set] at hj
          have hS1 : g.slots[j]'hj1 = .liveUser q r0 e0 := by
            have hGet : g'.slots[j]'hj = g.slots[j]'hj1 := by
              cases g'
              dsimp only at hg1'Slots hj ⊢
              subst hg1'Slots
              exact List.getElem_set_ne (Ne.symm hjEq) _
            exact hGet.symm.trans hS
          have hqNe : q ≠ p := fun hEq => hNoP1 g hg j hj1 r0 e0 (hEq ▸ hS1)
          obtain ⟨al, hAl, hBnd⟩ := hPres.user_slots_wf g hg j hj1 q r0 e0 hS1
          exact ⟨al, by simp [alignMap', hqNe, hAl], fun h63 => by omega⟩
      · have hg'EqG : g' = g := hg'Eq.symm.trans (hfMiss g hMeta)
        subst hg'EqG
        have hqNe : q ≠ p := fun hEq => hNoP1 g' hg j hj r0 e0 (hEq ▸ hS)
        obtain ⟨al, hAl, hBnd⟩ := hPres.user_slots_wf g' hg j hj q r0 e0 hS
        exact ⟨al, by simp [alignMap', hqNe, hAl], hBnd⟩
  have hGeomRel : List.Forall₂ FineGroupSameGeom st'.groups st1.groups := by
    rw [hGroupsF]
    have hMemGeom : ∀ g ∈ st1.groups, FineGroupSameGeom (f g) g := by
      intro g hg
      by_cases hMeta : g.metaPtr = g1.metaPtr
      · have hgEq : g = g1 := nodup_metaPtr_eq hNodup1 hg hg1Mem hMeta
        subst hgEq; rw [hfHit]; exact hg1Same
      · rw [hfMiss g hMeta]; exact FineGroupSameGeom.refl g
    have hNd := hNodup1
    generalize st1.groups = gs at hNd hMemGeom ⊢
    induction gs with
    | nil => exact .nil
    | cons a l ih =>
      rw [List.map_cons, List.nodup_cons] at hNd
      exact .cons (hMemGeom a List.mem_cons_self)
        (ih hNd.2 fun g hg => hMemGeom g (List.mem_cons_of_mem _ hg))
  have hGroups63Eq : groups63 st' = groups63 st1 := by
    unfold groups63
    rw [hGroupsF]
    have hAux : ∀ {gs : List GroupDesc},
        (∀ g ∈ gs, g.metaPtr = g1.metaPtr → g.sc = sc) →
        (gs.map f).filter (·.sc == 63) = gs.filter (·.sc == 63) := by
      intro gs hScEq
      induction gs with
      | nil => rfl
      | cons a l ih =>
        have ihEq := ih fun g hg => hScEq g (List.mem_cons_of_mem _ hg)
        by_cases hMeta : a.metaPtr = g1.metaPtr
        · have haSc : a.sc = sc := hScEq a List.mem_cons_self hMeta
          have hfA : f a = g1' := by simp [f, hMeta]
          have h63A : (a.sc == 63) = false := by rw [beq_eq_false_iff_ne, haSc]; omega
          have h63A' : (g1'.sc == 63) = false := by rw [beq_eq_false_iff_ne, hg1'Sc]; omega
          simp only [List.map_cons, hfA, List.filter_cons, h63A, h63A', Bool.false_eq_true, ↓reduceIte]
          exact ihEq
        · simp only [List.map_cons, hfMiss a hMeta, List.filter_cons]
          cases a.sc == 63 <;> simp [ihEq]
    exact hAux fun g hg hMeta => (nodup_metaPtr_eq hNodup1 hg hg1Mem hMeta) ▸ hg1Sc
  have hLarge63Bytes : large63DeclBytes st' alignMap' = b.live63Bytes := by
    have hEq1 : large63DeclBytes st' alignMap' = large63DeclBytes st1 alignMap' := by
      unfold large63DeclBytes large63Groups; rw [hGroups63Eq]
    have hEq2 : large63DeclBytes st1 alignMap' = large63DeclBytes st1 alignMap := by
      unfold large63DeclBytes large63Groups groups63
      congr 1
      refine List.map_congr_left fun g hg => ?_
      have hgMem : g ∈ st1.groups := (List.mem_filter.mp (List.mem_filter.mp hg).1).1
      congr 1
      refine List.map_congr_left fun s hs => ?_
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      exact slotDecl63_congr_update fun r0 e0 hS => hNoP1 g hgMem j hj r0 e0 hS
    rw [hEq1, hEq2, hPres.large63_eq.1, hInv0.live63_eq.1]
  have hLarge63Cnt : (large63Groups st').length = b.live63Count := by
    have hEq1 : large63Groups st' = large63Groups st1 := by
      unfold large63Groups; rw [hGroups63Eq]
    rw [hEq1, hPres.large63_eq.2, hInv0.live63_eq.2]
  let pk' := pk.set sc (pk.getD sc 0 + 1)
  have hscLen : sc < pk.length := hPk.1 ▸ hsc
  have hPkMono : ∀ k, pk.getD k 0 ≤ pk'.getD k 0 := list_set_succ_le_getD hscLen
  have hLiveCntG1' : groupLiveUserCount g1' = groupLiveUserCount g1 + 1 := by
    rw [groupLiveUserCount_eq_filter, groupLiveUserCount_eq_filter, hg1'Slots]
    refine filter_liveUser_set_claimed hIdx ?_ p req eff
    intro q r0 e0 hEq; rw [hClaimed] at hEq; cases hEq
  have hAllGroupsEq : ∀ k, (allGroups st' k).length = (allGroups st1 k).length := by
    intro k; unfold allGroups
    have hRel := hGeomRel
    generalize st'.groups = xs, st1.groups = ys at hRel
    induction hRel with
    | nil => rfl
    | @cons x y _ _ hr _ ih =>
      simp only [List.filter_cons, hr.2.1]
      cases y.sc == k <;> simp [ih]
  have hNestedEdgeEq : ∀ ch pSc, (nestedEdge st' ch pSc).length = (nestedEdge st1 ch pSc).length := by
    intro ch pSc; unfold nestedEdge
    have hRel := hGeomRel
    generalize st'.groups = xs, st1.groups = ys at hRel
    induction hRel with
    | nil => rfl
    | @cons x y _ _ hr _ ih =>
      have hDecEq : decide (x.sc = ch ∧ x.maplen = 0 ∧ x.nestedCap = slotStride pSc - 4) =
          decide (y.sc = ch ∧ y.maplen = 0 ∧ y.nestedCap = slotStride pSc - 4) := by
        rw [hr.2.1, hr.2.2.1, hr.2.2.2.1]
      simp only [List.filter_cons, hDecEq]
      cases h : decide (y.sc = ch ∧ y.maplen = 0 ∧ y.nestedCap = slotStride pSc - 4)
      · exact ih
      · simp only [↓reduceIte, List.length_cons, ih]
  have hRootBytesEq : ∀ k, rootBytes st' k = rootBytes st1 k := by
    intro k; unfold rootBytes
    have hRel := hGeomRel
    generalize st'.groups = xs, st1.groups = ys at hRel
    induction hRel with
    | nil => rfl
    | @cons x y _ _ hr _ ih =>
      have hDecEq : decide (x.sc = k ∧ 0 < x.maplen) = decide (y.sc = k ∧ 0 < y.maplen) := by
        rw [hr.2.1, hr.2.2.1]
      simp only [List.filter_cons, hDecEq]
      cases decide (y.sc = k ∧ 0 < y.maplen)
      · exact ih
      · simp only [↓reduceIte, List.map_cons, List.sum_cons, hr.2.2.1, ih]
  refine {
    ivs_eq := fun _ => rfl
    groups_geom := hGeom'
    alignMap_wf := hAlignWf'
    live63_eq := ⟨hLarge63Bytes.trans hBud63Eq.1, hLarge63Cnt.trans hBud63Eq.2⟩
    live63_le_peak := hBud63Peak
    metaAreas_le := hMetaLe'
    small_witness := ⟨pk', pkSC, pkSB, ?_⟩
  }
  refine ⟨by rw [List.length_set, hPk.1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [list_getD_set_eq hscLen]
    by_cases hkEq : k = sc
    · subst hkEq
      simp only [↓reduceIte]
      have hSumEq := map_sum_replace_unique_meta hNodup1 hg1Mem f hfHit hfMiss hg1Sc hg1'Sc
      unfold liveSlotsInClass allGroups
      rw [hGroupsF]
      have hLive1 : ((st1.groups.filter (·.sc == k)).map groupLiveUserCount).sum ≤ pk.getD k 0 := by
        change liveSlotsInClass st1 k ≤ pk.getD k 0
        rw [hPres.live_eq k]
        exact hPk.2.1 k hk
      have := hLiveCntG1'
      omega
    · simp only [hkEq, ↓reduceIte]
      have hMissSc : ∀ g ∈ st1.groups, ((f g).sc == k) = (g.sc == k) ∧
          ((g.sc == k) = true → groupLiveUserCount (f g) = groupLiveUserCount g) := by
        intro g hg
        by_cases hMeta : g.metaPtr = g1.metaPtr
        · have hgEq : g = g1 := nodup_metaPtr_eq hNodup1 hg hg1Mem hMeta
          subst hgEq; rw [hfHit]
          have hF1 : (g.sc == k) = false := by rw [beq_eq_false_iff_ne, hg1Sc]; omega
          have hF2 : (g1'.sc == k) = false := by rw [beq_eq_false_iff_ne, hg1'Sc]; omega
          exact ⟨hF2.trans hF1.symm, fun hT => by rw [hF1] at hT; cases hT⟩
        · rw [hfMiss g hMeta]
          exact ⟨rfl, fun _ => rfl⟩
      have hUnchanged : liveSlotsInClass st' k = liveSlotsInClass st1 k := by
        unfold liveSlotsInClass allGroups
        rw [hGroupsF]
        have hNd := hNodup1
        generalize st1.groups = gs at hNd hMissSc ⊢
        induction gs with
        | nil => rfl
        | cons a l ih =>
          rw [List.map_cons, List.nodup_cons] at hNd
          have hA := hMissSc a List.mem_cons_self
          have ihEq := ih hNd.2 fun g hg => hMissSc g (List.mem_cons_of_mem _ hg)
          simp only [List.map_cons, List.filter_cons, hA.1]
          cases hBeq : a.sc == k
          · exact ihEq
          · simp only [↓reduceIte, List.map_cons, List.sum_cons, hA.2 hBeq, ihEq]
      rw [hUnchanged, hPres.live_eq k]
      exact hPk.2.1 k hk
  · intro k hk
    rw [hAllGroupsEq k]
    exact Nat.le_trans (hPres.groups_le k hk) (gBound_mono hk fun j _ => hPkMono j)
  · intro ch hch pSc hpSc
    rw [hNestedEdgeEq ch pSc]
    exact Nat.le_trans (hPres.edges_le ch hch pSc hpSc) (edgeBound_mono pSc hch fun j _ => hPkMono j)
  · intro k hk
    rw [hRootBytesEq k]
    exact Nat.le_trans (hPres.roots_le k hk) (rBound_mono hk fun j _ => hPkMono j)
  · have hEq : straddle63Groups st' = straddle63Groups st1 := by
      unfold straddle63Groups; rw [hGroups63Eq]
    rw [hEq, hPres.straddle63_eq.1]
    exact hPk.2.2.2.2.2.1
  · have hEq : straddle63Bytes st' = straddle63Bytes st1 := by
      unfold straddle63Bytes straddle63Groups; rw [hGroups63Eq]
    rw [hEq, hPres.straddle63_eq.2]
    exact hPk.2.2.2.2.2.2.1
  · rw [linForm_set_succ grpWtS hPk.1 hsc]
    have hBase := hPk.2.2.2.2.2.2.2.1
    omega
  · rw [linForm_set_succ slotWt hPk.1 hsc]
    have hBase := hPk.2.2.2.2.2.2.2.2
    omega

/-! ## Inflight Invariant Recovery and Slab Corollaries -/

/-- Synthesizes a coarse `MallocngBudget` witness satisfying `MallocngCountIvsWF` for any
    `MallocngSt` and any `liveCost`/`peakCost`. -/
def synthCoarseBudget (liveCost peakCost : Nat) (st : MallocngSt) : MallocngBudget :=
  let pk := 128 + totalLiveCount st + (dynamicRootRegions st).length + 101 * st.metaAreas.length
  { liveCost := liveCost
    peakCost := peakCost
    liveCount := totalLiveCount st
    peakCount := pk }

theorem synthCoarseBudget_countIvsWF {liveCost peakCost : Nat} (st : MallocngSt)
    (hGrp : Cost.GroupsGrpBound 128 st.groups) :
    MallocngCountIvsWF (synthCoarseBudget liveCost peakCost st) (dynamicRootRegions st) st := by
  dsimp only [synthCoarseBudget, MallocngCountIvsWF]
  refine ⟨by omega, Nat.le_refl _, rfl, by omega, by omega, hGrp.mono (by omega)⟩

/-- Reconstructs `MallocngFineInv inflight b` at any intermediate `alloc_slot` state satisfying
    `AllocSlotInvPres`. -/
theorem mallocngFineInv_of_allocSlotInvPres {inflight : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 : MallocngSt}
    {pk : List Nat} {pkSC pkSB sc : Nat}
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hPk :
      pk.length = 48 ∧
      (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
      (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
      (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
      (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
      (straddle63Groups st0).length ≤ pkSC ∧
      straddle63Bytes st0 ≤ pkSB ∧
      linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
      linForm slotWt pk + pkSB ≤ b.cumSmallBytes)
    (hPres : AllocSlotInvPres sc pk alignMap st0 st1)
    (hLiveMap1 : st1.liveMap = st0.liveMap)
    (hMeta1 : st1.metaAreas.length ≤ fineMaxMetaAreas b) :
    MallocngFineInv inflight b (dynamicRootRegions st1) alignMap st1 :=
  { ivs_eq := fun _ => rfl
    groups_geom := hPres.groups_geom
    alignMap_wf := ⟨fun q al hAl => by
      obtain ⟨h16, n, hL0⟩ := hInv0.alignMap_wf.1 q al hAl
      exact ⟨h16, n, hLiveMap1 ▸ hL0⟩, hPres.user_slots_wf⟩
    live63_eq := ⟨hPres.large63_eq.1.trans hInv0.live63_eq.1,
      hPres.large63_eq.2.trans hInv0.live63_eq.2⟩
    live63_le_peak := hInv0.live63_le_peak
    metaAreas_le := hMeta1
    small_witness := ⟨pk, pkSC, pkSB, hPk.1,
      fun k hk => hPres.live_eq k ▸ hPk.2.1 k hk,
      hPres.groups_le, hPres.edges_le, hPres.roots_le,
      hPres.straddle63_eq.1 ▸ hPk.2.2.2.2.2.1,
      hPres.straddle63_eq.2 ▸ hPk.2.2.2.2.2.2.1,
      hPk.2.2.2.2.2.2.2.1, hPk.2.2.2.2.2.2.2.2⟩ }

/-- Slab commit specialized to `FineBudget.stepAligned align req b` (`malloc` / `calloc` at `align = 16`,
    and `aligned_alloc` / `posix_memalign` at general `align`). -/
theorem commit_claimed_slab_slot_aligned
    {base brkStart brk1 brk' : BitVec 64} {live1 peak1 live' peak' : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 st' : MallocngSt}
    {pk : List Nat} {pkSC pkSB : Nat}
    {sc idx align req eff : Nat} {p : BitVec 64}
    {g1 g1' : GroupDesc}
    (hsc : sc < 48)
    (hEffSmall : req + (max align 16 - 16) ≤ MmapThresholdReq)
    (hAlt : sc = sizeToClassUnits ((req + (max align 16 - 16) + 3) / 16) ∨
      sc = coarseAlt (sizeToClassUnits ((req + (max align 16 - 16) + 3) / 16)))
    (hFresh0 : st0.liveMap p = none)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hPk :
      pk.length = 48 ∧
      (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
      (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
      (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
      (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
      (straddle63Groups st0).length ≤ pkSC ∧
      straddle63Bytes st0 ≤ pkSB ∧
      linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
      linForm slotWt pk + pkSB ≤ b.cumSmallBytes)
    (hPres : AllocSlotInvPres sc pk alignMap st0 st1)
    (hwf1 : MallocngWFInflight 1 base brkStart brk1 live1 peak1 st1)
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hg1Mem : g1 ∈ st1.groups) (hg1Sc : g1.sc = sc)
    (hIdx : idx < g1.slots.length) (hClaimed : g1.slots[idx]'hIdx = .claimed)
    (hg1Same : FineGroupSameGeom g1' g1)
    (hg1'Slots : g1'.slots = g1.slots.set idx (.liveUser p req eff))
    (hGroups' : st'.groups = st1.groups.map fun g =>
      if g.metaPtr == g1.metaPtr then g1' else g)
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some req else st0.liveMap k)
    (hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas (FineBudget.stepAligned align req b)) :
    let alignMap' := fun k => if k = p then some (max align 16) else alignMap k
    MallocngFineInv 0 (FineBudget.stepAligned align req b) (dynamicRootRegions st') alignMap' st' := by
  have hNot63 : ¬ Guaranteed63Threshold ≤ req := by
    unfold MmapThresholdReq at hEffSmall
    unfold Guaranteed63Threshold
    omega
  have hWt := coarse_wt_ge_of_alt hAlt
  refine commit_claimed_slab_slot_general hsc (Nat.le_max_right align 16) hFresh0 hInv0 hPk
    hPres hwf1 hwf' hg1Mem hg1Sc hIdx hClaimed hg1Same hg1'Slots hGroups' hLiveMap' hMetaLe'
    ?_ ?_ ?_ ?_
  · simp only [FineBudget.stepAligned, hNot63, hEffSmall, ↓reduceIte]
    have := hWt.1; omega
  · simp only [FineBudget.stepAligned, hNot63, hEffSmall, ↓reduceIte]
    have := hWt.2; omega
  · simp [FineBudget.stepAligned, hNot63, hEffSmall]
  · simp only [FineBudget.stepAligned, hNot63, hEffSmall, ↓reduceIte, finePeak63Bytes, finePeak63Count]
    exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- Slab commit specialized to `FineBudget.stepReallocAdd align req b` (`realloc` Stage 4 OOP). -/
theorem commit_claimed_slab_slot_reallocAdd
    {base brkStart brk1 brk' : BitVec 64} {live1 peak1 live' peak' : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 st' : MallocngSt}
    {pk : List Nat} {pkSC pkSB : Nat}
    {sc idx align req eff : Nat} {p : BitVec 64}
    {g1 g1' : GroupDesc}
    (hsc : sc < 48)
    (hSmall : req ≤ MmapThresholdReq)
    (hAlt : sc = sizeToClassUnits ((req + 3) / 16) ∨
      sc = coarseAlt (sizeToClassUnits ((req + 3) / 16)))
    (hFresh0 : st0.liveMap p = none)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hPk :
      pk.length = 48 ∧
      (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
      (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
      (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
      (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
      (straddle63Groups st0).length ≤ pkSC ∧
      straddle63Bytes st0 ≤ pkSB ∧
      linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
      linForm slotWt pk + pkSB ≤ b.cumSmallBytes)
    (hPres : AllocSlotInvPres sc pk alignMap st0 st1)
    (hwf1 : MallocngWFInflight 1 base brkStart brk1 live1 peak1 st1)
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hg1Mem : g1 ∈ st1.groups) (hg1Sc : g1.sc = sc)
    (hIdx : idx < g1.slots.length) (hClaimed : g1.slots[idx]'hIdx = .claimed)
    (hg1Same : FineGroupSameGeom g1' g1)
    (hg1'Slots : g1'.slots = g1.slots.set idx (.liveUser p req eff))
    (hGroups' : st'.groups = st1.groups.map fun g =>
      if g.metaPtr == g1.metaPtr then g1' else g)
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some req else st0.liveMap k)
    (hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas (FineBudget.stepReallocAdd align req b)) :
    let alignMap' := fun k => if k = p then some (max align 16) else alignMap k
    MallocngFineInv 0 (FineBudget.stepReallocAdd align req b) (dynamicRootRegions st') alignMap' st' := by
  have hNot63 : ¬ Guaranteed63Threshold ≤ req := by
    unfold MmapThresholdReq at hSmall
    unfold Guaranteed63Threshold
    omega
  have hWt := coarse_wt_ge_of_alt hAlt
  refine commit_claimed_slab_slot_general hsc (Nat.le_max_right align 16) hFresh0 hInv0 hPk
    hPres hwf1 hwf' hg1Mem hg1Sc hIdx hClaimed hg1Same hg1'Slots hGroups' hLiveMap' hMetaLe'
    ?_ ?_ ?_ ?_
  · simp only [FineBudget.stepReallocAdd, hNot63, hSmall, ↓reduceIte]
    have := hWt.1; omega
  · simp only [FineBudget.stepReallocAdd, hNot63, hSmall, ↓reduceIte]
    have := hWt.2; omega
  · simp [FineBudget.stepReallocAdd, hNot63]
  · simp only [FineBudget.stepReallocAdd, hNot63, ↓reduceIte, finePeak63Bytes, finePeak63Count]
    exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-! ## Direct `sc = 63` `mmap` Group Commit -/

/-- General `sc = 63` individual-`mmap` group commit (`cg :: st1.groups`) into `MallocngFineInv 0 b'`.
    Routes `Guaranteed63Threshold ≤ req` to `large63Groups` (`live63Bytes` / `live63Count`) and
    `req < Guaranteed63Threshold` to `straddle63Groups` (`pkStraddleCnt + 1`, `pkStraddleBytes + c`). -/
theorem commit_mmap63_group_general
    {b b' : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 st' : MallocngSt}
    {cg : GroupDesc} {p : BitVec 64} {req eff effAlign : Nat}
    (hHal : 16 ≤ effAlign)
    (hFresh0 : st0.liveMap p = none)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hSame1 : FineSameGroupsSlotKind st1.groups st0.groups)
    (hGroups' : st'.groups = cg :: st1.groups)
    (hCgSc : cg.sc = 63)
    (hCgSlots : cg.slots = [.liveUser p req eff])
    (hCgEff : eff - max req MallocngMinBlockCost ≤ effAlign - 16)
    (hCgMap : cg.maplen * 4096 ≤ declCost63 req effAlign)
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some req else st0.liveMap k)
    (hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas b')
    (hBud63Peak : b'.live63Bytes ≤ b'.peak63Bytes ∧ b'.live63Count ≤ b'.peak63Count)
    (hLargeBud : Guaranteed63Threshold ≤ req →
      b'.live63Bytes = b.live63Bytes + declCost63 req effAlign ∧
      b'.live63Count = b.live63Count + 1 ∧
      b.cumSmallBytes ≤ b'.cumSmallBytes ∧
      b.cumSmallGroupsS ≤ b'.cumSmallGroupsS)
    (hStraddleBud : ¬ Guaranteed63Threshold ≤ req →
      b'.live63Bytes = b.live63Bytes ∧
      b'.live63Count = b.live63Count ∧
      b.cumSmallBytes + declCost63 req effAlign ≤ b'.cumSmallBytes ∧
      b.cumSmallGroupsS + FineScale ≤ b'.cumSmallGroupsS) :
    let alignMap' := fun k => if k = p then some effAlign else alignMap k
    MallocngFineInv 0 b' (dynamicRootRegions st') alignMap' st' := by
  intro alignMap'
  obtain ⟨hPGeom, hPUser, hPLive, hPAll, hPEdge, hPRoot, hPL63B, hPL63C, hPS63C, hPS63B⟩ :=
    fineSameGroupsSlotKind_preserves_all (alignMap := alignMap) hSame1
  have hGeom1 : ∀ g ∈ st1.groups, GroupFineGeom g := hPGeom hInv0.groups_geom
  have hUser1 := hPUser hInv0.alignMap_wf.2
  clear hPGeom hPUser
  have hNoP1 : ∀ g ∈ st1.groups, ∀ j (hj : j < g.slots.length) r0 e0,
      g.slots[j]'hj ≠ .liveUser p r0 e0 := by
    intro g hg j hj r0 e0 hEq
    obtain ⟨al, hAl, _⟩ := hUser1 g hg j hj p r0 e0 hEq
    obtain ⟨_, n, hL0⟩ := hInv0.alignMap_wf.1 p al hAl
    rw [hFresh0] at hL0; cases hL0
  have hCgGeom : GroupFineGeom cg :=
    ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩
  have hGeom' : ∀ g' ∈ st'.groups, GroupFineGeom g' := by
    intro g' hg'
    rw [hGroups'] at hg'
    rcases List.mem_cons.mp hg' with rfl | hg1
    · exact hCgGeom
    · exact hGeom1 g' hg1
  have hAlignWf' : FineAlignWf st' alignMap' := by
    refine ⟨?_, ?_⟩
    · intro q al hAl
      dsimp only [alignMap'] at hAl
      by_cases hq : q = p
      · subst hq
        simp only [↓reduceIte, Option.some.injEq] at hAl
        subst hAl
        exact ⟨hHal, req, by simp [hLiveMap']⟩
      · simp only [hq, ↓reduceIte] at hAl
        obtain ⟨h16, n, hL0⟩ := hInv0.alignMap_wf.1 q al hAl
        exact ⟨h16, n, by simp [hLiveMap', hq, hL0]⟩
    · intro g' hg' j hj q r0 e0 hS
      rw [hGroups'] at hg'
      rcases List.mem_cons.mp hg' with rfl | hg1
      · have hj0 : j = 0 := by rw [hCgSlots, List.length_singleton] at hj; omega
        subst hj0
        have hS0 : g'.slots[0]'hj = .liveUser p req eff := by
          cases g'; dsimp only at hCgSlots hj ⊢; subst hCgSlots; rfl
        rw [hS0] at hS
        injection hS with hq hr he
        subst hq hr he
        exact ⟨effAlign, by simp [alignMap'], fun _ => ⟨hCgEff, hCgMap⟩⟩
      · have hqNe : q ≠ p := fun hEq => hNoP1 g' hg1 j hj r0 e0 (hEq ▸ hS)
        obtain ⟨al, hAl, hBnd⟩ := hUser1 g' hg1 j hj q r0 e0 hS
        exact ⟨al, by simp [alignMap', hqNe, hAl], hBnd⟩
  have hAllEq : ∀ k < 48, allGroups st' k = allGroups st1 k := by
    intro k hk
    unfold allGroups
    have hF : (cg.sc == k) = false := by rw [beq_eq_false_iff_ne, hCgSc]; omega
    simp [hGroups', hF]
  have hLiveEq : ∀ k < 48, liveSlotsInClass st' k = liveSlotsInClass st0 k := by
    intro k hk
    unfold liveSlotsInClass
    rw [hAllEq k hk]
    exact hPLive k
  have hEdgeEq : ∀ ch < 48, ∀ pSc < 48,
      (nestedEdge st' ch pSc).length = (nestedEdge st0 ch pSc).length := by
    intro ch hch pSc _
    have hHead : nestedEdge st' ch pSc = nestedEdge st1 ch pSc := by
      unfold nestedEdge
      have hNe : cg.sc ≠ ch := by omega
      simp [hGroups', hNe]
    rw [hHead, hPEdge ch pSc]
  have hRootEq : ∀ k < 48, rootBytes st' k = rootBytes st0 k := by
    intro k hk
    have hHead : rootBytes st' k = rootBytes st1 k := by
      unfold rootBytes
      have hNe : cg.sc ≠ k := by omega
      simp [hGroups', hNe]
    rw [hHead, hPRoot k]
  have hLarge1Decl : large63DeclBytes st1 alignMap' = b.live63Bytes := by
    have hEqAlign : large63DeclBytes st1 alignMap' = large63DeclBytes st1 alignMap := by
      unfold large63DeclBytes large63Groups groups63
      congr 1
      refine List.map_congr_left fun g hg => ?_
      have hgMem : g ∈ st1.groups := (List.mem_filter.mp (List.mem_filter.mp hg).1).1
      congr 1
      refine List.map_congr_left fun s hs => ?_
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      exact slotDecl63_congr_update fun r0 e0 hS => hNoP1 g hgMem j hj r0 e0 hS
    rw [hEqAlign, hPL63B, hInv0.live63_eq.1]
  have hGroups63' : groups63 st' = cg :: groups63 st1 := by
    unfold groups63
    have hT : (cg.sc == 63) = true := beq_iff_eq.mpr hCgSc
    simp [hGroups', hT]
  obtain ⟨pk, pkSC, pkSB, hPkLen, hPkLive, hPkAll, hPkEdge, hPkRoot,
    hPkSC, hPkSB, hPkCumG, hPkCumB⟩ := hInv0.small_witness
  by_cases hBig : Guaranteed63Threshold ≤ req
  · have hLB := hLargeBud hBig
    have hIsLarge : isLarge63Group cg = true := by
      simp [isLarge63Group, hCgSlots, slotIs63Large, hBig]
    have hLargeGroups' : large63Groups st' = cg :: large63Groups st1 := by
      unfold large63Groups; rw [hGroups63', List.filter_cons]; simp [hIsLarge]
    have hStrGroups' : straddle63Groups st' = straddle63Groups st1 := by
      unfold straddle63Groups; rw [hGroups63', List.filter_cons]; simp [hIsLarge]
    have hCgDecl : (cg.slots.map (slotDecl63 alignMap')).sum = declCost63 req effAlign := by
      simp [hCgSlots, slotDecl63, hBig, alignMap']
    have hLargeBytes' : large63DeclBytes st' alignMap' = b'.live63Bytes := by
      have hStep : large63DeclBytes st' alignMap' =
          (cg.slots.map (slotDecl63 alignMap')).sum + large63DeclBytes st1 alignMap' := by
        unfold large63DeclBytes; rw [hLargeGroups', List.map_cons, List.sum_cons]
      rw [hStep, hCgDecl, hLarge1Decl, hLB.1]; omega
    have hLargeCnt' : (large63Groups st').length = b'.live63Count := by
      rw [hLargeGroups', List.length_cons, hPL63C, hInv0.live63_eq.2, hLB.2.1]
    have hStrBytesEq : straddle63Bytes st' = straddle63Bytes st1 := by
      unfold straddle63Bytes; rw [hStrGroups']
    refine {
      ivs_eq := fun _ => rfl
      groups_geom := hGeom'
      alignMap_wf := hAlignWf'
      live63_eq := ⟨hLargeBytes', hLargeCnt'⟩
      live63_le_peak := hBud63Peak
      metaAreas_le := hMetaLe'
      small_witness := ⟨pk, pkSC, pkSB, hPkLen,
        fun k hk => (hLiveEq k hk).symm ▸ hPkLive k hk,
        fun k hk => by rw [hAllEq k hk, hPAll k]; exact hPkAll k hk,
        fun ch hch pSc hpSc => (hEdgeEq ch hch pSc hpSc).symm ▸ hPkEdge ch hch pSc hpSc,
        fun k hk => (hRootEq k hk).symm ▸ hPkRoot k hk,
        by rw [hStrGroups', hPS63C]; exact hPkSC,
        by rw [hStrBytesEq, hPS63B]; exact hPkSB,
        Nat.le_trans hPkCumG hLB.2.2.2,
        Nat.le_trans hPkCumB hLB.2.2.1⟩
    }
  · have hSB := hStraddleBud hBig
    have hIsLarge : isLarge63Group cg = false := by
      simp [isLarge63Group, hCgSlots, slotIs63Large, hBig]
    have hLargeGroups' : large63Groups st' = large63Groups st1 := by
      unfold large63Groups; rw [hGroups63', List.filter_cons]; simp [hIsLarge]
    have hStrGroups' : straddle63Groups st' = cg :: straddle63Groups st1 := by
      unfold straddle63Groups; rw [hGroups63', List.filter_cons]; simp [hIsLarge]
    have hLargeBytes' : large63DeclBytes st' alignMap' = b'.live63Bytes := by
      have hStep : large63DeclBytes st' alignMap' = large63DeclBytes st1 alignMap' := by
        unfold large63DeclBytes; rw [hLargeGroups']
      rw [hStep, hLarge1Decl, hSB.1]
    have hLargeCnt' : (large63Groups st').length = b'.live63Count := by
      rw [hLargeGroups', hPL63C, hInv0.live63_eq.2, hSB.2.1]
    have hStrBytes' : straddle63Bytes st' ≤ pkSB + declCost63 req effAlign := by
      have hStep : straddle63Bytes st' = cg.maplen * 4096 + straddle63Bytes st1 := by
        unfold straddle63Bytes; rw [hStrGroups', List.map_cons, List.sum_cons]
      rw [hStep, hPS63B]
      exact Nat.add_comm _ _ ▸ Nat.add_le_add hPkSB hCgMap
    refine {
      ivs_eq := fun _ => rfl
      groups_geom := hGeom'
      alignMap_wf := hAlignWf'
      live63_eq := ⟨hLargeBytes', hLargeCnt'⟩
      live63_le_peak := hBud63Peak
      metaAreas_le := hMetaLe'
      small_witness := ⟨pk, pkSC + 1, pkSB + declCost63 req effAlign, hPkLen,
        fun k hk => (hLiveEq k hk).symm ▸ hPkLive k hk,
        fun k hk => by rw [hAllEq k hk, hPAll k]; exact hPkAll k hk,
        fun ch hch pSc hpSc => (hEdgeEq ch hch pSc hpSc).symm ▸ hPkEdge ch hch pSc hpSc,
        fun k hk => (hRootEq k hk).symm ▸ hPkRoot k hk,
        by rw [hStrGroups', List.length_cons, hPS63C]; exact Nat.add_le_add_right hPkSC 1,
        hStrBytes',
        by rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_right hPkCumG _) hSB.2.2.2,
        by rw [← Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_right hPkCumB _) hSB.2.2.1⟩
    }

/-- `sc = 63` `mmap` commit specialized to `FineBudget.stepAligned align req b`
    when `¬ (req + (max align 16 - 16) ≤ MmapThresholdReq)`. -/
theorem commit_mmap63_group_aligned
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 st' : MallocngSt}
    {cg : GroupDesc} {p : BitVec 64} {align req eff : Nat}
    (hEffLarge : ¬ (req + (max align 16 - 16) ≤ MmapThresholdReq))
    (hFresh0 : st0.liveMap p = none)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hSame1 : FineSameGroupsSlotKind st1.groups st0.groups)
    (hGroups' : st'.groups = cg :: st1.groups)
    (hCgSc : cg.sc = 63)
    (hCgSlots : cg.slots = [.liveUser p req eff])
    (hCgEff : eff - max req MallocngMinBlockCost ≤ max align 16 - 16)
    (hCgMap : cg.maplen * 4096 ≤ declCost63 req (max align 16))
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some req else st0.liveMap k)
    (hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas (FineBudget.stepAligned align req b)) :
    let alignMap' := fun k => if k = p then some (max align 16) else alignMap k
    MallocngFineInv 0 (FineBudget.stepAligned align req b) (dynamicRootRegions st') alignMap' st' := by
  refine commit_mmap63_group_general (Nat.le_max_right align 16) hFresh0 hInv0 hSame1 hGroups'
    hCgSc hCgSlots hCgEff hCgMap hLiveMap' hMetaLe' ?_ ?_ ?_
  · by_cases hBig : Guaranteed63Threshold ≤ req
    · simp only [FineBudget.stepAligned, hBig, ↓reduceIte]
      exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
    · simp only [FineBudget.stepAligned, hBig, hEffLarge, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
  · intro hBig
    simp [FineBudget.stepAligned, hBig]
  · intro hBig
    simp [FineBudget.stepAligned, hBig, hEffLarge]

/-- `sc = 63` `mmap` commit specialized to `FineBudget.stepReallocAdd align req b`
    (`realloc` Stage 4 OOP when `malloc(req)` allocates a fresh `sc = 63` group). -/
theorem commit_mmap63_group_reallocAdd
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st1 st' : MallocngSt}
    {cg : GroupDesc} {p : BitVec 64} {align req eff : Nat}
    (hFresh0 : st0.liveMap p = none)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hSame1 : FineSameGroupsSlotKind st1.groups st0.groups)
    (hGroups' : st'.groups = cg :: st1.groups)
    (hCgSc : cg.sc = 63)
    (hCgSlots : cg.slots = [.liveUser p req eff])
    (hCgEff : eff - max req MallocngMinBlockCost ≤ max align 16 - 16)
    (hCgMap : cg.maplen * 4096 ≤ declCost63 req (max align 16))
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some req else st0.liveMap k)
    (hMetaLe' : st'.metaAreas.length ≤ fineMaxMetaAreas (FineBudget.stepReallocAdd align req b)) :
    let alignMap' := fun k => if k = p then some (max align 16) else alignMap k
    MallocngFineInv 0 (FineBudget.stepReallocAdd align req b) (dynamicRootRegions st') alignMap' st' := by
  refine commit_mmap63_group_general (Nat.le_max_right align 16) hFresh0 hInv0 hSame1 hGroups'
    hCgSc hCgSlots hCgEff hCgMap hLiveMap' hMetaLe' ?_ ?_ ?_
  · by_cases hBig : Guaranteed63Threshold ≤ req
    · simp only [FineBudget.stepReallocAdd, hBig, ↓reduceIte, FineBudget.stepAligned]
      exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
    · simp only [FineBudget.stepReallocAdd, hBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
  · intro hBig
    simp [FineBudget.stepReallocAdd, FineBudget.stepAligned, hBig]
  · intro hBig
    dsimp only [FineBudget.stepReallocAdd]
    simp only [hBig, ↓reduceIte]
    exact ⟨trivial, trivial, Nat.add_le_add_left (Nat.le_max_right _ _) _,
      Nat.add_le_add_left (Nat.le_max_right _ _) _⟩

end LibsignalBinary.Heap.Fine
