/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocMremapHelpers
import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Large-Slot `mremap` No-Orphan and Group Invariant Helpers

Proves `reallocMremap_noOrphan` for the `sc = 63` `mremap` resize and in-place skip paths of
`__libc_realloc`, defines the updated group and heap state `mkReallocMremapGroup` and
`mkReallocMremapSt`, and proves `reallocMremap_groupWf_self`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Root-Region Replacement and `MallocngNoOrphanMappings` -/

theorem extractLsb_list_eq_unpack32 (u : BitVec 32) :
    [u.extractLsb' (8 * 0) 8, u.extractLsb' (8 * 1) 8,
     u.extractLsb' (8 * 2) 8, u.extractLsb' (8 * 3) 8] = unpack32 u := by
  simp only [unpack32]

theorem slotWf_lift_other {st1 st2 : MallocngSt} {g : GroupDesc} {idx : Nat} {s : SlotState}
    (hSubG : ∀ cg ∈ st1.groups, cg.parentMeta ≠ none → cg ∈ st2.groups)
    (hEq : ∀ a : BitVec 64, g.mem.toNat ≤ a.toNat → a.toNat < (g.slotEnd idx).toNat →
      st2.byteVal a = st1.byteVal a)
    (hBounds : g.storage.toNat = g.mem.toNat + 16 ∧
      (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride ∧
      (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride ∧
      16 ≤ g.stride ∧ (g.slotEnd idx).toNat ≤ 2 ^ 48)
    (hsw : SlotWf st1 g idx s)
    (hOv : ∀ u r e, s = .liveUser u r e → st2.liveMap.ov u = st1.liveMap.ov u := by intros; rfl) :
    SlotWf st2 g idx s := by
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hSuccMul : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hRead : ∀ (p : BitVec 64) (k : Nat), g.mem.toNat ≤ p.toNat →
      p.toNat + k ≤ (g.slotEnd idx).toNat →
      readBytesFromMap st2.byteVal p k = readBytesFromMap st1.byteVal p k := fun p k h1 h2 =>
    readBytesFromMap_congr_pred
      (W := fun a => ¬ (g.mem.toNat ≤ a.toNat ∧ a.toNat < (g.slotEnd idx).toNat)) (by omega)
      (fun a ha hN => by
        have haN := (inRegion_iff_toNat (base := p) (n := k) (by omega) a).mp ha
        exact hN ⟨by omega, by omega⟩)
      (fun a hNN => let ⟨hL, hR⟩ := Classical.not_not.mp hNN; hEq a hL hR)
  have hSm4Nat : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 :=
    bv64_sub_toNat (a := g.slotStart idx) (n := 4) (by omega)
  refine ⟨(hEq _ (by omega) (by omega)).trans hsw.1, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1, ?_⟩
  have hRest := hsw.2.2.2.2
  cases s with
  | freeAvail | freeInactive | claimed => trivial
  | liveNested cm =>
    obtain ⟨hsc, cg, hcg, hcm, hpar, hstLe, hal, hendLe, hcap, hoff, hb4, hb3, hb2⟩ := hRest
    have hcgm4 : (cg.mem - 4#64).toNat = cg.mem.toNat - 4 := bv64_sub_toNat (a := cg.mem) (n := 4) (by omega)
    have hcgm3 : (cg.mem - 3#64).toNat = cg.mem.toNat - 3 := bv64_sub_toNat (a := cg.mem) (n := 3) (by omega)
    have hcgm2 : (cg.mem - 2#64).toNat = cg.mem.toNat - 2 := bv64_sub_toNat (a := cg.mem) (n := 2) (by omega)
    exact ⟨hsc, cg, hSubG cg hcg (by simp [hpar]), hcm, hpar, hstLe, hal, hendLe, hcap, hoff,
      (hEq _ (by omega) (by omega)).trans hb4, (hEq _ (by omega) (by omega)).trans hb3,
      (hRead (cg.mem - 2#64) 2 (by omega) (by omega)).trans hb2⟩
  | liveUser userPtr reqSize effCost =>
    obtain ⟨hbwf, hstLe, hendLe, h1, h2, h3, h4, h5, hb3, hOffCase, hRes1, hRes5⟩ := hRest
    have hum3 : (userPtr - 3#64).toNat = userPtr.toNat - 3 := bv64_sub_toNat (a := userPtr) (n := 3) (by omega)
    have hum4 : (userPtr - 4#64).toNat = userPtr.toNat - 4 := bv64_sub_toNat (a := userPtr) (n := 4) (by omega)
    have hum2 : (userPtr - 2#64).toNat = userPtr.toNat - 2 := bv64_sub_toNat (a := userPtr) (n := 2) (by omega)
    refine ⟨hbwf, hstLe, hendLe, h1, by rw [hOv _ _ _ rfl]; exact h2, h3, h4, h5,
      (hEq _ (by omega) (by omega)).trans hb3, ?_, ?_, ?_⟩
    · by_cases hOffLt : (userPtr.toNat - g.storage.toNat) / 16 ≤ 0xffff <;>
        simp only [hOffLt, ↓reduceIte] at hOffCase ⊢
      · exact ⟨(hEq _ (by omega) (by omega)).trans hOffCase.1,
          (hRead (userPtr - 2#64) 2 (by omega) (by omega)).trans hOffCase.2⟩
      · obtain ⟨hsc63, hidx0, hoff32, hb4, hb2, hb8⟩ := hOffCase
        have hum8 : (userPtr - 8#64).toNat = userPtr.toNat - 8 := bv64_sub_toNat (a := userPtr) (n := 8) (by omega)
        exact ⟨hsc63, hidx0, hoff32, (hEq _ (by omega) (by omega)).trans hb4,
          (hRead (userPtr - 2#64) 2 (by omega) (by omega)).trans hb2,
          (hRead (userPtr - 8#64) 4 (by omega) (by omega)).trans hb8⟩
    · intro hr1
      have huReq : (userPtr + BitVec.ofNat 64 reqSize).toNat = userPtr.toNat + reqSize :=
        bv64_add_toNat (a := userPtr) (n := reqSize) (by omega)
      exact (hEq _ (by omega) (by omega)).trans (hRes1 hr1)
    · intro hr5
      have hse5 : (g.slotEnd idx - 5#64).toNat = (g.slotEnd idx).toNat - 5 :=
        bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega)
      have hse4 : (g.slotEnd idx - 4#64).toNat = (g.slotEnd idx).toNat - 4 :=
        bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
      exact ⟨(hEq _ (by omega) (by omega)).trans (hRes5 hr5).1,
        (hRead (g.slotEnd idx - 4#64) 4 (by omega) (by omega)).trans (hRes5 hr5).2⟩

theorem pairwiseDisjoint_replaceGroup_root {g g' : GroupDesc}
    (hMpG' : 0 < g'.maplen) :
    ∀ (gs : List GroupDesc),
      (gs.map (·.metaPtr)).Nodup →
      PairwiseDisjointRegions
        ((gs.filter fun x => decide (0 < x.maplen)).map fun x => (x.mem, x.maplen * 4096)) →
      (∀ x ∈ gs, 0 < x.maplen → x.metaPtr ≠ g.metaPtr →
        DisjointRegions x.mem (x.maplen * 4096) g'.mem (g'.maplen * 4096)) →
      PairwiseDisjointRegions
        (((replaceGroup gs g.metaPtr g').filter fun x => decide (0 < x.maplen)).map
          fun x => (x.mem, x.maplen * 4096)) := by
  intro gs
  induction gs with
  | nil => intro _ _ _; trivial
  | cons hd tl ih =>
    intro hnd hP hDisj
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hEq : hd.metaPtr = g.metaPtr
    · have hIdTl : replaceGroup tl g.metaPtr g' = tl :=
        replaceGroup_id_of_ne tl g.metaPtr g'
          (fun x hx hE => hnd.1 (hEq.trans hE.symm ▸ List.mem_map_of_mem hx))
      have hCons : replaceGroup (hd :: tl) g.metaPtr g' = g' :: tl := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: replaceGroup tl g.metaPtr g' = g' :: tl
        rw [beq_iff_eq.mpr hEq, hIdTl]; rfl
      rw [hCons]
      simp only [List.filter_cons, decide_eq_true hMpG', ↓reduceIte, List.map_cons]
      have hPTl : PairwiseDisjointRegions
          ((tl.filter fun x => decide (0 < x.maplen)).map fun x => (x.mem, x.maplen * 4096)) := by
        by_cases hMpHd : 0 < hd.maplen
        · simp only [List.filter_cons, decide_eq_true hMpHd, ↓reduceIte, List.map_cons,
            PairwiseDisjointRegions] at hP
          exact hP.2
        · simp only [List.filter_cons, decide_eq_false hMpHd, Bool.false_eq_true, ↓reduceIte] at hP
          exact hP
      refine ⟨fun r hr => ?_, hPTl⟩
      obtain ⟨x, hxF, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hxTl, hxMpB⟩ := List.mem_filter.mp hxF
      have hxNe : x.metaPtr ≠ g.metaPtr :=
        fun hE => hnd.1 (hEq.trans hE.symm ▸ List.mem_map_of_mem hxTl)
      exact (hDisj x (List.mem_cons_of_mem hd hxTl) (of_decide_eq_true hxMpB) hxNe).symm
    · have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
        rw [beq_false_of_ne hEq]; rfl
      rw [hCons]
      by_cases hMpHd : 0 < hd.maplen
      · simp only [List.filter_cons, decide_eq_true hMpHd, ↓reduceIte, List.map_cons,
          PairwiseDisjointRegions] at hP ⊢
        refine ⟨fun r hr => ?_,
          ih hnd.2 hP.2 (fun x hx => hDisj x (List.mem_cons_of_mem hd hx))⟩
        obtain ⟨y, hyF, rfl⟩ := List.mem_map.mp hr
        obtain ⟨hyRep, hyMpB⟩ := List.mem_filter.mp hyF
        have hyCases : y = g' ∨ y ∈ tl := by
          obtain ⟨a, haTl, haEq⟩ := List.mem_map.mp hyRep
          cases hA : (a.metaPtr == g.metaPtr)
          · rw [hA] at haEq
            simp only [Bool.false_eq_true, ↓reduceIte] at haEq
            exact Or.inr (haEq ▸ haTl)
          · rw [hA] at haEq
            simp only [↓reduceIte] at haEq
            exact Or.inl haEq.symm
        rcases hyCases with rfl | hyTl
        · exact hDisj hd List.mem_cons_self hMpHd hEq
        · exact hP.1 (y.mem, y.maplen * 4096)
            (List.mem_map_of_mem (List.mem_filter.mpr ⟨hyTl, hyMpB⟩))
      · simp only [List.filter_cons, decide_eq_false hMpHd, Bool.false_eq_true, ↓reduceIte] at hP ⊢
        exact ih hnd.2 hP (fun x hx => hDisj x (List.mem_cons_of_mem hd hx))

theorem replaceGroup_filter_pos_length {g g' : GroupDesc}
    (hMpG : 0 < g.maplen) (hMpG' : 0 < g'.maplen) :
    ∀ (gs : List GroupDesc),
      (gs.map (·.metaPtr)).Nodup →
      g ∈ gs →
      ((replaceGroup gs g.metaPtr g').filter fun x => decide (0 < x.maplen)).length =
        (gs.filter fun x => decide (0 < x.maplen)).length := by
  intro gs
  induction gs with
  | nil => intro _ hg; cases hg
  | cons hd tl ih =>
    intro hnd hg
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hg with rfl | hgTl
    · have hIdTl : replaceGroup tl g.metaPtr g' = tl :=
        replaceGroup_id_of_ne tl g.metaPtr g' (fun y hy hE => hnd.1 (hE ▸ List.mem_map_of_mem hy))
      have hCons : replaceGroup (g :: tl) g.metaPtr g' = g' :: tl := by
        show (if (g.metaPtr == g.metaPtr) = true then g' else g) :: replaceGroup tl g.metaPtr g' = g' :: tl
        rw [BEq.rfl, hIdTl]; rfl
      rw [hCons]
      simp [hMpG, hMpG']
    · have hNe : hd.metaPtr ≠ g.metaPtr :=
        fun hE => hnd.1 (hE ▸ List.mem_map_of_mem hgTl)
      have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
        rw [beq_false_of_ne hNe]; rfl
      rw [hCons]
      by_cases hMpHd : 0 < hd.maplen <;>
        simp [hMpHd, ih hnd.2 hgTl]

/-- `MallocngNoOrphanMappings` across Stage 3 (`needed = oldLen` skip or `mremap` success). -/
theorem reallocMremap_noOrphan {st st' : MallocngSt} {g g' : GroupDesc}
    {ivs0 : List (BitVec 64 × Nat)} {newBase : BitVec 64} {needed : Nat}
    {m0 mf : Memory}
    (hIvs0 : ivs0 = dynamicRootRegions st)
    (hNdMeta : (st.groups.map (·.metaPtr)).Nodup)
    (hg : g ∈ st.groups)
    (hMpG : 0 < g.maplen)
    (hMpG' : 0 < g'.maplen)
    (hMetaEq : g'.metaPtr = g.metaPtr)
    (hMemG' : g'.mem = newBase)
    (hLenG' : g'.maplen * 4096 = needed)
    (hSt'Ivs : dynamicRootRegions st' =
      st.metaAreas.map (fun ma => (ma.base, 4096)) ++
      st.guardPages.map (fun gp => (gp, 4096)) ++
      st.availMetaPages.map (fun ap => (ap, 4096)) ++
      ((replaceGroup st.groups g.metaPtr g').filter fun x => decide (0 < x.maplen)).map
        (fun x => (x.mem, x.maplen * 4096)))
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → m0.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ mf.perm = m0.perm) ∨
      (∃ m1 : Memory, m1.perm = m0.perm ∧
        mf.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm)) :
    MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') m0 mf := by
  obtain ⟨hg'Mem, _, hGsKeep, _, _, _⟩ :=
    replaceGroup_props st.groups g g' hg hNdMeta hMetaEq
  have hNewInIvs' : (newBase, needed) ∈ dynamicRootRegions st' := by
    rw [hSt'Ivs, ← hMemG', ← hLenG']
    exact List.mem_append_right _
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg'Mem, decide_eq_true hMpG'⟩))
  have hOtherInIvs' : ∀ iv ∈ dynamicRootRegions st,
      ∀ a, (a - iv.1).toNat < iv.2 → ¬ InRegion g.mem (g.maplen * 4096) a →
        MallocngInIntervals (dynamicRootRegions st') a := by
    intro iv hiv a haIv haNotG
    unfold dynamicRootRegions at hiv
    rcases List.mem_append.mp hiv with h123 | hRg
    · refine ⟨iv, ?_, haIv⟩
      rw [hSt'Ivs]
      exact List.mem_append_left _ h123
    · obtain ⟨x, hxF, rfl⟩ := List.mem_map.mp hRg
      obtain ⟨hx, hxMpB⟩ := List.mem_filter.mp hxF
      by_cases hEx : x.metaPtr = g.metaPtr
      · have rflX := mem_groups_eq_of_metaPtr hNdMeta hx hg hEx
        subst rflX
        exact False.elim (haNotG haIv)
      · refine ⟨(x.mem, x.maplen * 4096), ?_, haIv⟩
        rw [hSt'Ivs]
        exact List.mem_append_right _
          (List.mem_map_of_mem (List.mem_filter.mpr ⟨hGsKeep x hx hEx, hxMpB⟩))
  intro a hmf hOr
  rcases hPermRel with ⟨rfl, hNeedEq, hPermEq⟩ | ⟨m1, hm1Eq, hmfEq⟩
  · rw [hPermEq] at hmf
    rcases hOr with hm0F | ⟨iv, hiv, haIv⟩
    · rw [hmf] at hm0F; cases hm0F
    · rw [hIvs0] at hiv
      by_cases haG : InRegion g.mem (g.maplen * 4096) a
      · exact ⟨(g.mem, needed), hNewInIvs', hNeedEq.symm ▸ haG⟩
      · exact hOtherInIvs' iv hiv a haIv haG
  · by_cases haNew : InRegion newBase needed a
    · exact ⟨(newBase, needed), hNewInIvs', haNew⟩
    · by_cases haOld : InRegion g.mem (g.maplen * 4096) a
      · exfalso
        have hf : (m1.perm a).frozen = false := by rw [hm1Eq, hOldRw a haOld]; rfl
        have hRemapNone : (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm a = none := by
          rw [Memory.perm_remapRw_raw, hf]
          change (if false = true then _ else if InRegion newBase needed a then _
            else if InRegion g.mem (g.maplen * 4096) a then none else _) = none
          simp only [Bool.false_eq_true, ↓reduceIte, haNew, haOld]
        rw [hmfEq, hRemapNone] at hmf
        cases hmf
      · have hRemapSame : (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm a = m0.perm a := by
          rw [Memory.perm_remapRw_raw]
          change (if (m1.perm a).frozen = true then m1.perm a else if InRegion newBase needed a then _
            else if InRegion g.mem (g.maplen * 4096) a then _ else m1.perm a) = m0.perm a
          simp only [haNew, haOld, ↓reduceIte, ite_self, hm1Eq]
        rw [hmfEq, hRemapSame] at hmf
        rcases hOr with hm0F | ⟨iv, hiv, haIv⟩
        · rw [hmf] at hm0F; cases hm0F
        · rw [hIvs0] at hiv
          exact hOtherInIvs' iv hiv a haIv haOld

/-! ## Group Invariant Preservation -/

/-- State construction for Stage 3 `sc = 63` `mremap` / in-place group update. -/
def mkReallocMremapGroup (g : GroupDesc) (newBase newP : BitVec 64)
    (needed newSz newEff : Nat) : GroupDesc :=
  { g with
    mem := newBase
    maplen := needed / 4096
    slots := [.liveUser newP newSz newEff] }

def mkReallocMremapSt (st : MallocngSt) (g : GroupDesc)
    (p newBase newP : BitVec 64) (needed newSz newEff : Nat)
    (bsFinal : List (BitVec 8)) : MallocngSt :=
  let g' := mkReallocMremapGroup g newBase newP needed newSz newEff
  let domRest := st.masterDom.filter (fun a => !decide (InRegion g.mem (g.maplen * 4096) a))
  let dom' := domRest ++ rangeAddrs newBase needed
  let val' := writeBytesToMap (writeBytesToMap st.byteVal g.metaPtr g'.metaBytes) newBase bsFinal
  let liveMap' := (st.liveMap.erase p).insert newP newSz (st.liveMap.ov p)
  { st with
    groups := replaceGroup st.groups g.metaPtr g'
    masterDom := dom'
    byteVal := val'
    liveMap := liveMap' }

theorem nodup_map_mem_replaceGroup {g g' : GroupDesc} :
    ∀ (gs : List GroupDesc),
      (gs.map (·.metaPtr)).Nodup →
      (gs.map (·.mem)).Nodup →
      (∀ x ∈ gs, x.metaPtr ≠ g.metaPtr → x.mem ≠ g'.mem) →
      ((replaceGroup gs g.metaPtr g').map (·.mem)).Nodup := by
  intro gs
  induction gs with
  | nil => intro _ _ _; exact List.nodup_nil
  | cons hd tl ih =>
    intro hndM hndMem hNeMem
    simp only [List.map_cons, List.nodup_cons] at hndM hndMem
    by_cases hEq : hd.metaPtr = g.metaPtr
    · have hIdTl : replaceGroup tl g.metaPtr g' = tl :=
        replaceGroup_id_of_ne tl g.metaPtr g'
          (fun x hx hE => hndM.1 (hEq.trans hE.symm ▸ List.mem_map_of_mem hx))
      have hCons : replaceGroup (hd :: tl) g.metaPtr g' = g' :: tl := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: replaceGroup tl g.metaPtr g' = g' :: tl
        rw [beq_iff_eq.mpr hEq, hIdTl]; rfl
      rw [hCons, List.map_cons, List.nodup_cons]
      refine ⟨fun hIn => ?_, hndMem.2⟩
      obtain ⟨x, hxTl, hxEq⟩ := List.mem_map.mp hIn
      have hxNe : x.metaPtr ≠ g.metaPtr :=
        fun hE => hndM.1 (hEq.trans hE.symm ▸ List.mem_map_of_mem hxTl)
      exact hNeMem x (List.mem_cons_of_mem hd hxTl) hxNe hxEq
    · have hCons : replaceGroup (hd :: tl) g.metaPtr g' = hd :: replaceGroup tl g.metaPtr g' := by
        show (if (hd.metaPtr == g.metaPtr) = true then g' else hd) :: _ = _
        rw [beq_false_of_ne hEq]; rfl
      rw [hCons, List.map_cons, List.nodup_cons]
      refine ⟨fun hIn => ?_, ih hndM.2 hndMem.2 (fun x hx => hNeMem x (List.mem_cons_of_mem hd hx))⟩
      obtain ⟨y, hyRep, hyEq⟩ := List.mem_map.mp hIn
      obtain ⟨a, haTl, haEq⟩ := List.mem_map.mp hyRep
      cases hA : (a.metaPtr == g.metaPtr)
      · rw [hA] at haEq
        simp only [Bool.false_eq_true, ↓reduceIte] at haEq
        subst haEq; exact hndMem.1 (hyEq ▸ List.mem_map_of_mem haTl)
      · rw [hA] at haEq
        simp only [↓reduceIte] at haEq
        subst haEq; exact hNeMem hd List.mem_cons_self hEq hyEq.symm

theorem reallocMremap_groupWf_self {st st' : MallocngSt} {g : GroupDesc}
    {p newBase newP : BitVec 64} {oldSz oldEff needed newSz newEff : Nat}
    (hgw : GroupWf st g)
    (hIdx0 : 0 < g.slots.length) (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) (hNewBWf : MallocngBlockWf newP newSz)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNeedLo : 4096 ≤ needed) (hNeedDvd : 4096 ∣ needed)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hNewPNat : newP.toNat = newBase.toNat + 16 + (p.toNat - (g.slotStart 0).toNat))
    (hNewSlotFit : 16 + (p.toNat - (g.slotStart 0).toNat) + newSz + 4 ≤ needed)
    (hNeedResHi : (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) < 2 ^ 31)
    (hNewEffEq : newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost)
    (hNewEffBound : needed ≤ newEff + 8195)
    (hNewOv : st'.liveMap.ov newP = st.liveMap.ov p)
    (hEndZero : st'.byteVal (newBase + BitVec.ofNat 64 (needed - 4)) = 0#8)
    (hMetaSelf : readBytesFromMap st'.byteVal g.metaPtr 40 =
      (mkReallocMremapGroup g newBase newP needed newSz newEff).metaBytes)
    (hPreByte : ∀ i, i < 16 + (p.toNat - (g.slotStart 0).toNat) →
      i ≠ 13 + (p.toNat - (g.slotStart 0).toNat) →
      st'.byteVal (newBase + BitVec.ofNat 64 i) = st.byteVal (g.mem + BitVec.ofNat 64 i))
    (hHdrVal : st'.byteVal (newP - 3#64) =
      BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
    (hRes1Val : 1 ≤ (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) →
      st'.byteVal (newP + BitVec.ofNat 64 newSz) = 0#8)
    (hRes5Val : 5 ≤ (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) →
      st'.byteVal (newBase + BitVec.ofNat 64 ((needed - 4) - 5)) = 0#8 ∧
      readBytesFromMap st'.byteVal (newBase + BitVec.ofNat 64 ((needed - 4) - 4)) 4 =
        unpack32 (BitVec.ofNat 32 ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)))) :
    GroupWf st' (mkReallocMremapGroup g newBase newP needed newSz newEff) := by
  have ⟨hLast0, hMpPos, hPrev0, hNext0⟩ := hgw.2.2.2.1 hSc63
  have hLastLe31 := hgw.2.1
  have hParentNone : g.parentMeta = none := hgw.2.2.2.2.2.2.2.2.2.2.1.mp hMpPos
  have hNest0 : g.nestedCap = 0 := (hgw.2.2.2.2.2.2.2.2.2.2.2.1 hMpPos).2.1
  have hMask1 := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMask2 := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hActLe := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMem8Old := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAct8Old := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsw0 := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx0
  have hOldStor : g.storage.toNat = g.mem.toNat + 16 := (group_slot_bounds hgw hIdx0).2.1
  have hOldSt0Simpl : (g.slotStart 0).toNat = g.mem.toNat + 16 := by
    have h := (group_slot_bounds hgw hIdx0).2.2.1; simp at h; exact h
  have hOldSub4Simpl : (g.slotStart 0 - 4#64).toNat = g.mem.toNat + 12 := by
    have h := (group_slot_bounds hgw hIdx0).2.2.2.1; simp at h; exact h
  have hOld48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := (group_slot_bounds hgw hIdx0).2.2.2.2.2.2.1
  clear hgw
  rw [hSlot0] at hsw0
  obtain ⟨hOldSt4, hAv0, hFr0, d1, d2, hLoP, hOldFit, hMaxLeOld, ⟨hOffLeOld, hOverLeOld, hOvLeOld⟩,
    d3, d4, d5, d6, hOldOffHdr, d7, d8⟩ := hsw0
  clear d1 d2 d3 d4 d5 d6 d7 d8 hSlot0 hIdx0
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMapMul : (needed / 4096) * 4096 = needed := Nat.div_mul_cancel hNeedDvd
  have hNewMpPos : 0 < needed / 4096 := by
    rcases hNeedDvd with ⟨k, rfl⟩; rw [Nat.mul_div_cancel_left k (by decide)]; omega
  have hNb16 : (newBase + 16#64).toNat = newBase.toNat + 16 := bv64_add_toNat (by omega)
  generalize hg'Eq : mkReallocMremapGroup g newBase newP needed newSz newEff = g' at hMetaSelf ⊢
  have hg'Fields : g'.metaPtr = g.metaPtr ∧ g'.prev = g.prev ∧ g'.next = g.next ∧
      g'.mem = newBase ∧ g'.availMask = g.availMask ∧ g'.freedMask = g.freedMask ∧
      g'.lastIdx = 0 ∧ g'.sc = 63 ∧ g'.maplen = needed / 4096 ∧
      g'.activeByte = g.activeByte ∧ g'.parentMeta = none ∧ g'.nestedCap = 0 ∧
      g'.slots = [.liveUser newP newSz newEff] := by
    subst hg'Eq
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hLast0, hSc63, rfl, rfl, hParentNone, hNest0, rfl⟩
  clear hg'Eq
  obtain ⟨hGMeta, hGPrev, hGNext, hGMem, hGAv, hGFr, hGLast, hGSc, hGMap, hGActB,
    hGPar, hGNest, hGSlots⟩ := hg'Fields
  have hCnt' : g'.cnt = 1 := by unfold GroupDesc.cnt; rw [hGLast]
  have hActEq : g'.activeIdx = g.activeIdx := by unfold GroupDesc.activeIdx; rw [hGActB]
  have hTot' : g'.totalBytes = needed := by
    unfold GroupDesc.totalBytes; rw [hGMap]; simp [hNewMpPos, hMapMul]
  have hStr' : g'.stride = needed - 16 := by
    unfold GroupDesc.stride; rw [hGLast, hGMap]; simp [hNewMpPos, hMapMul]
  have hStor' : g'.storage = newBase + 16#64 := by unfold GroupDesc.storage; rw [hGMem]
  have hSt0' : g'.slotStart 0 = newBase + 16#64 := by
    unfold GroupDesc.slotStart; rw [hStor']; simp
  have hEn0' : g'.slotEnd 0 = newBase + BitVec.ofNat 64 (needed - 4) := by
    unfold GroupDesc.slotEnd; rw [hSt0', hStr']
    apply BitVec.eq_of_toNat_eq
    rw [bv64_add_toNat (by rw [hNb16]; omega), hNb16, bv64_add_toNat (by omega)]; omega
  have hGMapPos : 0 < g'.maplen := by rw [hGMap]; exact hNewMpPos
  have hGMapMul : g'.maplen * 4096 = needed := by rw [hGMap, hMapMul]
  have hNbEnd : (newBase + BitVec.ofNat 64 (needed - 4)).toNat = newBase.toNat + (needed - 4) :=
    bv64_add_toNat (by omega)
  clear hGMap hMapMul hNewMpPos
  have hSm4Old : g.slotStart 0 - 4#64 = g.mem + BitVec.ofNat 64 12 := by
    apply BitVec.eq_of_toNat_eq
    rw [hOldSub4Simpl]; clear hOldSub4Simpl hOldSt0Simpl hOldStor hLoP hOldFit hOffLeOld hOldOffHdr
    rw [bv64_add_toNat (by omega)]
  clear hOldSub4Simpl
  generalize hExtraEq : p.toNat - (g.slotStart 0).toNat = extra at hOffLeOld hNewPNat hNewSlotFit hNeedResHi hPreByte hHdrVal hRes1Val hRes5Val
  rw [hOldSt0Simpl] at hExtraEq hLoP
  clear hOldSt0Simpl hOldFit
  have hPNat : p.toNat = g.mem.toNat + 16 + extra := by
    clear hOldStor hOldOffHdr; omega
  have hOldUnits : (p.toNat - g.storage.toNat) / 16 = extra / 16 :=
    congrArg (· / 16) (by rw [hOldStor]; clear hOldStor hOldOffHdr; omega)
  rw [hOldUnits] at hOldOffHdr
  clear hExtraEq hOldStor hLoP hOldUnits hOld48
  refine ⟨Or.inr hGSc, by rw [hGLast]; decide, by rw [hGSlots, hCnt']; rfl,
    fun _ => ⟨hGLast, hGMapPos, hGPrev.trans hPrev0, hGNext.trans hNext0⟩,
    by clear hOldOffHdr; rw [hGMem]; exact hNewBaseGe,
    by clear hOldOffHdr; rw [hGMem]; omega,
    by rw [hGMem, hTot']; exact hNewBaseFit,
    by clear hOldOffHdr; rw [hCnt', hStr', hTot']; omega,
    fun _ => by clear hOldOffHdr; rw [hCnt', hStr', hTot']; omega,
    by rw [hGLast, hEn0']; exact hEndZero,
    ⟨fun _ => hGPar, fun _ => hGMapPos⟩,
    fun _ => ⟨by rw [hGMem]; exact hNewBaseAl, hGNest,
      fun h => by clear hOldOffHdr; rw [hGSc] at h; omega,
      fun h => by clear hOldOffHdr; rw [hGSc] at h; omega⟩,
    fun h => by clear hOldOffHdr; omega,
    by rw [hGAv, hGFr]; exact hMask1,
    by rw [hGAv, hGFr, hCnt']; rw [show g.cnt = 1 by clear hOldOffHdr; unfold GroupDesc.cnt; omega] at hMask2; exact hMask2,
    by rw [hActEq, hGLast]; rw [hLast0] at hActLe; exact hActLe,
    by rw [hGMeta]; exact hMetaSelf, ?_, ?_, ?_⟩
  · rw [hGMem, hGMeta, ← hMem8Old]
    apply List.ext_getElem (by simp [readBytesFromMap_length])
    intro i hi1 hi2
    have hi8 : i < 8 := by rwa [readBytesFromMap_length] at hi1
    rw [readBytesFromMap_getElem _ _ _ _ hi1, readBytesFromMap_getElem _ _ _ _ hi2]
    exact hPreByte i (by clear hOldOffHdr; omega) (by clear hOldOffHdr; omega)
  · rw [hGMem, hGActB]
    exact (hPreByte 8 (by clear hOldOffHdr; omega) (by clear hOldOffHdr; omega)).trans hAct8Old
  · intro j hj
    have hj0 : j = 0 := by rw [hGSlots] at hj; simp at hj; exact hj
    subst hj0
    have hSlotG' : g'.slots[0]'hj = .liveUser newP newSz newEff := by simp [hGSlots]
    rw [hSlotG']
    clear hCnt' hTot' hStr' hMask2 hActLe hLastLe31 hGMapPos
    have hSm4' : g'.slotStart 0 - 4#64 = newBase + BitVec.ofNat 64 12 := by
      rw [hSt0']; apply BitVec.eq_of_toNat_eq
      clear hOldOffHdr
      rw [bv64_sub_toNat (by rw [hNb16]; omega), hNb16, bv64_add_toNat (by omega)]; omega
    have hResEq : (g'.slotEnd 0).toNat - (newP.toNat + newSz) =
        (needed - 4) - (16 + extra + newSz) := by
      clear hOldOffHdr; rw [hEn0', hNbEnd, hNewPNat]; omega
    have hUnitsEq : (newP.toNat - g'.storage.toNat) / 16 = extra / 16 :=
      congrArg (· / 16) (by clear hOldOffHdr; rw [hStor', hNb16, hNewPNat]; omega)
    unfold SlotWf
    refine ⟨by rw [hSm4', hPreByte 12 (by clear hOldOffHdr; omega) (by clear hOldOffHdr; omega), ← hSm4Old]; exact hOldSt4,
      ⟨(fun h => by rw [hGAv] at h; cases hAv0.mp h), (fun h => by cases h)⟩,
      ⟨(fun h => by rw [hGFr] at h; cases hFr0.mp h), (fun h => by cases h)⟩,
      fun h => absurd h (Nat.not_lt_zero _),
      hNewBWf,
      by clear hOldOffHdr; rw [hSt0', hNb16, hNewPNat]; omega,
      by clear hOldOffHdr; rw [hEn0', hNbEnd, hNewPNat]; omega,
      by clear hOldOffHdr; rw [hNewEffEq]; omega,
      ⟨by clear hOldOffHdr; rw [hSt0', hNb16, hNewPNat, hNewEffEq]; omega,
        by rw [hNewEffEq, Nat.add_sub_cancel]; exact hOverLeOld,
        by rw [hNewEffEq, Nat.add_sub_cancel, hNewOv]; exact hOvLeOld⟩,
      by rw [hResEq]; exact hNeedResHi,
      ⟨fun h => by clear hOldOffHdr; rw [hGSc] at h; omega,
        fun h => by clear hOldOffHdr; rw [hGSc] at h; omega⟩,
      fun _ => by rw [hGMapMul]; exact hNewEffBound,
      by rw [hResEq, Nat.or_zero]; exact hHdrVal, ?_,
      fun h1 => hRes1Val (by rwa [← hResEq]),
      fun h5 => ?_⟩
    · rw [hUnitsEq]
      have hSub4New : newP - 4#64 = newBase + BitVec.ofNat 64 (12 + extra) := by
        clear hOldOffHdr; apply BitVec.eq_of_toNat_eq
        rw [bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
      have hSub4Old : p - 4#64 = g.mem + BitVec.ofNat 64 (12 + extra) := by
        clear hOldOffHdr; apply BitVec.eq_of_toNat_eq
        rw [bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
      have hRead2 : readBytesFromMap st'.byteVal (newP - 2#64) 2 =
          readBytesFromMap st.byteVal (p - 2#64) 2 := by
        clear hOldOffHdr
        apply List.ext_getElem (by simp [readBytesFromMap_length])
        intro k hk1 hk2
        have hkLt : k < 2 := by rwa [readBytesFromMap_length] at hk1
        rw [readBytesFromMap_getElem _ _ _ _ hk1, readBytesFromMap_getElem _ _ _ _ hk2]
        have hAN : (newP - 2#64) + BitVec.ofNat 64 k =
            newBase + BitVec.ofNat 64 (14 + extra + k) := by
          apply BitVec.eq_of_toNat_eq
          rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
            bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
        have hAO : (p - 2#64) + BitVec.ofNat 64 k =
            g.mem + BitVec.ofNat 64 (14 + extra + k) := by
          apply BitVec.eq_of_toNat_eq
          rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
            bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
        rw [hAN, hAO]; exact hPreByte _ (by omega) (by omega)
      by_cases hU16 : extra / 16 ≤ 0xffff
      · simp only [hU16, ↓reduceIte] at hOldOffHdr ⊢
        obtain ⟨hB4, hB2⟩ := hOldOffHdr
        exact ⟨by rw [hSub4New, hPreByte _ (by omega) (by omega), ← hSub4Old]; exact hB4,
          hRead2.trans hB2⟩
      · simp only [hU16, ↓reduceIte] at hOldOffHdr ⊢
        obtain ⟨_, _, hOff32, hB4, hB2, hB8⟩ := hOldOffHdr
        have hGe16 : 16 ≤ extra := by omega
        have hRead4 : readBytesFromMap st'.byteVal (newP - 8#64) 4 =
            readBytesFromMap st.byteVal (p - 8#64) 4 := by
          apply List.ext_getElem (by simp [readBytesFromMap_length])
          intro k hk1 hk2
          have hkLt : k < 4 := by rwa [readBytesFromMap_length] at hk1
          rw [readBytesFromMap_getElem _ _ _ _ hk1, readBytesFromMap_getElem _ _ _ _ hk2]
          have hAN : (newP - 8#64) + BitVec.ofNat 64 k =
              newBase + BitVec.ofNat 64 (8 + extra + k) := by
            apply BitVec.eq_of_toNat_eq
            rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
              bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
          have hAO : (p - 8#64) + BitVec.ofNat 64 k =
              g.mem + BitVec.ofNat 64 (8 + extra + k) := by
            apply BitVec.eq_of_toNat_eq
            rw [bv64_add_toNat (by rw [bv64_sub_toNat (by omega)]; omega),
              bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
          rw [hAN, hAO]; exact hPreByte _ (by omega) (by omega)
        exact ⟨hGSc, trivial, hOff32,
          by rw [hSub4New, hPreByte _ (by omega) (by omega), ← hSub4Old]; exact hB4,
          hRead2.trans hB2, hRead4.trans hB8⟩
    · clear hOldOffHdr
      obtain ⟨h5a, h5b⟩ := hRes5Val (by rwa [← hResEq])
      have hSub5 : g'.slotEnd 0 - 5#64 = newBase + BitVec.ofNat 64 ((needed - 4) - 5) := by
        rw [hEn0']; apply BitVec.eq_of_toNat_eq
        rw [bv64_sub_toNat (by rw [hNbEnd]; omega), hNbEnd, bv64_add_toNat (by omega)]; omega
      have hSub4 : g'.slotEnd 0 - 4#64 = newBase + BitVec.ofNat 64 ((needed - 4) - 4) := by
        rw [hEn0']; apply BitVec.eq_of_toNat_eq
        rw [bv64_sub_toNat (by rw [hNbEnd]; omega), hNbEnd, bv64_add_toNat (by omega)]; omega
      rw [hSub5, hSub4, hResEq]
      exact ⟨h5a, h5b⟩

end VerifiedLibraries.Mallocng.Proofs

