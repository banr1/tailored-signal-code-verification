/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers
public import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Group-Update, `try_avail`, and `enframe` Spatial Helpers

Pure `MallocngWFInflight`, `ByteMap`, large-`mmap` group absorption, bitmask, and `SlotWf` local
congruence lemmas parameterized over `MallocngAddrs`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Group-Update and Large `mmap` Absorption -/

theorem mallocngWFInflight_change_base {inflight : Nat} {b1 b2 brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (h : MallocngWFInflight inflight b1 brkStart brk liveCost peakCost st) :
    MallocngWFInflight inflight b2 brkStart brk liveCost peakCost st :=
  { base_wf := trivial
    brk_bounds := h.brk_bounds
    ctx_lens := h.ctx_lens
    initDone_wf := h.initDone_wf
    initZero_wf := h.initZero_wf
    bounces_wf := h.bounces_wf
    usage_wf := h.usage_wf
    brk_mode_wf := h.brk_mode_wf
    metaAreas_wf := h.metaAreas_wf
    guard_avail_wf := h.guard_avail_wf
    inflight_wf := h.inflight_wf
    free_bump_metas_wf := h.free_bump_metas_wf
    groups_nodup := h.groups_nodup
    groups_wf := h.groups_wf
    regions_disjoint := h.regions_disjoint
    active_wf := h.active_wf
    liveMap_wf := h.liveMap_wf
    live_le_peak := h.live_le_peak
    effCost_le_live := h.effCost_le_live
    meta_pages_bound := h.meta_pages_bound
    empty_groups_bound := h.empty_groups_bound
    masterDom_wf := h.masterDom_wf }

theorem active_head_group_of_nonzero {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hAct : sc < st.ctx.active.length) (hActL : sc < st.activeLists.length)
    (hNe0 : st.ctx.active[sc]'hAct ≠ 0#64) :
    ∃ g ∈ st.groups,
      g.metaPtr = st.ctx.active[sc]'hAct ∧
      g.sc = sc ∧
      ∃ msTl : List (BitVec 64), st.activeLists[sc]'hActL = g.metaPtr :: msTl := by
  have hAWf := hwf.active_wf sc hAct hActL
  rcases hMs : st.activeLists[sc]'hActL with _ | ⟨m0, msTl⟩
  · have hDll := hAWf.2.1
    rw [hMs] at hDll
    exact False.elim (hNe0 hDll)
  · have hm0Mem : m0 ∈ st.activeLists[sc]'hActL := by rw [hMs]; exact List.mem_cons_self
    obtain ⟨g, hg, hGm0, hGsc⟩ := hAWf.1 m0 hm0Mem
    subst hGm0
    have hFind := findGroupByMeta_of_mem hwf.groups_nodup.1 hg
    have hDll := hAWf.2.1
    rw [hMs] at hDll
    simp only [List.filterMap_cons, hFind, Option.map_some, CircularDllWf] at hDll
    exact ⟨g, hg, hDll.1.symm, hGsc, msTl, rfl⟩

namespace MallocImplH1
def replaceGroup (gs : List GroupDesc) (m : BitVec 64) (g' : GroupDesc) : List GroupDesc :=
  gs.map (fun h => if h.metaPtr == m then g' else h)

theorem replaceGroup_props (gs : List GroupDesc) (g g' : GroupDesc)
    (hg : g ∈ gs) (hNd : (gs.map (·.metaPtr)).Nodup)
    (hMeta : g'.metaPtr = g.metaPtr) (hPrev : g'.prev = g.prev) (hNext : g'.next = g.next)
    (hMem : g'.mem = g.mem) (hLast : g'.lastIdx = g.lastIdx)
    (hSc : g'.sc = g.sc) (hMap : g'.maplen = g.maplen) :
    let gs' := replaceGroup gs g.metaPtr g'
    g' ∈ gs' ∧
    (∀ x' ∈ gs', (x'.metaPtr = g.metaPtr ∧ x' = g') ∨ (x'.metaPtr ≠ g.metaPtr ∧ x' ∈ gs)) ∧
    (∀ x ∈ gs, x.metaPtr ≠ g.metaPtr → x ∈ gs') ∧
    gs'.map (·.metaPtr) = gs.map (·.metaPtr) ∧
    gs'.map (·.mem) = gs.map (·.mem) ∧
    ((gs'.filter fun x => decide (0 < x.maplen)).map fun x => (x.mem, x.maplen * 4096)) =
      ((gs.filter fun x => decide (0 < x.maplen)).map fun x => (x.mem, x.maplen * 4096)) ∧
    (∀ sc' : Nat, (gs'.filter (·.sc == sc')).map GroupDesc.cnt =
      (gs.filter (·.sc == sc')).map GroupDesc.cnt) ∧
    (∀ m : BitVec 64,
      (gs'.find? (·.metaPtr == m)).map (fun x => (x.metaPtr, x.prev, x.next)) =
      (gs.find? (·.metaPtr == m)).map (fun x => (x.metaPtr, x.prev, x.next))) ∧
    (∀ φ : GroupDesc → Nat, (gs'.map φ).sum + φ g = (gs.map φ).sum + φ g') := by
  dsimp only
  refine ⟨List.mem_map.mpr ⟨g, hg, by simp⟩, ?_,
    fun x hx hNe => List.mem_map.mpr ⟨x, hx, by simp [beq_false_of_ne hNe]⟩, ?_, ?_, ?_⟩
  · intro x' hx'; unfold replaceGroup at hx'; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    cases hEq : (x.metaPtr == g.metaPtr)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Or.inr ⟨(fun hE => by rw [hE, beq_self_eq_true] at hEq; cases hEq), hx⟩
    · simp only [↓reduceIte]; exact Or.inl ⟨hMeta, trivial⟩
  · unfold replaceGroup; rw [List.map_map]; apply List.map_congr_left; intro x _
    dsimp only [Function.comp_apply]
    cases hEq : (x.metaPtr == g.metaPtr)
    · rfl
    · simp only [↓reduceIte]; exact hMeta.trans (beq_iff_eq.mp hEq).symm
  · unfold replaceGroup; rw [List.map_map]; apply List.map_congr_left; intro x hx
    dsimp only [Function.comp_apply]
    cases hEq : (x.metaPtr == g.metaPtr)
    · rfl
    · simp only [↓reduceIte]
      exact hMem.trans (congrArg GroupDesc.mem (mem_groups_eq_of_metaPtr hNd hx hg (beq_iff_eq.mp hEq)).symm)
  · unfold replaceGroup
    induction gs with
    | nil => cases hg
    | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hNd ⊢
      rcases List.mem_cons.mp hg with rfl | hTl
      · have hTlEq : tl.map (fun h => if h.metaPtr == g.metaPtr then g' else h) = tl :=
          (List.map_congr_left (g := fun x => x) fun x hx => by
            have hNe : (x.metaPtr == g.metaPtr) = false := beq_false_of_ne (fun hE => hNd.1 (hE.symm ▸ List.mem_map_of_mem hx))
            simp only [hNe]; rfl).trans
          (let rec go (l : List GroupDesc) : l.map (fun x => x) = l :=
            match l with | [] => rfl | hd2 :: tl2 => congrArg (hd2 :: ·) (go tl2); go tl)
        simp only [beq_self_eq_true, ↓reduceIte]; rw [hTlEq]
        refine ⟨by by_cases hMp : 0 < g.maplen <;> simp [List.filter, hMap, hMp, hMem],
          fun sc' => by cases hE : (g.sc == sc') <;> simp [List.filter, hSc, hE, GroupDesc.cnt, hLast],
          fun m => by cases hM : (g.metaPtr == m) <;> simp [List.find?, hMeta, hM, hPrev, hNext],
          fun φ => by simp only [List.sum_cons]; omega⟩
      · have hNe : (hd.metaPtr == g.metaPtr) = false := beq_false_of_ne (fun hE => hNd.1 (hE ▸ List.mem_map_of_mem hTl))
        simp only [hNe, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := ih hTl hNd.2
        exact ⟨by cases hMp : decide (0 < hd.maplen) <;> simp only [List.filter, hMp, List.map] <;> rw [h1],
          fun sc' => by cases hE : (hd.sc == sc') <;> simp only [List.filter, hE, List.map] <;> rw [h2 sc'],
          fun m => by cases hM : (hd.metaPtr == m) <;> simp only [List.find?, hM]; exact h3 m,
          fun φ => by have h4φ := h4 φ; simp only [List.sum_cons] at h4φ ⊢; omega⟩
end MallocImplH1
export MallocImplH1 (replaceGroup replaceGroup_props)

theorem fresh_mmap_disjoint_A
    {m : Memory} {inflight : Nat} {γ : GhostName} {A : MallocngAddrs} {brkStart brk mb : BitVec 64}
    {liveCost peakCost len : Nat} {st : MallocngSt} {R : SepProp}
    (hMem : m ⊨
      (mb ↦ₛ List.replicate len 0#8) ∗
      memMapped mb len ∗
      MallocngCoreStInflightA inflight γ A brkStart brk liveCost peakCost st ∗
      R)
    (hMbAl : mb.toNat % 4096 = 0)
    (hLenAl : len % 4096 = 0)
    (hLenPos : 4096 ≤ len)
    (hMbBound : mb.toNat + len ≤ 2 ^ 48) :
    ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 mb len := by
  dsimp only [MallocngCoreStInflightA] at hMem
  have hwf : MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st := by
    have hCore := Satisfies.drop_left (Satisfies.drop_left hMem)
    rw [sepConj_assoc] at hCore
    exact ((satisfies_pure_sepConj _ _ m).mp hCore).1
  have hMbReg : (mb ↦ₛ List.replicate len 0#8) ⊢ memRegion mb len := by
    simpa [List.length_replicate] using pointsToBytes_entails_memRegion mb (List.replicate len 0#8)
  have hMbPermRw : ∀ a : BitVec 64, InRegion mb len a → m.perm a = some Perm.rw := fun a ha => by
    obtain ⟨Q, h1⟩ : ∃ Q, m ⊨ (mb ↦ₛ List.replicate len 0#8) ∗ Q :=
      ⟨_, Satisfies.mono (by sep_frame) hMem⟩
    exact (IsBlock.pointsToBytes mb (List.replicate len 0#8)).perm_rw h1
      (by simpa [List.length_replicate] using ha)
  intro r hr
  unfold dynamicRootRegions at hr
  rcases List.mem_append.mp hr with hr123 | hrGrp
  · rcases List.mem_append.mp hr123 with hr12 | hrAp
    · rcases List.mem_append.mp hr12 with hrMa | hrGp
      · obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hrMa
        dsimp only
        have hmaWf := hwf.metaAreas_wf.2.1 ma hma
        apply Classical.byContradiction; intro hNot
        obtain ⟨k, hkLt, hkIn⟩ := page_overlap_of_not_disjoint
          hmaWf.2.1 (by decide) hMbAl hLenAl (by decide) (by omega) (by omega) (by omega) hNot
        have hk0 : k = 0 := by omega
        subst hk0
        have haIn : InRegion mb len ma.base := by simpa using (hkIn 0 (by decide)).2
        have ⟨hKeep, hDom⟩ := metaArea_base_ownedRw hwf hma
        have hFocus : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
            ((ma.base ↦₈ st.byteVal ma.base) ∗
              ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ a ≠ ma.base) st.byteVal) :=
          SetSep_focus hwf.masterDom_wf.1 _ hDom hKeep
        rw [hFocus] at hMem
        have hMem1 := Satisfies.mono (sepConj_mono_left hMbReg) hMem
        obtain ⟨Q, hSat⟩ : ∃ Q, m ⊨ (ma.base ↦₈ st.byteVal ma.base) ∗ (memRegion mb len ∗ Q) :=
          ⟨_, Satisfies.mono (by sep_frame) hMem1⟩
        exact not_satisfies_ownsRW_ownsRW (ownsRW_pointsTo8 ma.base _)
          (ownsRW_sepConj_left (ownsRW_memRegion mb len _ haIn)) hSat
      · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hrGp
        dsimp only
        have hgpWf := hwf.guard_avail_wf.2.1 gp hgp
        apply Classical.byContradiction; intro hNot
        obtain ⟨k, hkLt, hkIn⟩ := page_overlap_of_not_disjoint
          hgpWf.2.1 (by decide) hMbAl hLenAl (by decide) (by omega) (by omega) (by omega) hNot
        have hk0 : k = 0 := by omega
        subst hk0
        have haIn : InRegion mb len gp := by simpa using (hkIn 0 (by decide)).2
        have hKeep : OwnedProtNoneByte st gp := Or.inl ⟨gp, hgp, by unfold InRegion; bv_omega⟩
        have hDom : gp ∈ st.masterDom := hwf.masterDom_wf.2.1 gp (Or.inr (Or.inl hKeep))
        have hFocus : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
            ((gp ↦₈ₙ st.byteVal gp) ∗
              ProtNoneByteMap st.masterDom (fun a => OwnedProtNoneByte st a ∧ a ≠ gp) st.byteVal) :=
          SetSep_focus hwf.masterDom_wf.1 _ hDom hKeep
        rw [hFocus] at hMem
        obtain ⟨Q, hSat⟩ : ∃ Q, m ⊨ (gp ↦₈ₙ st.byteVal gp) ∗ Q :=
          ⟨_, Satisfies.mono (by sep_frame) hMem⟩
        have hPn := (IsBlockProtNone.pointsTo8ProtNone gp (st.byteVal gp)).perm_protNone hSat
          (a := gp) (by unfold InRegion; bv_omega)
        rw [hMbPermRw gp haIn] at hPn; cases hPn
    · obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hrAp
      dsimp only
      have hSubKeep : ∀ a, InRegion ap 4096 a → OwnedMappedByte st a :=
        fun a ha => Or.inr (Or.inr (Or.inl ⟨ap, hap, ha⟩))
      have hSubDom : ∀ a, InRegion ap 4096 a → a ∈ st.masterDom :=
        fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (hSubKeep a ha)))
      rw [MappedSet_extract_slice hwf.masterDom_wf.1 ap (by decide) hSubDom hSubKeep] at hMem
      obtain ⟨Q, hSat⟩ : ∃ Q, m ⊨ memMapped ap 4096 ∗ (memMapped mb len ∗ Q) :=
        ⟨_, Satisfies.mono (by sep_frame) hMem⟩
      exact Satisfies.disjointRegions_of_memMapped (by decide) (by omega) hSat
  · obtain ⟨g, hgF, rfl⟩ := List.mem_map.mp hrGrp
    dsimp only
    obtain ⟨hg, hMapPosB⟩ := List.mem_filter.mp hgF
    have hMapPos : 0 < g.maplen := of_decide_eq_true hMapPosB
    have hgw := hwf.groups_wf g hg
    have hgTot : g.totalBytes = g.maplen * 4096 := by unfold GroupDesc.totalBytes; simp [hMapPos]
    have hgBound : g.maplen * 4096 ≤ 2 ^ 64 := by have hFit := hgw.2.2.2.2.2.2.1; rw [hgTot] at hFit; omega
    have hSubKeep : ∀ a, InRegion g.mem (g.maplen * 4096) a → OwnedMappedByte st a :=
      fun a ha => Or.inr (Or.inr (Or.inr ⟨g, hg, hMapPos, ha⟩))
    have hSubDom : ∀ a, InRegion g.mem (g.maplen * 4096) a → a ∈ st.masterDom :=
      fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (hSubKeep a ha)))
    rw [MappedSet_extract_slice hwf.masterDom_wf.1 g.mem hgBound hSubDom hSubKeep] at hMem
    obtain ⟨Q, hSat⟩ : ∃ Q, m ⊨ memMapped g.mem (g.maplen * 4096) ∗ (memMapped mb len ∗ Q) :=
      ⟨_, Satisfies.mono (by sep_frame) hMem⟩
    exact Satisfies.disjointRegions_of_memMapped (by omega) (by omega) hSat

theorem createLargeMmapGroup_absorb {γ : GhostName} {A : MallocngAddrs} {brkStart brk m mb : BitVec 64}
    {liveCost peakCost len : Nat} {st1 : MallocngSt}
    (hwf1 : MallocngWFInflight 1 A.base brkStart brk liveCost peakCost st1)
    (hRes : st1.reservedMetas = [m])
    (hMbNe : mb ≠ 0#64) (hMbAl : mb.toNat % 4096 = 0)
    (hLenPos : 4096 ≤ len) (hLenAl : len % 4096 = 0)
    (hMbBound : mb.toNat + len ≤ 2 ^ 48)
    (hDisjDyn : ∀ r ∈ dynamicRootRegions st1, DisjointRegions r.1 r.2 mb len) :
    let gNew := mkLargeGroup m mb len
    let st2 := mkLargeGroupSt st1 m mb len
    let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
    MallocngLiveAuth γ st1.liveMap ∗
    (A.ctx ↦ₛ st2.ctx.toBytes) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    ((A.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
    MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗
    (m ↦ₛ gNew.metaBytes) ∗
    (mb ↦ₛ groupBytes) ∗
    memMapped mb len ∗
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
    MappedSet st1.masterDom (OwnedMappedByte st1) ⊢
      MallocngCoreStInflightA 1 γ A brkStart brk liveCost peakCost st2 := by
  intro gNew st2 groupBytes
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let bDummy : BitVec 64 := BitVec.ofNat 64 (2 ^ 49)
  have hDisjDummy : DisjointRegions bDummy 0x5000 mb len := by
    have hbN : bDummy.toNat = 2 ^ 49 := by simp [bDummy]
    exact disjointRegions_of_nonwrap (by decide) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have hwf2 := mallocngWFInflight_change_base (b2 := A.base) (createLargeMmapGroup_wf
    (mallocngWFInflight_change_base (b2 := bDummy) hwf1)
    hRes hMbNe hMbAl hLenPos hLenAl hMbBound hDisjDummy hDisjDyn)
  have hMapMul : (len / 4096) * 4096 = len := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hLenAl)
  have hMapPos : 0 < len / 4096 := by omega
  have hGbLen : groupBytes.length = len := by simp [groupBytes]; omega
  let extraMeta := (rangeAddrs m 40).filter (fun a => !decide (a ∈ st1.masterDom))
  have hDomEq : st2.masterDom = st1.masterDom ++ (extraMeta ++ rangeAddrs mb len) := by
    simp [st2, mkLargeGroupSt, extraMeta, List.append_assoc]
  have hDom2Nd : st2.masterDom.Nodup := hwf2.masterDom_wf.1
  have hTailNotDom1 : ∀ a ∈ extraMeta ++ rangeAddrs mb len, a ∉ st1.masterDom := by
    intro a ha hIn1
    have hNd := hDomEq ▸ hDom2Nd
    exact (List.nodup_append.mp hNd).2.2 a hIn1 a ha rfl
  have hNot1 : ∀ a ∈ extraMeta ++ rangeAddrs mb len,
      ¬ OwnedRwByte st1 a ∧ ¬ OwnedProtNoneByte st1 a ∧ ¬ OwnedMappedByte st1 a := fun a ha =>
    ⟨fun h => hTailNotDom1 a ha (hwf1.masterDom_wf.2.1 a (Or.inl h)),
     fun h => hTailNotDom1 a ha (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inl h))),
     fun h => hTailNotDom1 a ha (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inr h)))⟩
  have hLiftRw : ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal =
      ByteMap st2.masterDom (OwnedRwByte st1) st1.byteVal := by
    unfold ByteMap; rw [hDomEq]
    exact (SetSep_append_right_empty _ (fun a ha => (hNot1 a ha).1)).symm
  have hLiftPn : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st1) st1.byteVal := by
    unfold ProtNoneByteMap; rw [hDomEq]
    exact (SetSep_append_right_empty _ (fun a ha => (hNot1 a ha).2.1)).symm
  have hLiftMp : MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st2.masterDom (OwnedMappedByte st1) := by
    unfold MappedSet; rw [hDomEq]
    exact (SetSep_append_right_empty _ (fun a ha => (hNot1 a ha).2.2)).symm
  have hmAll : m ∈ allMetaSlots st1 := (hwf1.free_bump_metas_wf.2.2.2.2.2 m).mp (by simp [hRes])
  obtain ⟨maM, hmaM, _, _, _, hmNat, hmFit, hMaM48⟩ := metaSlot_in_metaArea hwf1 hmAll
  have hmInMaM : ∀ a : BitVec 64, InRegion m 40 a → InRegion maM.base 4096 a := fun a ha => by
    have haN := (inRegion_iff_toNat (base := m) (n := 40) (by omega) a).mp ha
    exact (inRegion_iff_toNat (base := maM.base) (n := 4096) (by omega) a).mpr ⟨by omega, by omega⟩
  have hMInDomM : ∀ a, InRegion m 40 a → a ∈ st1.masterDom ++ extraMeta := fun a hm => by
    by_cases h1 : a ∈ st1.masterDom
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_filter.mpr
        ⟨(mem_rangeAddrs_iff_inRegion m (by decide) a).mpr hm, by simp [h1]⟩)
  have hMSubDom2 : ∀ a, InRegion m gNew.metaBytes.length a → a ∈ st2.masterDom := fun a hm => by
    rw [GroupDesc.metaBytes_length] at hm
    rw [hDomEq, ← List.append_assoc]; exact List.mem_append_left _ (hMInDomM a hm)
  have hMbSubDom2 : ∀ a, InRegion mb len a → a ∈ st2.masterDom := fun a hmb => by
    rw [hDomEq]; exact List.mem_append_right _ (List.mem_append_right _
      ((mem_rangeAddrs_iff_inRegion mb (by omega) a).mpr hmb))
  have hDisjMbDomM : ∀ a, InRegion mb len a → a ∉ st1.masterDom ++ extraMeta := fun a hmb hIn => by
    rcases List.mem_append.mp hIn with hDom1 | hEx
    · obtain ⟨r, hr, haR⟩ := hwf1.masterDom_wf.2.2 a hDom1
      exact not_both_inRegion_of_disjointRegions (hDisjDyn r hr) haR hmb
    · have hm := (mem_rangeAddrs_iff_inRegion m (by decide) a).mp (List.mem_filter.mp hEx).1
      have hMaDyn : (maM.base, 4096) ∈ dynamicRootRegions st1 :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmaM)))
      exact not_both_inRegion_of_disjointRegions (hDisjDyn _ hMaDyn) (hmInMaM a hm) hmb
  have hAbsM := ByteMap_absorb_slice hDom2Nd (keep := OwnedRwByte st1) st1.byteVal m gNew.metaBytes
    (by rw [GroupDesc.metaBytes_length]; decide) hMSubDom2
    (fun a hm hRw => by
      rw [GroupDesc.metaBytes_length] at hm
      exact hRw.2.2 ⟨m, by simp [hRes], hm⟩)
  have hAbsMb := ByteMap_absorb_slice hDom2Nd
    (keep := fun a => OwnedRwByte st1 a ∨ InRegion m gNew.metaBytes.length a)
    (writeBytesToMap st1.byteVal m gNew.metaBytes) mb groupBytes (by rw [hGbLen]; omega)
    (by rw [hGbLen]; exact hMbSubDom2)
    (fun a hmb hOr => by
      rw [hGbLen] at hmb
      rcases hOr with hRw | hm
      · exact hDisjMbDomM a hmb (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inl hRw)))
      · rw [GroupDesc.metaBytes_length] at hm
        exact hDisjMbDomM a hmb (hMInDomM a hm))
  have hCarvEq : ∀ a, CarvedUserByte st2 a ↔ CarvedUserByte st1 a := fun a => by
    constructor
    · rintro ⟨g, hg, s, hs, h⟩
      rcases List.mem_cons.mp hg with rfl | hg1
      · simp [mkLargeGroup] at hs; subst hs; cases h
      · exact ⟨g, hg1, s, hs, h⟩
    · rintro ⟨g, hg1, s, hs, h⟩
      exact ⟨g, List.mem_cons_of_mem gNew hg1, s, hs, h⟩
  have hRwPredEq : ByteMap st2.masterDom
      (fun a => (OwnedRwByte st1 a ∨ InRegion m gNew.metaBytes.length a) ∨ InRegion mb groupBytes.length a)
      st2.byteVal = ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal := by
    unfold ByteMap
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    rw [GroupDesc.metaBytes_length, hGbLen]
    have hCarvInRoot : ∀ g ∈ st1.groups, ∀ s ∈ g.slots,
        (match s with | .liveUser u rq _ => InRegion u rq a | _ => False) →
        ∃ rg ∈ st1.groups, 0 < rg.maplen ∧ InRegion rg.mem (rg.maplen * 4096) a := by
      intro g hg1 s hs hC
      cases s with
      | freeAvail | freeInactive | claimed | liveNested _ => cases hC
      | liveUser u rq ef =>
        obtain ⟨idx, hIdx, hEqS⟩ := List.mem_iff_getElem.mp hs
        have hgw := hwf1.groups_wf g hg1
        have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx; rw [hEqS] at hsw
        have hSB := group_slot_bounds hgw hIdx
        obtain ⟨rg, hrg, hrgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf1 hg1
        have hCN := (inRegion_iff_toNat (base := u) (n := rq) (by have := hsw.2.2.2.2.2.2.1; omega) a).mp hC
        exact ⟨rg, hrg, hrgMp, (inRegion_iff_toNat (base := rg.mem) (n := rg.maplen * 4096)
          (by have h := (hwf1.groups_wf rg hrg).2.2.2.2.2.2.1; simp [GroupDesc.totalBytes, hrgMp] at h; omega) a).mpr
          ⟨by have := hsw.2.2.2.2.2.1; omega, by have := hsw.2.2.2.2.2.2.1; omega⟩⟩
    constructor
    · rintro ((hRw1 | hm) | hmb)
      · exact ⟨hRw1.1.elim Or.inl (fun ⟨g, hg, hp, hi⟩ => Or.inr ⟨g, List.mem_cons_of_mem gNew hg, hp, hi⟩),
          fun hc => hRw1.2.1 ((hCarvEq a).mp hc), fun ⟨_, hx, _⟩ => by cases hx⟩
      · refine ⟨Or.inl ⟨maM, hmaM, hmInMaM a hm⟩, fun hc => ?_, fun ⟨_, hx, _⟩ => by cases hx⟩
        obtain ⟨g, hg1, s, hs, hC⟩ := (hCarvEq a).mp hc
        obtain ⟨rg, hrg, hrgMp, haRg⟩ := hCarvInRoot g hg1 s hs hC
        exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf1 hmaM hrg hrgMp) (hmInMaM a hm) haRg
      · refine ⟨Or.inr ⟨gNew, List.mem_cons_self, hMapPos, by dsimp [gNew, mkLargeGroup]; rwa [hMapMul]⟩,
          fun hc => ?_, fun ⟨_, hx, _⟩ => by cases hx⟩
        obtain ⟨g, hg1, s, hs, hC⟩ := (hCarvEq a).mp hc
        obtain ⟨rg, hrg, hrgMp, haRg⟩ := hCarvInRoot g hg1 s hs hC
        have hRgDyn : (rg.mem, rg.maplen * 4096) ∈ dynamicRootRegions st1 :=
          List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hrgMp⟩))
        exact not_both_inRegion_of_disjointRegions (hDisjDyn _ hRgDyn) haRg hmb
    · intro hRw2
      by_cases hm : InRegion m 40 a
      · exact Or.inl (Or.inr hm)
      · by_cases hmb : InRegion mb len a
        · exact Or.inr hmb
        · refine Or.inl (Or.inl ⟨?_, fun hc => hRw2.2.1 ((hCarvEq a).mpr hc),
            fun ⟨mx, hmx, _⟩ => hm (by rw [hRes] at hmx; simp at hmx; rwa [← hmx])⟩)
          rcases hRw2.1 with hMa | ⟨g, hg, hp, hi⟩
          · exact Or.inl hMa
          · rcases List.mem_cons.mp hg with rfl | hg1
            · dsimp [gNew, mkLargeGroup] at hi; rw [hMapMul] at hi; exact False.elim (hmb hi)
            · exact Or.inr ⟨g, hg1, hp, hi⟩
  have hPnEq : ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal := by
    unfold ProtNoneByteMap; refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => ?_)
    obtain ⟨hP123, _, _⟩ := pairwiseDisjoint_append hwf1.regions_disjoint.1
    obtain ⟨hP12, _, hC12Ap⟩ := pairwiseDisjoint_append hP123
    obtain ⟨_, _, hCMaGp⟩ := pairwiseDisjoint_append hP12
    have hNotM : ¬ InRegion m 40 a := fun hm =>
      hPn.elim (fun ⟨gp, hgp, haGp⟩ => not_both_inRegion_of_disjointRegions
          (hCMaGp _ (List.mem_map_of_mem hmaM) _ (List.mem_map_of_mem hgp)) (hmInMaM a hm) haGp)
        (fun ⟨ap, hap, haAp⟩ => not_both_inRegion_of_disjointRegions
          (hC12Ap _ (List.mem_append_left _ (List.mem_map_of_mem hmaM)) _ (List.mem_map_of_mem hap)) (hmInMaM a hm) haAp)
    have hNotMb : ¬ InRegion mb len a := fun hmb =>
      hDisjMbDomM a hmb (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inl hPn))))
    congr 1; change st1.byteVal a = writeBytesToMap (writeBytesToMap st1.byteVal m gNew.metaBytes) mb groupBytes a
    rw [writeBytesToMap_out _ mb groupBytes (by rwa [hGbLen]), writeBytesToMap_out _ m gNew.metaBytes (by rwa [GroupDesc.metaBytes_length])]
  have hAbsMp := MappedSet_absorb_slice hDom2Nd (keep := OwnedMappedByte st1) mb (n := len) (by omega) hMbSubDom2
    (fun a hmb hMp1 => hDisjMbDomM a hmb (List.mem_append_left _ (hwf1.masterDom_wf.2.1 a (Or.inr (Or.inr hMp1)))))
  have hMpPredEq : MappedSet st2.masterDom (fun a => OwnedMappedByte st1 a ∨ InRegion mb len a) =
      MappedSet st2.masterDom (OwnedMappedByte st2) := by
    unfold MappedSet; refine SetSep_congr (fun a _ => ⟨?_, ?_⟩) (fun _ _ _ => rfl)
    · rintro ((h1 | h2 | h3 | ⟨g, hg, hp, hi⟩) | hmb)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr ⟨g, List.mem_cons_of_mem gNew hg, hp, hi⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨gNew, List.mem_cons_self, hMapPos, by dsimp [gNew, mkLargeGroup]; rwa [hMapMul]⟩))
    · rintro (h1 | h2 | h3 | ⟨g, hg, hp, hi⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inl h2))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
      · rcases List.mem_cons.mp hg with rfl | hg1
        · dsimp [gNew, mkLargeGroup] at hi; rw [hMapMul] at hi; exact Or.inr hi
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨g, hg1, hp, hi⟩)))
  unfold MallocngCoreStInflightA; rw [pure_sepConj_of_true hwf2]
  have hByteEq : ((mb ↦ₛ groupBytes) ∗ ((m ↦ₛ gNew.metaBytes) ∗ ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal)) =
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal := by rw [hLiftRw, hAbsM, hAbsMb]; exact hRwPredEq
  have hMpEq : (memMapped mb len ∗ MappedSet st1.masterDom (OwnedMappedByte st1)) =
      MappedSet st2.masterDom (OwnedMappedByte st2) := by rw [hLiftMp, hAbsMp, hMpPredEq]
  have hPnFullEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal := hLiftPn.trans hPnEq
  change _ ⊢ MallocngLiveAuth γ st1.liveMap ∗ (A.ctx ↦ₛ st2.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
    MallocngAuxvState γ st1.auxvPtr st1.auxvSnap ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
    ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
    MappedSet st2.masterDom (OwnedMappedByte st2)
  rw [← hByteEq, ← hMpEq, ← hPnFullEq]; sep_entail

/-! ## Bitmask, `ProtNone` Disjointness, and `SlotWf` Congruence -/

private theorem bit32_sub_lowest_eq_and_not (x : BitVec 32) :
    x - ((-x) &&& x) = x &&& ~~~((-x) &&& x) := by
  bv_robdd

private theorem bit32_sub_lowest_and_zero (x y : BitVec 32) (h : x &&& y = 0#32) :
    (x - ((-x) &&& x)) &&& y = 0#32 := by
  bv_robdd

private theorem bit32_sub_lowest_or_ule (x y : BitVec 32) :
    ((x - ((-x) &&& x)) ||| y) ≤ (x ||| y) := by
  bv_robdd

theorem bit32_sub_pow2_props (k : Nat) (hk : k < 32) (x : BitVec 32)
    (hIso : (-x) &&& x = 1#32 <<< k)
    (hSet : x &&& (1#32 <<< k) = 1#32 <<< k) :
    let rem := x - ((-x) &&& x)
    x.getLsbD k = true ∧
    rem = x &&& ~~~(1#32 <<< k) ∧
    (∀ j : Nat, rem.getLsbD j = (if j = k then false else x.getLsbD j)) ∧
    (∀ y : BitVec 32, x &&& y = 0#32 → rem &&& y = 0#32) ∧
    (∀ y : BitVec 32, (rem ||| y).toNat ≤ (x ||| y).toNat) := by
  dsimp only
  have hkBit : (1#32 <<< k).getLsbD k = true := by simp [hk]
  have hxK : x.getLsbD k = true := by
    have h1 := congrArg (·.getLsbD k) hSet
    simpa [hkBit] using h1
  have hRem : x - ((-x) &&& x) = x &&& ~~~(1#32 <<< k) := by
    rw [bit32_sub_lowest_eq_and_not, hIso]
  refine ⟨hxK, hRem, ?_, fun y hy => bit32_sub_lowest_and_zero x y hy,
    fun y => BitVec.le_def.mp (bit32_sub_lowest_or_ule x y)⟩
  intro j
  rw [hRem]
  by_cases hj32 : j < 32
  · by_cases hjk : j = k
    · subst hjk; simp [hk]
    · simp only [hjk, ↓reduceIte, BitVec.getLsbD_and, BitVec.getLsbD_not, hj32, decide_true,
        Bool.true_and, BitVec.getLsbD_shiftLeft]
      have hPk : (!decide (j < k) && (1#32).getLsbD (j - k)) = false := by
        by_cases hlt : j < k
        · simp [hlt]
        · have hpos : 0 < j - k := by omega
          have h1 : (1#32).getLsbD (j - k) = false := by
            rcases hjkDiff : j - k with _ | n
            · omega
            · simp only [BitVec.getLsbD, BitVec.toNat_ofNat]
              exact Nat.testBit_lt_two_pow (by have : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2; omega)
          simp [h1]
      rw [hPk]; simp
  · have hL : (x &&& ~~~(1#32 <<< k)).getLsbD j = false := BitVec.getLsbD_of_ge _ j (by omega)
    have hR : x.getLsbD j = false := BitVec.getLsbD_of_ge _ j (by omega)
    rw [hL, hR]; split <;> rfl

namespace MallocImplH1
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
  have hSB := group_slot_bounds (hwf.groups_wf g hg) hIdx
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
  have hSB := group_slot_bounds hgw hj
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hStridePos := (group_stride_pos_and_align hgw).1
  have hSubS4 : (h.slotStart j - 4#64).toNat = (h.slotStart j).toNat - 4 := bv64_sub_toNat (by omega)
  have hStrideEq : h'.stride = h.stride := by simp [GroupDesc.stride, hLast, hMap, hSc]
  have hStorEq : h'.storage = h.storage := by simp [GroupDesc.storage, hMem]
  have hStartEq : h'.slotStart j = h.slotStart j := by simp [GroupDesc.slotStart, hStorEq, hStrideEq]
  have hEndEq : h'.slotEnd j = h.slotEnd j := by simp [GroupDesc.slotEnd, hStartEq, hStrideEq]
  have hSM : (j + 1) * h.stride = j * h.stride + h.stride := Nat.succ_mul j h.stride
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
end MallocImplH1
export MallocImplH1 (protNone_disjoint_slotWriteMod slotWf_congr_local)

def claimFreeAvailGroup (g : GroupDesc) : GroupDesc :=
  let idx := ctz32DeBruijn g.availMask
  { g with
    availMask := g.availMask - ((-g.availMask) &&& g.availMask)
    slots     := g.slots.set idx .claimed }

def claimFreeAvailSt (st : MallocngSt) (g : GroupDesc) : MallocngSt :=
  let g' := claimFreeAvailGroup g
  { st with
    groups  := replaceGroup st.groups g.metaPtr g'
    byteVal := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes }

theorem list_set_slot_props (xs : List SlotState) (idx : Nat) (hIdx : idx < xs.length)
    (sNew : SlotState) :
    ((xs.set idx sNew).filter SlotState.isClaimed).length +
        (if (xs[idx]'hIdx).isClaimed then 1 else 0) =
      (xs.filter SlotState.isClaimed).length + (if sNew.isClaimed then 1 else 0) ∧
    ((xs.set idx sNew).map slotEffCost).sum + slotEffCost (xs[idx]'hIdx) =
      (xs.map slotEffCost).sum + slotEffCost sNew ∧
    ((xs.set idx sNew).map slotLiveCount).sum + slotLiveCount (xs[idx]'hIdx) =
      (xs.map slotLiveCount).sum + slotLiveCount sNew ∧
    (∀ u r c, (∀ u₀ r₀ c₀, xs[idx]'hIdx ≠ .liveUser u₀ r₀ c₀) →
      (SlotState.liveUser u r c ∈ xs.set idx sNew ↔
        sNew = .liveUser u r c ∨ SlotState.liveUser u r c ∈ xs)) := by
  induction xs generalizing idx with
  | nil => cases hIdx
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp only [List.set, List.getElem_cons_zero, List.filter, List.map_cons, List.sum_cons,
        List.mem_cons]
      refine ⟨by cases hd <;> cases sNew <;> simp [SlotState.isClaimed] <;> omega,
        by omega, by omega, ?_⟩
      intro u r c hNot
      constructor
      · rintro (hEq | hMem)
        · exact Or.inl hEq.symm
        · exact Or.inr (Or.inr hMem)
      · rintro (rfl | hEq | hMem)
        · exact Or.inl rfl
        · exact False.elim (hNot u r c hEq.symm)
        · exact Or.inr hMem
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hIdx
      obtain ⟨h1, h2, hCnt, h3⟩ := ih k hk
      simp only [List.set, List.getElem_cons_succ, List.filter, List.map_cons, List.sum_cons,
        List.mem_cons]
      refine ⟨by cases hd.isClaimed <;> simp only [List.length_cons] <;> omega,
        by omega, by omega, ?_⟩
      intro u r c hNot
      rw [h3 u r c hNot]
      exact ⟨fun h => h.elim (fun hhd => Or.inr (Or.inl hhd))
          (fun htl => htl.elim Or.inl (fun hm => Or.inr (Or.inr hm))),
        fun h => h.elim (fun hs => Or.inr (Or.inl hs))
          (fun hm => hm.elim Or.inl (fun htl => Or.inr (Or.inr htl)))⟩

def mkReplaceSlotGroup (g : GroupDesc) (idx : Nat) (newAvail : BitVec 32)
    (sNew : SlotState) : GroupDesc :=
  { g with availMask := newAvail, slots := g.slots.set idx sNew }

def mkReplaceSlotSt (st : MallocngSt) (g : GroupDesc) (idx : Nat) (newAvail : BitVec 32)
    (sNew : SlotState) (val' : BitVec 64 → BitVec 8)
    (liveMap' : MallocngLiveMap) : MallocngSt :=
  { st with
    groups  := replaceGroup st.groups g.metaPtr (mkReplaceSlotGroup g idx newAvail sNew)
    byteVal := val'
    liveMap := liveMap' }

end VerifiedLibraries.Mallocng.Proofs
