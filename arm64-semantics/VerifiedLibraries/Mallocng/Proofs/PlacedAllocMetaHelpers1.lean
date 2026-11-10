/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.AllocMetaHelpers
public import VerifiedLibraries.Mallocng.Proofs.TryAvailHelpers
public import VerifiedLibraries.Mallocng.Proofs.EnframeUserHelpers
public import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Placed `__malloc_alloc_meta` Invariant Helpers

Meta-slot geometry, `PROT_NONE` batch disjointness, and `MallocngWFInflight` / `ByteMap`
transitions for the bump, free-meta DLL pop, and `SYS_brk` fallback paths of `__malloc_alloc_meta`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Meta-Slot Geometry and `PROT_NONE` Batch Disjointness -/

theorem nat_sep_of_disjointRegions {a b : BitVec 64} {na nb : Nat}
    (_hna : 0 < na) (_hnb : 0 < nb) (_ha : a.toNat + na ≤ 2 ^ 48) (_hb : b.toNat + nb ≤ 2 ^ 48)
    (hd : DisjointRegions a na b nb) :
    a.toNat + na ≤ b.toNat ∨ b.toNat + nb ≤ a.toNat := by
  unfold DisjointRegions at hd
  have hs1 := BitVec.toNat_sub b a
  have hs2 := BitVec.toNat_sub a b
  omega

theorem inRegion_toNat {b a : BitVec 64} {n : Nat} (hFit : b.toNat + n ≤ 2 ^ 64) :
    InRegion b n a ↔ b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + n :=
  inRegion_iff_toNat hFit a

theorem pairwiseDisjoint_append_iff {xs ys : List (BitVec 64 × Nat)} :
    PairwiseDisjointRegions (xs ++ ys) ↔
      PairwiseDisjointRegions xs ∧ PairwiseDisjointRegions ys ∧
      ∀ x ∈ xs, ∀ y ∈ ys, DisjointRegions x.1 x.2 y.1 y.2 :=
  ⟨pairwiseDisjoint_append, fun ⟨h1, h2, h3⟩ => pairwiseDisjoint_append_intro h1 h2 h3⟩

theorem mem_allMetaSlots_props {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    (∀ m ∈ allMetaSlots st,
      m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
      (∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions m 40 g.mem (g.maplen * 4096)) ∧
      ¬ CarvedUserByte st m ∧ ∀ a : BitVec 64, InRegion m 40 a → ¬ CarvedUserByte st a) ∧
    (∀ m1 ∈ allMetaSlots st, ∀ m2 ∈ allMetaSlots st, m1 ≠ m2 → DisjointRegions m1 40 m2 40) := by
  have hMaB := hwf.metaAreas_wf.2.1; constructor
  · intro m hm; unfold allMetaSlots at hm; obtain ⟨ma, hma, hmSlot⟩ := List.mem_flatMap.mp hm; obtain ⟨k, hkR, rfl⟩ := List.mem_map.mp hmSlot
    have hkLt := List.mem_range.mp hkR; have hb := hMaB ma hma; have hSlotNat : (ma.slotAddr k).toNat = ma.base.toNat + 24 + 40 * k := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    have hNe0 : ma.slotAddr k ≠ 0#64 := fun h => by have := congrArg BitVec.toNat h; simp at this; omega
    have hDisjRg : ∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions (ma.slotAddr k) 40 g.mem (g.maplen * 4096) := fun g hg hml => by
      obtain ⟨_, _, _, _, _, _, hgTotFit, _⟩ := hwf.groups_wf g hg; have hgTot : g.totalBytes = g.maplen * 4096 := (by simp [GroupDesc.totalBytes, hml])
      have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff] at hpd
      have hDisjMa := hpd.2.2 (ma.base, (4096 : Nat)) (List.mem_map_of_mem hma) (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))))
      dsimp only at hDisjMa; have := nat_sep_of_disjointRegions (by decide) (by omega) hb.2.2.1 (hgTot ▸ hgTotFit) hDisjMa; exact disjointRegions_of_nat_bounds (by decide) (by omega) (by omega) (hgTot ▸ hgTotFit) (by omega)
    have hNoUser : ∀ a : BitVec 64, InRegion (ma.slotAddr k) 40 a → ¬ CarvedUserByte st a := fun a ha ⟨g, hg, s, hs, hInU⟩ => by
      cases s with
      | freeAvail | freeInactive | claimed | liveNested _ => cases hInU
      | liveUser _ _ _ =>
        obtain ⟨idx, hIdx, hsEq⟩ := List.mem_iff_getElem.mp hs; obtain ⟨_, _, hgLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hSlotWf⟩ := hwf.groups_wf g hg
        have hswf := hSlotWf idx hIdx; rw [hsEq] at hswf; obtain ⟨_, hStartLe, hReqLe, _⟩ := hswf.2.2.2.2; have ⟨hStartNat, _, hEndLe⟩ := group_slotStart_End_toNat (hwf.groups_wf g hg) idx (by unfold GroupDesc.cnt at hgLen; omega)
        obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, _⟩ := rootAncestor_of_group hwf g hg; obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hwf.groups_wf rg hrg; have hrgTot : rg.totalBytes = rg.maplen * 4096 := (by simp [GroupDesc.totalBytes, hrgMl])
        have haSlot := (inRegion_toNat (by omega)).mp ha; have haU := (inRegion_toNat (by omega)).mp hInU; have := nat_sep_of_disjointRegions (by decide) (by omega) (by omega) (hrgTot ▸ hrgTotFit) (hDisjRg rg hrg hrgMl); omega
    exact ⟨hNe0, by omega, by omega, by omega, hDisjRg, hNoUser (ma.slotAddr k) (by simp [InRegion]), hNoUser⟩
  · intro m1 hm1 m2 hm2 hne; unfold allMetaSlots at hm1 hm2; obtain ⟨ma1, hma1, hs1⟩ := List.mem_flatMap.mp hm1; obtain ⟨k1, hk1R, rfl⟩ := List.mem_map.mp hs1; obtain ⟨ma2, hma2, hs2⟩ := List.mem_flatMap.mp hm2; obtain ⟨k2, hk2R, rfl⟩ := List.mem_map.mp hs2
    have hk1 := List.mem_range.mp hk1R; have hk2 := List.mem_range.mp hk2R; have hb1 := hMaB ma1 hma1; have hb2 := hMaB ma2 hma2
    have hn1 : (ma1.slotAddr k1).toNat = ma1.base.toNat + 24 + 40 * k1 := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    have hn2 : (ma2.slotAddr k2).toNat = ma2.base.toNat + 24 + 40 * k2 := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    have hNeNat : (ma1.slotAddr k1).toNat ≠ (ma2.slotAddr k2).toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
    exact disjointRegions_of_nat_bounds (by decide) (by decide) (by omega) (by omega) (by by_cases hS : ma1.base.toNat = ma2.base.toNat <;> omega)

theorem disjoint_protNone_batch {inflight : Nat} {A : MallocngAddrs} {brkStart brk mb : BitVec 64}
    {liveCost peakCost len : Nat} {st : MallocngSt} {ctxBs : List (BitVec 8)} {m : Memory} {R : SepProp}
    (hwf : MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st)
    (hNoAvail : st.availMetaPages = [])
    (_hAlign : 4096 ∣ mb.toNat) (hLen8192 : 8192 ≤ len) (hFit : mb.toNat + len ≤ 2 ^ 48)
    (hm : m ⊨ (mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len ∗ (A.ctx ↦ₛ ctxBs) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :
    ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 mb len := by
  have hmPn : m ⊨ (mb ↦ₙ List.replicate len 0#8) ∗ (memMapped mb len ∗ (A.ctx ↦ₛ ctxBs) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  have hPnPerm : ∀ x : BitVec 64, InRegion mb len x → m.perm x = some Perm.protNone := fun x hx =>
    (IsBlockProtNone.pointsToBytesProtNone_len (List.length_replicate (n := len) (a := 0#8))).perm_protNone hmPn hx
  intro r hr; unfold dynamicRootRegions at hr; simp only [List.mem_append] at hr
  rcases hr with ((hmaList | hgpList) | hapList) | hrgList
  · obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hmaList; dsimp only; have hmaB := hwf.metaAreas_wf.2.1 ma hma
    refine disjointRegions_of_nat_bounds (by decide) (by omega) hmaB.2.2.1 hFit (Classical.byContradiction fun hno => ?_)
    have hxIn : InRegion mb len ma.base := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩
    have ⟨hOwn, hDom⟩ := metaArea_base_ownedRw hwf hma
    have hEx := ByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal ma.base (n := 1) (by decide)
      (fun a ha => (show a = ma.base from BitVec.eq_of_toNat_eq (by have := (inRegion_toNat (by omega)).mp ha; omega)) ▸ hDom)
      (fun a ha => (show a = ma.base from BitVec.eq_of_toNat_eq (by have := (inRegion_toNat (by omega)).mp ha; omega)) ▸ hOwn)
    have hm' : m ⊨ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ((mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len ∗ (A.ctx ↦ₛ ctxBs) ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    rw [hEx, sepConj_assoc] at hm'
    have hRw := (IsBlock.pointsToBytes ma.base (readBytesFromMap st.byteVal ma.base 1)).perm_rw hm' (a := ma.base) (by simp [InRegion, readBytesFromMap_length])
    rw [hPnPerm _ hxIn] at hRw; cases hRw
  · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hgpList; dsimp only; have hgpB := hwf.guard_avail_wf.2.1 gp hgp
    refine disjointRegions_of_nat_bounds (by decide) (by omega) hgpB.2.2 hFit (Classical.byContradiction fun hno => ?_)
    have hxIn : InRegion mb len gp := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩
    have hOwn : OwnedProtNoneByte st gp := Or.inl ⟨gp, hgp, by simp [InRegion]⟩
    have hDom : gp ∈ st.masterDom := hwf.masterDom_wf.2.1 gp (Or.inr (Or.inl hOwn))
    have hEx1 := ProtNoneByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal gp (n := 1) (by decide)
      (fun a ha => (show a = gp from BitVec.eq_of_toNat_eq (by have := (inRegion_toNat (by omega)).mp ha; omega)) ▸ hDom)
      (fun a ha => (show a = gp from BitVec.eq_of_toNat_eq (by have := (inRegion_toNat (by omega)).mp ha; omega)) ▸ hOwn)
    have hRepEq : List.replicate len 0#8 = readBytesFromMap (fun _ => 0#8) mb len :=
      List.ext_getElem (by simp [readBytesFromMap_length]) (fun _ _ _ => by simp [readBytesFromMap_getElem])
    have hEx2 : (mb ↦ₙ List.replicate len 0#8) = ((gp ↦₈ₙ 0#8) ∗ SetSep (rangeAddrs mb len) (fun a => True ∧ a ≠ gp) (fun a => a ↦₈ₙ 0#8)) := by
      have hSub := SetSep_eq_BigSep_of_sub (nodup_rangeAddrs mb (n := len) (by omega)) (nodup_rangeAddrs mb (n := len) (by omega)) (fun _ hx => hx) (keep := fun _ => True) (fun _ hx => ⟨fun _ => hx, fun _ => trivial⟩) (fun a => a ↦₈ₙ 0#8)
      rw [hRepEq, ← BigSep_pointsTo8ProtNone_rangeAddrs (fun _ => 0#8) mb len, ← hSub]
      exact SetSep_focus (nodup_rangeAddrs mb (n := len) (by omega)) (keep := fun _ => True) (fun a => a ↦₈ₙ 0#8) ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) gp).mpr hxIn) trivial
    have hRead1 : readBytesFromMap st.byteVal gp 1 = [st.byteVal gp] := by simp [readBytesFromMap, rangeAddrs]
    have hm' : m ⊨ ((gp ↦₈ₙ 0#8) ∗ (gp ↦₈ₙ st.byteVal gp)) ∗ (SetSep (rangeAddrs mb len) (fun a => True ∧ a ≠ gp) (fun a => a ↦₈ₙ 0#8) ∗ ProtNoneByteMap st.masterDom (fun a => OwnedProtNoneByte st a ∧ ¬InRegion gp 1 a) st.byteVal ∗ memMapped mb len ∗ (A.ctx ↦ₛ ctxBs) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st) ∗ R) := by
      have hm0 := hm; rw [hEx1, hRead1, pointsToBytesProtNone_cons, pointsToBytesProtNone_nil, hEx2] at hm0; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm0
    exact not_satisfies_false_sepConj (Satisfies.mono (sepConj_mono_left (pointsTo8ProtNone_conflict gp 0#8 (st.byteVal gp))) hm')
  · rw [hNoAvail] at hapList; cases hapList
  · obtain ⟨rg, hrgFilt, rfl⟩ := List.mem_map.mp hrgList; dsimp only
    obtain ⟨hrg, hrgMlB⟩ := List.mem_filter.mp hrgFilt
    have hrgMl : 0 < rg.maplen := of_decide_eq_true hrgMlB
    obtain ⟨_, _, _, _, _, _, hrgFit, _⟩ := hwf.groups_wf rg hrg
    have hrgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hrgMl]
    have hEx := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st) rg.mem (n := rg.maplen * 4096) (by omega)
      (fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rg, hrg, hrgMl, ha⟩))))))
      (fun a ha => Or.inr (Or.inr (Or.inr ⟨rg, hrg, hrgMl, ha⟩)))
    have hm' : m ⊨ memMapped rg.mem (rg.maplen * 4096) ∗ (memMapped mb len ∗ (MappedSet st.masterDom (fun a => OwnedMappedByte st a ∧ ¬InRegion rg.mem (rg.maplen * 4096) a) ∗ (mb ↦ₙ List.replicate len 0#8) ∗ (A.ctx ↦ₛ ctxBs) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ R)) := by
      have hm0 := hm; rw [hEx] at hm0; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm0
    exact Satisfies.disjointRegions_of_memMapped (by omega) (by omega) hm'

/-! ## `MallocngWFInflight` and `ByteMap` Path Transitions -/

theorem carvedMeta_byteMap_extract {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {m : BitVec 64}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hmFreeBump : m ∈ st.freeMetas.map (·.ptr) ++ st.bumpMetas) :
    (m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48) ∧ m ∉ st.reservedMetas ∧ (∀ ma' ∈ st.metaAreas, DisjointRegions ma'.base 24 m 40) ∧
    (∀ g ∈ st.groups, ∀ a : BitVec 64, InRegion m 40 a → ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion g.mem g.totalBytes a) ∧ (∀ a : BitVec 64, InRegion m 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((m ↦ₛ readBytesFromMap st.byteVal m 40) ∗ ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion m 40 a) st.byteVal) := by
  have ⟨hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2; have hUfEq : st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas = st.groups.map (·.metaPtr) ++ ((st.freeMetas.map (·.ptr) ++ st.bumpMetas) ++ st.reservedMetas) := (by simp [List.append_assoc])
  rw [hUfEq] at hUfNd; have ⟨_, hRestNd, hDisjGs⟩ := List.nodup_append.mp hUfNd; have ⟨_, _, hDisjRes⟩ := List.nodup_append.mp hRestNd; have hmNotRes : m ∉ st.reservedMetas := fun hr => hDisjRes m hmFreeBump m hr rfl
  have hmAll : m ∈ allMetaSlots st := (hUfIff m).mp (by rw [hUfEq]; exact List.mem_append_right _ (List.mem_append_left _ hmFreeBump)); have ⟨hSlotProps, hAllDisj⟩ := mem_allMetaSlots_props hwf; obtain ⟨hNe0, hGe, hMod8, hFit, hDisjRg, _, hNoUser⟩ := hSlotProps m hmAll
  have hMaHdrDisj : ∀ ma' ∈ st.metaAreas, DisjointRegions ma'.base 24 m 40 := fun ma' hma' => by
    have hmAll' := hmAll; unfold allMetaSlots at hmAll'; obtain ⟨ma, hma, hmS⟩ := List.mem_flatMap.mp hmAll'; obtain ⟨k, hkR, rfl⟩ := List.mem_map.mp hmS; have hkLt := List.mem_range.mp hkR; have hb := hwf.metaAreas_wf.2.1 ma hma; have hb' := hwf.metaAreas_wf.2.1 ma' hma'
    have hSlotNat : (ma.slotAddr k).toNat = ma.base.toNat + 24 + 40 * k := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); exact disjointRegions_of_nat_bounds (by decide) (by decide) (by omega) hFit (by by_cases hS : ma'.base.toNat = ma.base.toNat <;> omega)
  have hGrpDisj : ∀ g ∈ st.groups, ∀ a : BitVec 64, InRegion m 40 a → ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion g.mem g.totalBytes a := fun g hg a ha => by
    have hgAll : g.metaPtr ∈ allMetaSlots st := (hUfIff g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
    have hD1 := hAllDisj m hmAll g.metaPtr hgAll (fun h => hDisjGs g.metaPtr (List.mem_map_of_mem hg) m (List.mem_append_left _ hmFreeBump) h.symm); obtain ⟨_, _, _, _, _, _, hgTotFit, _⟩ := hwf.groups_wf g hg; obtain ⟨_, _, _, hgMetaFit, _⟩ := hSlotProps g.metaPtr hgAll; have h1 := (inRegion_toNat (by omega)).mp ha
    refine ⟨fun haG => by have h2 := (inRegion_toNat (by omega)).mp haG; have := nat_sep_of_disjointRegions (by decide) (by decide) hFit hgMetaFit hD1; omega, fun haMem => ?_⟩
    obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, _⟩ := rootAncestor_of_group hwf g hg; obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hwf.groups_wf rg hrg; have hrgTot : rg.totalBytes = rg.maplen * 4096 := (by simp [GroupDesc.totalBytes, hrgMl]); have h2 := (inRegion_toNat (by omega)).mp haMem; have := nat_sep_of_disjointRegions (by decide) (by omega) hFit (hrgTot ▸ hrgTotFit) (hDisjRg rg hrg hrgMl); omega
  have hOwnDom : ∀ a : BitVec 64, InRegion m 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom := fun a ha => by
    have hmAll' := hmAll; unfold allMetaSlots at hmAll'; obtain ⟨ma, hma, hmS⟩ := List.mem_flatMap.mp hmAll'; obtain ⟨k, hkR, hmk⟩ := List.mem_map.mp hmS; have hkLt := List.mem_range.mp hkR; have hb := hwf.metaAreas_wf.2.1 ma hma; have hSlotNat : m.toNat = ma.base.toNat + 24 + 40 * k := (by rw [← hmk]; unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    have haNat := (inRegion_toNat (by omega)).mp ha; have hInMa : InRegion ma.base 4096 a := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩
    have hNoRes : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ => by have hmrAll : mr ∈ allMetaSlots st := (hUfIff mr).mp (List.mem_append_right _ hmr); obtain ⟨_, _, _, hmrFit, _⟩ := hSlotProps mr hmrAll; have h2 := (inRegion_toNat (by omega)).mp haMr; have := nat_sep_of_disjointRegions (by decide) (by decide) hFit hmrFit (hAllDisj m hmAll mr hmrAll (fun h => hmNotRes (h ▸ hmr))); omega
    have hOwn : OwnedRwByte st a := ⟨Or.inl ⟨ma, hma, hInMa⟩, hNoUser a ha, hNoRes⟩; exact ⟨hOwn, hwf.masterDom_wf.2.1 a (Or.inl hOwn)⟩
  exact ⟨⟨hNe0, hGe, hMod8, hFit⟩, hmNotRes, hMaHdrDisj, hGrpDisj, hOwnDom, ByteMap_extract_slice hwf.masterDom_wf.1 st.byteVal m (n := 40) (by omega) (fun a ha => (hOwnDom a ha).2) (fun a ha => (hOwnDom a ha).1)⟩

private theorem nodup_move_to_reserved {α : Type} {A B C : List α} {m : α} (hNd : (A ++ (m :: B) ++ C).Nodup) : (A ++ B ++ (m :: C)).Nodup ∧ ∀ x, x ∈ A ++ B ++ (m :: C) ↔ x ∈ A ++ (m :: B) ++ C := by
  have ⟨hABNd, hCNd, hDisjC⟩ := List.nodup_append.mp hNd; have ⟨hANd, hmBNd, hDisjAB⟩ := List.nodup_append.mp hABNd; have ⟨hmNotB, hBNd⟩ := List.nodup_cons.mp hmBNd
  refine ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hANd, hBNd, fun x hx y hy => hDisjAB x hx y (List.Mem.tail m hy)⟩, List.nodup_cons.mpr ⟨fun hmC => hDisjC m (List.mem_append_right _ (List.Mem.head B)) m hmC rfl, hCNd⟩, ?_⟩, ?_⟩
  · intro x hxAB y hyMC hxy; subst hxy; exact (List.mem_cons.mp hyMC).elim (fun hEq => by subst hEq; exact (List.mem_append.mp hxAB).elim (fun hxA => hDisjAB x hxA x (List.Mem.head B) rfl) hmNotB)
      fun hxC => (List.mem_append.mp hxAB).elim (fun hxA => hDisjC x (List.mem_append_left _ hxA) x hxC rfl) (fun hxB => hDisjC x (List.mem_append_right _ (List.Mem.tail m hxB)) x hxC rfl)
  · intro x; simp only [List.mem_append, List.mem_cons]; exact ⟨fun h => h.elim (fun hAB => hAB.elim (Or.inl ∘ Or.inl) (Or.inl ∘ Or.inr ∘ Or.inr)) (fun hMC => hMC.elim (Or.inl ∘ Or.inr ∘ Or.inl) Or.inr),
      fun h => h.elim (fun hAMB => hAMB.elim (Or.inl ∘ Or.inl) (fun hMB => hMB.elim (Or.inr ∘ Or.inl) (Or.inl ∘ Or.inr))) (Or.inr ∘ Or.inr)⟩

theorem fastPath2_bump_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (_hNoFree : st.freeMetas = []) (hBumpNe : st.ctx.availMetaCount ≠ 0#64) :
    let m := st.ctx.availMeta; let st' : MallocngSt := { st with ctx := { st.ctx with availMeta := m + 40#64, availMetaCount := st.ctx.availMetaCount - 1#64 }, bumpMetas := st.bumpMetas.tail, reservedMetas := m :: st.reservedMetas }
    (m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas) ∧ MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((m ↦ₛ List.replicate 40 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal) ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  dsimp only; rcases hwf.free_bump_metas_wf.2.2.1 with ⟨hZero, _⟩ | ⟨hCntPos, hCntLe, hne, hAvailEq, hBumpEq⟩; · exact False.elim (hBumpNe hZero)
  let tail := st.metaAreas.getLast hne; let k0 := 101 - st.ctx.availMetaCount.toNat; let n := st.ctx.availMetaCount.toNat - 1; have hCntSucc : st.ctx.availMetaCount.toNat = n + 1 := (by omega)
  have hBumpCons : st.bumpMetas = st.ctx.availMeta :: (List.range n).map (fun j => tail.slotAddr ((k0 + 1) + j)) := by
    rw [hBumpEq, show List.range st.ctx.availMetaCount.toNat = 0 :: (List.range n).map (· + 1) by rw [hCntSucc, List.range_succ_eq_map], List.map_cons, List.map_map]
    congr 1; · rw [hAvailEq]; congr 1
    · apply List.map_congr_left; intro j _; dsimp only [Function.comp, tail, k0]; congr 1; omega
  have hmInBump : st.ctx.availMeta ∈ st.bumpMetas := (by rw [hBumpCons]; exact List.Mem.head _); obtain ⟨⟨hNe0, hGe, hMod8, hFit⟩, hmNotRes, _, _, _, hEx⟩ := carvedMeta_byteMap_extract hwf (List.mem_append_right _ hmInBump)
  have hSubNat : (st.ctx.availMetaCount - 1#64).toNat = n := (by rw [BitVec.toNat_sub_of_le (by show (1#64).toNat ≤ _; simp; omega)]; simp; omega)
  have hBumpTail : st.bumpMetas.tail = (List.range n).map (fun j => tail.slotAddr ((k0 + 1) + j)) := (by rw [hBumpCons]; rfl); have ⟨hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hUfMove : ((st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr)) ++ st.bumpMetas.tail ++ (st.ctx.availMeta :: st.reservedMetas)).Nodup ∧ ∀ x, x ∈ (st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr)) ++ st.bumpMetas.tail ++ (st.ctx.availMeta :: st.reservedMetas) ↔ x ∈ allMetaSlots st := by
    have h1 := hUfNd; rw [hBumpCons] at h1; have ⟨hNd', hMem'⟩ := nodup_move_to_reserved (A := st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr)) (B := (List.range n).map (fun j => tail.slotAddr ((k0 + 1) + j))) (C := st.reservedMetas) (m := st.ctx.availMeta) h1
    rw [hBumpTail]; exact ⟨hNd', fun x => (hMem' x).trans (by rw [← hBumpCons]; exact hUfIff x)⟩
  let st' : MallocngSt := { st with ctx := { st.ctx with availMeta := st.ctx.availMeta + 40#64, availMetaCount := st.ctx.availMetaCount - 1#64 }, bumpMetas := st.bumpMetas.tail, reservedMetas := st.ctx.availMeta :: st.reservedMetas }
  have hKeepRw : ∀ a : BitVec 64, (OwnedRwByte st a ∧ ¬ InRegion st.ctx.availMeta 40 a) ↔ OwnedRwByte st' a := fun a => by
    simp only [OwnedRwByte, CarvedUserByte, CarvedMetaByte, st', List.mem_cons]
    exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, by rintro ⟨mr, rfl | hmr, ha⟩; exact h4 ha; exact h3 ⟨mr, hmr, ha⟩⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, fun ⟨mr, hmr, ha⟩ => h3 ⟨mr, Or.inr hmr, ha⟩⟩, fun ha => h3 ⟨_, Or.inl rfl, ha⟩⟩⟩
  have hWf' : MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' := {
    base_wf := hwf.base_wf, brk_bounds := hwf.brk_bounds, ctx_lens := hwf.ctx_lens, initDone_wf := hwf.initDone_wf, initZero_wf := fun h0 => False.elim (hBumpNe ((hwf.initZero_wf h0).1 ▸ rfl))
    bounces_wf := hwf.bounces_wf, usage_wf := hwf.usage_wf, brk_mode_wf := hwf.brk_mode_wf, metaAreas_wf := hwf.metaAreas_wf, guard_avail_wf := hwf.guard_avail_wf
    inflight_wf := by have := hwf.inflight_wf; simp [st', totalClaimedSlots] at *; omega
    free_bump_metas_wf := ⟨hwf.free_bump_metas_wf.1, hwf.free_bump_metas_wf.2.1, by
      by_cases hn0 : n = 0
      · exact Or.inl ⟨BitVec.eq_of_toNat_eq (by simp [st', hSubNat, hn0]), by simp [st', hBumpTail, hn0]⟩
      · refine Or.inr ⟨by simp [st', hSubNat]; omega, by simp [st', hSubNat]; omega, ⟨hne, ?_, by dsimp only [st']; rw [hBumpTail, hSubNat, show 101 - n = k0 + 1 by omega]⟩⟩
        dsimp only [st']; rw [hAvailEq]; unfold MetaAreaDesc.slotAddr; rw [show 101 - (st.ctx.availMetaCount - 1#64).toNat = k0 + 1 by rw [hSubNat]; omega, BitVec.add_assoc]; congr 1
        have hTailB := hwf.metaAreas_wf.2.1 tail (List.getLast_mem hne); apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega,
      fun bm hbm => hwf.free_bump_metas_wf.2.2.2.1 bm (by rw [hBumpCons]; exact List.Mem.tail _ (hBumpTail ▸ hbm)), hUfMove.1, hUfMove.2⟩
    groups_nodup := hwf.groups_nodup, groups_wf := hwf.groups_wf, regions_disjoint := hwf.regions_disjoint, active_wf := hwf.active_wf, liveMap_wf := hwf.liveMap_wf, live_le_peak := hwf.live_le_peak
    effCost_le_live := hwf.effCost_le_live, meta_pages_bound := hwf.meta_pages_bound, empty_groups_bound := hwf.empty_groups_bound
    masterDom_wf := ⟨hwf.masterDom_wf.1, fun a h => hwf.masterDom_wf.2.1 a (h.elim (fun hRw => Or.inl ((hKeepRw a).mpr hRw).1) Or.inr), hwf.masterDom_wf.2.2⟩ }
  refine ⟨⟨hNe0, hGe, hMod8, hFit, hmNotRes⟩, hWf', ?_, rfl, rfl⟩
  rw [hEx, hwf.free_bump_metas_wf.2.2.2.1 st.ctx.availMeta hmInBump]; exact congrArg _ (SetSep_congr (fun a _ => hKeepRw a) (fun _ _ _ => rfl))

theorem freeMeta_pop_wf_of_byteVal {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    {fm0 : FreeMetaDesc} {fmRest newFms : List FreeMetaDesc} {newHead : BitVec 64} {newVal : BitVec 64 → BitVec 8}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hFmEq : st.freeMetas = fm0 :: fmRest) (hNewPtrs : newFms.map (·.ptr) = fmRest.map (·.ptr))
    (hNewDll : CircularDllWf newHead (newFms.map fun fm => (fm.ptr, fm.prev, fm.next))) (hNewBytes : ∀ fm ∈ newFms, readBytesFromMap newVal fm.ptr 40 = fm.toBytes)
    (hValSupport : ∀ a : BitVec 64, newVal a ≠ st.byteVal a → ∃ fm ∈ fmRest, InRegion fm.ptr 40 a) :
    let m := fm0.ptr; let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := newHead }, freeMetas := newFms, reservedMetas := m :: st.reservedMetas, byteVal := newVal }
    MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧ (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    (∀ a : BitVec 64, (OwnedRwByte st a ∧ ¬ InRegion m 40 a) ↔ OwnedRwByte st' a) ∧ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
  dsimp only; let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := newHead }, freeMetas := newFms, reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := newVal }
  have hRestProps : ∀ fm ∈ fmRest, (∀ ma' ∈ st.metaAreas, DisjointRegions ma'.base 24 fm.ptr 40) ∧ (∀ g ∈ st.groups, ∀ a : BitVec 64, InRegion fm.ptr 40 a → ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion g.mem g.totalBytes a) ∧ (∀ a : BitVec 64, InRegion fm.ptr 40 a → OwnedRwByte st a) := fun fm hfm => by
    obtain ⟨_, _, h1, h2, h3, _⟩ := carvedMeta_byteMap_extract hwf (by rw [hFmEq]; exact List.mem_append_left _ (List.Mem.tail _ (List.mem_map_of_mem hfm))); exact ⟨h1, h2, fun a ha => (h3 a ha).1⟩
  have hPnAg : ∀ a : BitVec 64, OwnedProtNoneByte st a → newVal a = st.byteVal a := fun a hPn => Classical.byContradiction fun hne => by
    obtain ⟨fm, hfm, haFm⟩ := hValSupport a hne; have hRw := (hRestProps fm hfm).2.2 a haFm; rcases hRw.1 with ⟨ma, hma, haMa⟩ | ⟨g, hg, hgMl, haG⟩
    · have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff] at hpd; have hb1 := hwf.metaAreas_wf.2.1 ma hma; have h1 := (inRegion_toNat (by omega)).mp haMa
      rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
      · have hD := hpd.2.2 (ma.base, 4096) (List.mem_map_of_mem hma) (gp, 4096) (List.mem_append_left _ (List.mem_map_of_mem hgp)); dsimp only at hD; unfold DisjointRegions at hD; have hb2 := hwf.guard_avail_wf.2.1 gp hgp; have h2 := (inRegion_toNat (by omega)).mp haGp; have := BitVec.toNat_sub gp ma.base; have := BitVec.toNat_sub ma.base gp; omega
      · have hD := hpd.2.2 (ma.base, 4096) (List.mem_map_of_mem hma) (ap, 4096) (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hap))); dsimp only at hD; unfold DisjointRegions at hD; have hb2 := hwf.guard_avail_wf.2.2.2 ap hap; have h2 := (inRegion_toNat (by omega)).mp haAp; have := BitVec.toNat_sub ap ma.base; have := BitVec.toNat_sub ma.base ap; omega
    · exact ((hRestProps fm hfm).2.1 g hg a haFm).2 ((show g.totalBytes = g.maplen * 4096 by simp [GroupDesc.totalBytes, hgMl]) ▸ haG)
  have hGrpByteAg : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ (0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) → st'.byteVal a = st.byteVal a := fun g hg a hIn => Classical.byContradiction fun hne => by
    obtain ⟨fm, hfm, haFm⟩ := hValSupport a hne; have ⟨_, hGrp, _⟩ := hRestProps fm hfm; exact hIn.elim (hGrp g hg a haFm).1 fun ⟨hgMl, haMem⟩ => (hGrp g hg a haFm).2 ((show g.totalBytes = g.maplen * 4096 by simp [GroupDesc.totalBytes, hgMl]) ▸ haMem)
  obtain ⟨hGwf', hActWf', hGrpPost, hClaimEq, hEffEq⟩ := groups_active_wf_congr (st' := st') hwf rfl rfl rfl hGrpByteAg; have ⟨hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hUfMove : ((st.groups.map (·.metaPtr) ++ newFms.map (·.ptr)) ++ st.bumpMetas ++ (fm0.ptr :: st.reservedMetas)).Nodup ∧ ∀ x, x ∈ (st.groups.map (·.metaPtr) ++ newFms.map (·.ptr)) ++ st.bumpMetas ++ (fm0.ptr :: st.reservedMetas) ↔ x ∈ allMetaSlots st := by
    rw [hNewPtrs]; have h1 := hUfNd; rw [hFmEq, List.map_cons] at h1
    have hEq1 : st.groups.map (·.metaPtr) ++ (fm0.ptr :: fmRest.map (·.ptr)) ++ st.bumpMetas ++ st.reservedMetas = st.groups.map (·.metaPtr) ++ (fm0.ptr :: (fmRest.map (·.ptr) ++ st.bumpMetas)) ++ st.reservedMetas := (by simp [List.append_assoc])
    have hEq2 : (st.groups.map (·.metaPtr) ++ fmRest.map (·.ptr)) ++ st.bumpMetas ++ (fm0.ptr :: st.reservedMetas) = st.groups.map (·.metaPtr) ++ (fmRest.map (·.ptr) ++ st.bumpMetas) ++ (fm0.ptr :: st.reservedMetas) := (by simp [List.append_assoc])
    rw [hEq1] at h1; rw [hEq2]; have ⟨hNd', hMem'⟩ := nodup_move_to_reserved h1; exact ⟨hNd', fun x => (hMem' x).trans (by rw [← hEq1, ← List.map_cons, ← hFmEq]; exact hUfIff x)⟩
  have hKeepRw : ∀ a : BitVec 64, (OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ↔ OwnedRwByte st' a := fun a => by
    simp only [OwnedRwByte, CarvedUserByte, CarvedMetaByte, st', List.mem_cons]
    exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, by rintro ⟨mr, rfl | hmr, ha⟩; exact h4 ha; exact h3 ⟨mr, hmr, ha⟩⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, fun ⟨mr, hmr, ha⟩ => h3 ⟨mr, Or.inr hmr, ha⟩⟩, fun ha => h3 ⟨_, Or.inl rfl, ha⟩⟩⟩
  refine ⟨{
    base_wf := hwf.base_wf, brk_bounds := hwf.brk_bounds, ctx_lens := hwf.ctx_lens, initDone_wf := hwf.initDone_wf, initZero_wf := fun h0 => by have hz := (hwf.initZero_wf h0).2.2.2.2.2.2.1; rw [hz] at hFmEq; cases hFmEq
    bounces_wf := hwf.bounces_wf, usage_wf := hwf.usage_wf, brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
      have hb := hwf.metaAreas_wf.2.1 ma hma; refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩; rw [← hb.2.2.2]; refine readBytesFromMap_congr (by omega) fun a ha => Classical.byContradiction fun hne => ?_
      obtain ⟨fm, hfm, haFm⟩ := hValSupport a hne; have hD := (hRestProps fm hfm).1 ma hma; unfold DisjointRegions at hD
      have ⟨_, _, _, hFmFit, _⟩ := (mem_allMetaSlots_props hwf).1 fm.ptr ((hUfIff fm.ptr).mp (by rw [hFmEq]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.tail _ (List.mem_map_of_mem hfm))))))
      have h1 := (inRegion_toNat (by omega)).mp ha; have h2 := (inRegion_toNat (by omega)).mp haFm; have := BitVec.toNat_sub fm.ptr ma.base; have := BitVec.toNat_sub ma.base fm.ptr; omega, hwf.metaAreas_wf.2.2⟩
    guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1, fun ap hap => by have hb := hwf.guard_avail_wf.2.2.2 ap hap; exact ⟨hb.1, hb.2.1, hb.2.2.1, by rw [← hb.2.2.2]; exact readBytesFromMap_congr (by omega) fun a ha => hPnAg a (Or.inr ⟨ap, hap, ha⟩)⟩⟩
    inflight_wf := by have := hwf.inflight_wf; rw [show st'.reservedMetas.length = st.reservedMetas.length + 1 from rfl, hClaimEq]; omega
    free_bump_metas_wf := ⟨hNewDll, hNewBytes, hwf.free_bump_metas_wf.2.2.1, fun bm hbm => by
      rw [← hwf.free_bump_metas_wf.2.2.2.1 bm hbm]; refine readBytesFromMap_congr (by omega) fun a ha => Classical.byContradiction fun hne => ?_
      obtain ⟨fm, hfm, haFm⟩ := hValSupport a hne; have ⟨hSlotProps, hAllDisj⟩ := mem_allMetaSlots_props hwf; have hbmAll : bm ∈ allMetaSlots st := (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
      have hfmAll : fm.ptr ∈ allMetaSlots st := (hUfIff fm.ptr).mp (by rw [hFmEq]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.tail _ (List.mem_map_of_mem hfm)))))
      have hNe : bm ≠ fm.ptr := fun hEq => by have ⟨h1, _⟩ := List.nodup_append.mp hUfNd; have ⟨_, _, hDisjFB⟩ := List.nodup_append.mp h1; exact hDisjFB fm.ptr (List.mem_append_right _ (by rw [hFmEq]; exact List.Mem.tail _ (List.mem_map_of_mem hfm))) bm hbm hEq.symm
      have hD := hAllDisj bm hbmAll fm.ptr hfmAll hNe; unfold DisjointRegions at hD; obtain ⟨_, _, _, hbmFit, _⟩ := hSlotProps bm hbmAll; obtain ⟨_, _, _, hfmFit, _⟩ := hSlotProps fm.ptr hfmAll
      have h1 := (inRegion_toNat (by omega)).mp ha; have h2 := (inRegion_toNat (by omega)).mp haFm; have := BitVec.toNat_sub fm.ptr bm; have := BitVec.toNat_sub bm fm.ptr; omega, hUfMove.1, hUfMove.2⟩
    groups_nodup := hwf.groups_nodup, groups_wf := hGwf', regions_disjoint := hwf.regions_disjoint, active_wf := hActWf', liveMap_wf := hwf.liveMap_wf, live_le_peak := hwf.live_le_peak
    effCost_le_live := hEffEq ▸ hwf.effCost_le_live, meta_pages_bound := hwf.meta_pages_bound, empty_groups_bound := hwf.empty_groups_bound
    masterDom_wf := ⟨hwf.masterDom_wf.1, fun a h => hwf.masterDom_wf.2.1 a (h.elim (fun hRw => Or.inl ((hKeepRw a).mpr hRw).1) Or.inr), hwf.masterDom_wf.2.2⟩
  }, hGrpPost, hKeepRw, SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => by rw [hPnAg a hPn])⟩

theorem fastPath1_singleton_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {fm0 : FreeMetaDesc}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hFmEq : st.freeMetas = [fm0]) :
    let m := fm0.ptr; let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := 0#64 }, freeMetas := [], reservedMetas := m :: st.reservedMetas }
    (st.ctx.freeMetaHead = m ∧ fm0.prev = m ∧ fm0.next = m) ∧ (m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas) ∧
    MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧ (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((m ↦ₛ fm0.toBytes) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal) ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  dsimp only; let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := 0#64 }, freeMetas := [], reservedMetas := fm0.ptr :: st.reservedMetas }
  have hDll := hwf.free_bump_metas_wf.1; rw [hFmEq, List.map_singleton] at hDll; obtain ⟨hHead, _, _, hLinks⟩ := hDll; have hL0 := hLinks 0 Nat.zero_lt_one; have hNext := hL0.1; have hPrev := hL0.2
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero] at hNext hPrev
  obtain ⟨⟨hNe0, hGe, hMod8, hFit⟩, hmNotRes, _, _, _, hEx⟩ := carvedMeta_byteMap_extract hwf (by rw [hFmEq]; exact List.mem_append_left _ (List.Mem.head _))
  obtain ⟨hWf', hGrpPost, hKeepRw, hPnEq⟩ := freeMeta_pop_wf_of_byteVal hwf hFmEq (newFms := []) (newHead := 0#64) (newVal := st.byteVal) rfl rfl (fun _ h => by cases h) (fun _ h => False.elim (h rfl))
  have hmBytes := hwf.free_bump_metas_wf.2.1 fm0 (by rw [hFmEq]; exact List.Mem.head _); have hMapEq : ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) st.byteVal = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal := SetSep_congr (fun a _ => hKeepRw a) (fun _ _ _ => rfl)
  exact ⟨⟨hHead, hPrev, hNext⟩, ⟨hNe0, hGe, hMod8, hFit, hmNotRes⟩, hWf', hGrpPost, by rw [hEx, hmBytes, hMapEq], hPnEq, rfl⟩

theorem fastPath1_pair_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {fm0 fm1 : FreeMetaDesc}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hFmEq : st.freeMetas = [fm0, fm1]) :
    let m := fm0.ptr; let fm1' : FreeMetaDesc := { ptr := fm1.ptr, prev := fm1.ptr, next := fm1.ptr }; let newVal := writeBytesToMap st.byteVal fm1.ptr fm1'.toBytes
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := [fm1'], reservedMetas := m :: st.reservedMetas, byteVal := newVal }
    let R_mid := ByteMap st.masterDom (fun a => (OwnedRwByte st a ∧ ¬ InRegion m 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal
    (st.ctx.freeMetaHead = m ∧ fm0.prev = fm1.ptr ∧ fm0.next = fm1.ptr ∧ m ≠ fm1.ptr) ∧ (m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas) ∧
    (fm1.ptr ≠ 0#64 ∧ fm1.ptr.toNat % 8 = 0 ∧ fm1.ptr.toNat + 40 ≤ 2 ^ 48) ∧ MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧
    (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((m ↦ₛ fm0.toBytes) ∗ ((fm1.ptr ↦ₛ fm1.toBytes) ∗ R_mid)) ∧ ((fm1.ptr ↦ₛ fm1'.toBytes) ∗ R_mid) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  dsimp only; let fm1' : FreeMetaDesc := { ptr := fm1.ptr, prev := fm1.ptr, next := fm1.ptr }; let newVal := writeBytesToMap st.byteVal fm1.ptr fm1'.toBytes
  let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := [fm1'], reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := newVal }
  have hDll := hwf.free_bump_metas_wf.1; simp only [hFmEq, List.map_cons, List.map_nil] at hDll; obtain ⟨hHead, hNd, hNonNull, hLinks⟩ := hDll
  have hNe01 : fm0.ptr ≠ fm1.ptr := fun h => (List.nodup_cons.mp hNd).1 (by simp [h]); have hNe1Zero : fm1.ptr ≠ 0#64 := hNonNull (fm1.ptr, fm1.prev, fm1.next) (List.Mem.tail _ (List.Mem.head _))
  have hL0 := hLinks 0 (Nat.zero_lt_succ 1); have hNext0 := hL0.1; have hPrev0 := hL0.2; simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ] at hNext0 hPrev0
  have hm0FB : fm0.ptr ∈ st.freeMetas.map (·.ptr) ++ st.bumpMetas := (by rw [hFmEq]; exact List.mem_append_left _ (List.Mem.head _)); have hm1FB : fm1.ptr ∈ st.freeMetas.map (·.ptr) ++ st.bumpMetas := (by rw [hFmEq]; exact List.mem_append_left _ (List.Mem.tail _ (List.Mem.head _)))
  obtain ⟨⟨hNe0, hGe0, hMod80, hFit0⟩, hmNotRes, _, _, _, hEx0⟩ := carvedMeta_byteMap_extract hwf hm0FB; obtain ⟨⟨_, _, hMod81, hFit1⟩, _, _, _, hDom1, _⟩ := carvedMeta_byteMap_extract hwf hm1FB
  have hDisj01 : ∀ a : BitVec 64, InRegion fm1.ptr 40 a → ¬ InRegion fm0.ptr 40 a := fun a ha1 ha0 => by
    have ⟨_, hAllDisj⟩ := mem_allMetaSlots_props hwf; have ⟨_, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
    have hm0All : fm0.ptr ∈ allMetaSlots st := (hUfIff _).mp (List.mem_append_left _ (by rw [List.append_assoc]; exact List.mem_append_right _ hm0FB))
    have hm1All : fm1.ptr ∈ allMetaSlots st := (hUfIff _).mp (List.mem_append_left _ (by rw [List.append_assoc]; exact List.mem_append_right _ hm1FB))
    have hD := hAllDisj fm0.ptr hm0All fm1.ptr hm1All hNe01; unfold DisjointRegions at hD; have h1 := (inRegion_toNat (by omega)).mp ha0; have h2 := (inRegion_toNat (by omega)).mp ha1; have hs1 := BitVec.toNat_sub fm1.ptr fm0.ptr; have hs2 := BitVec.toNat_sub fm0.ptr fm1.ptr; omega
  have hNewDll : CircularDllWf fm1.ptr ([fm1'].map fun fm => (fm.ptr, fm.prev, fm.next)) := by
    rw [List.map_singleton]; unfold CircularDllWf; exact ⟨rfl, List.Pairwise.cons nofun List.Pairwise.nil, fun x hx => by simp only [List.mem_singleton] at hx; exact hx ▸ hNe1Zero, fun i hi => by have hi0 : i = 0 := (by simp at hi; omega); subst hi0; simp [fm1']⟩
  obtain ⟨hWf', hGrpPost, hKeepRw, hPnEq⟩ := freeMeta_pop_wf_of_byteVal hwf hFmEq (newFms := [fm1']) (newHead := fm1.ptr) (newVal := newVal) rfl hNewDll
    (fun fm hfm => by simp only [List.mem_singleton] at hfm; rw [hfm]; simpa [newVal] using readBytesFromMap_writeBytesToMap st.byteVal fm1.ptr fm1'.toBytes (by simp))
    (fun a hne => ⟨fm1, List.Mem.head _, Classical.byContradiction fun hout => hne (by simpa [newVal] using writeBytesToMap_out st.byteVal fm1.ptr fm1'.toBytes hout)⟩)
  have hm0Bytes := hwf.free_bump_metas_wf.2.1 fm0 (by rw [hFmEq]; exact List.Mem.head _); have hm1Bytes := hwf.free_bump_metas_wf.2.1 fm1 (by rw [hFmEq]; exact List.Mem.tail _ (List.Mem.head _))
  have hEx1 := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) st.byteVal fm1.ptr (n := 40) (by omega) (fun a ha => (hDom1 a ha).2) (fun a ha => ⟨(hDom1 a ha).1, hDisj01 a ha⟩)
  have hAbs1 := ByteMap_absorb_slice hwf.masterDom_wf.1 (keep := fun a => (OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal fm1.ptr fm1'.toBytes (by simp) (fun a ha => (hDom1 a (by simpa using ha)).2) (fun a ha h => h.2 (by simpa using ha))
  refine ⟨⟨hHead, hPrev0, hNext0, hNe01⟩, ⟨hNe0, hGe0, hMod80, hFit0, hmNotRes⟩, ⟨hNe1Zero, hMod81, hFit1⟩, hWf', hGrpPost, by rw [hEx0, hm0Bytes, hEx1, hm1Bytes], ?_, hPnEq, rfl⟩
  rw [hAbs1]; exact SetSep_congr (fun a _ => ⟨fun h => (hKeepRw a).mp (h.elim And.left fun ha1 => ⟨(hDom1 a (by simpa using ha1)).1, hDisj01 a (by simpa using ha1)⟩), fun h => if ha1 : InRegion fm1.ptr 40 a then Or.inr (by simpa using ha1) else Or.inl ⟨(hKeepRw a).mpr h, ha1⟩⟩) (fun _ _ _ => rfl)

theorem fastPath1_ge3_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {fm0 fm1 fmLast : FreeMetaDesc} {mid : List FreeMetaDesc}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hFmEq : st.freeMetas = fm0 :: fm1 :: (mid ++ [fmLast])) :
    let m := fm0.ptr; let fm1' : FreeMetaDesc := { fm1 with prev := fmLast.ptr }; let fmLast' : FreeMetaDesc := { fmLast with next := fm1.ptr }
    let newFms := fm1' :: (mid ++ [fmLast']); let newVal := writeBytesToMap (writeBytesToMap st.byteVal fmLast.ptr fmLast'.toBytes) fm1.ptr fm1'.toBytes
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := newFms, reservedMetas := m :: st.reservedMetas, byteVal := newVal }
    let R_mid := ByteMap st.masterDom (fun a => ((OwnedRwByte st a ∧ ¬ InRegion m 40 a) ∧ ¬ InRegion fmLast.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal
    (st.ctx.freeMetaHead = m ∧ fm0.prev = fmLast.ptr ∧ fm0.next = fm1.ptr ∧ m ≠ fm1.ptr) ∧ (m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas) ∧
    (fm1.ptr ≠ 0#64 ∧ fm1.ptr.toNat % 8 = 0 ∧ fm1.ptr.toNat + 40 ≤ 2 ^ 48) ∧ (fmLast.ptr ≠ 0#64 ∧ fmLast.ptr.toNat % 8 = 0 ∧ fmLast.ptr.toNat + 40 ≤ 2 ^ 48) ∧ MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧
    (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((m ↦ₛ fm0.toBytes) ∗ ((fmLast.ptr ↦ₛ fmLast.toBytes) ∗ ((fm1.ptr ↦ₛ fm1.toBytes) ∗ R_mid))) ∧
    ((fm1.ptr ↦ₛ fm1'.toBytes) ∗ ((fmLast.ptr ↦ₛ fmLast'.toBytes) ∗ R_mid)) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  dsimp only; let f : FreeMetaDesc → BitVec 64 × BitVec 64 × BitVec 64 := fun fm => (fm.ptr, fm.prev, fm.next)
  let fm1' : FreeMetaDesc := { fm1 with prev := fmLast.ptr }; let fmLast' : FreeMetaDesc := { fmLast with next := fm1.ptr }; let newFms := fm1' :: (mid ++ [fmLast'])
  let v1 := writeBytesToMap st.byteVal fmLast.ptr fmLast'.toBytes; let newVal := writeBytesToMap v1 fm1.ptr fm1'.toBytes
  let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := newFms, reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := newVal }
  have hDll := hwf.free_bump_metas_wf.1; let xs0 := (fm0 :: fm1 :: (mid ++ [fmLast])).map f; let xs1 := newFms.map f
  have hLen0 : xs0.length = mid.length + 3 := (by simp [xs0]); have hLen1 : xs1.length = mid.length + 2 := (by simp [xs1, newFms])
  have hFstEq : xs1.map Prod.fst = fm1.ptr :: (mid.map (·.ptr) ++ [fmLast.ptr]) := (by simp [xs1, newFms, f, fm1', fmLast', List.map_append])
  have hFst0Eq : xs0.map Prod.fst = fm0.ptr :: fm1.ptr :: (mid.map (·.ptr) ++ [fmLast.ptr]) := (by simp [xs0, f, List.map_append])
  rw [hFmEq] at hDll; change CircularDllWf st.ctx.freeMetaHead (f fm0 :: (fm1 :: (mid ++ [fmLast])).map f) at hDll; unfold CircularDllWf at hDll; obtain ⟨hHead, hNd, hNonNull, hLinks⟩ := hDll
  have hLinks' : ∀ (i : Nat) (hi : i < xs0.length), (xs0[i]'hi).2.2 = (xs0[(i + 1) % xs0.length]'(Nat.mod_lt _ (by omega))).1 ∧ (xs0[i]'hi).2.1 = (xs0[(i + xs0.length - 1) % xs0.length]'(Nat.mod_lt _ (by omega))).1 := hLinks
  have hPtrNd : (fm0.ptr :: fm1.ptr :: (mid.map (·.ptr) ++ [fmLast.ptr])).Nodup := hFst0Eq ▸ (show (xs0.map Prod.fst).Nodup from hNd); have hTailNd := (List.nodup_cons.mp hPtrNd).2
  have hNe01 : fm0.ptr ≠ fm1.ptr := fun h => (List.nodup_cons.mp hPtrNd).1 (by simp [h]); have hNe0L : fm0.ptr ≠ fmLast.ptr := fun h => (List.nodup_cons.mp hPtrNd).1 (by simp [h]); have hNe1L : fm1.ptr ≠ fmLast.ptr := fun h => (List.nodup_cons.mp hTailNd).1 (by simp [h])
  have hMem0 : fm0 ∈ st.freeMetas := (by rw [hFmEq]; exact List.Mem.head _); have hMem1 : fm1 ∈ st.freeMetas := (by rw [hFmEq]; exact List.Mem.tail _ (List.Mem.head _)); have hMemL : fmLast ∈ st.freeMetas := (by rw [hFmEq]; simp)
  have hNe1Zero : fm1.ptr ≠ 0#64 := hNonNull (f fm1) (by simp [f]); have hNeLZero : fmLast.ptr ≠ 0#64 := hNonNull (f fmLast) (by simp [f, List.map_append])
  have ⟨hSlotProps, hAllDisj⟩ := mem_allMetaSlots_props hwf; have ⟨_, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hInAll : ∀ {x : FreeMetaDesc}, x ∈ st.freeMetas → x.ptr ∈ allMetaSlots st := fun hx => (hUfIff _).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx))))
  have hDisjPtr : ∀ {x y : FreeMetaDesc}, x ∈ st.freeMetas → y ∈ st.freeMetas → x.ptr ≠ y.ptr → ∀ a, InRegion x.ptr 40 a → ¬ InRegion y.ptr 40 a := fun {x y} hx hy hne a hax hay => by
    obtain ⟨_, _, _, hfx, _⟩ := hSlotProps _ (hInAll hx); obtain ⟨_, _, _, hfy, _⟩ := hSlotProps _ (hInAll hy); have hSep := nat_sep_of_disjointRegions (by decide) (by decide) hfx hfy (hAllDisj _ (hInAll hx) _ (hInAll hy) hne)
    have h1 := (inRegion_toNat (by omega)).mp hax; have h2 := (inRegion_toNat (by omega)).mp hay; omega
  have hFstShift : ∀ (k : Nat) (hk : k < xs1.length) (hk0 : k + 1 < xs0.length), (xs1[k]'hk).1 = (xs0[k + 1]'hk0).1 := fun k hk hk0 => by
    rw [(List.getElem_map _ : (xs1.map Prod.fst)[k]'(by simpa using hk) = (xs1[k]'hk).1).symm, (List.getElem_map _ : (xs0.map Prod.fst)[k + 1]'(by simpa using hk0) = (xs0[k + 1]'hk0).1).symm]; simp only [hFstEq, hFst0Eq, List.getElem_cons_succ]
  have hXs0Last : (xs0[mid.length + 2]'(by simp [xs0])) = f fmLast := (by simp [xs0, List.map_append, List.getElem_cons_succ, List.getElem_append_right])
  have hXs1Last : (xs1[mid.length + 1]'(by simp [xs1, newFms])) = f fmLast' := (by rw [getElem_congr_coll (show xs1 = f fm1' :: (mid.map f ++ [f fmLast']) by simp [xs1, newFms, List.map_append]), List.getElem_cons_succ, List.getElem_append_right (by simp)]; simp)
  have hL0 := hLinks' 0 (by omega); have hNext0 := hL0.1; have hPrev0 := hL0.2
  have hNext0Eq : fm0.next = fm1.ptr := (by rw [getElem_congr_idx (show (0 + 1) % xs0.length = 1 by rw [hLen0]; exact Nat.mod_eq_of_lt (by omega))] at hNext0; simpa [xs0, f] using hNext0)
  have hPrev0Eq : fm0.prev = fmLast.ptr := (by rw [getElem_congr_idx (show (0 + xs0.length - 1) % xs0.length = mid.length + 2 by rw [show 0 + xs0.length - 1 = mid.length + 2 by omega, hLen0]; exact Nat.mod_eq_of_lt (by omega)), hXs0Last] at hPrev0; simpa [xs0, f] using hPrev0)
  have hNewDll : CircularDllWf fm1.ptr xs1 := by
    unfold CircularDllWf; have hXs1Cons : xs1 = f fm1' :: (mid ++ [fmLast']).map f := rfl; rw [hXs1Cons]; refine ⟨rfl, by rw [← hXs1Cons, hFstEq]; exact hTailNd, fun x hx => ?_, fun i hi => ?_⟩
    · rw [← hXs1Cons] at hx; have hxPtr : x.1 ∈ xs1.map Prod.fst := List.mem_map_of_mem hx; rw [hFstEq] at hxPtr
      exact (List.mem_cons.mp hxPtr).elim (fun hx1 => hx1 ▸ hNe1Zero) fun hxRest => (List.mem_append.mp hxRest).elim
        (fun hxMid => by obtain ⟨fm, hfm, hxEq⟩ := List.mem_map.mp hxMid; exact hxEq ▸ hNonNull (f fm) (by simp [f, List.map_append, List.mem_map_of_mem hfm]))
        (fun hxL => by simp only [List.mem_singleton] at hxL; exact hxL ▸ hNeLZero)
    · have hi1 : i < xs1.length := hXs1Cons ▸ hi
      change (xs1[i]'hi1).2.2 = (xs1[(i + 1) % xs1.length]'(Nat.mod_lt _ (by omega))).1 ∧ (xs1[i]'hi1).2.1 = (xs1[(i + xs1.length - 1) % xs1.length]'(Nat.mod_lt _ (by omega))).1
      by_cases hi0 : i = 0
      · subst hi0; have hN1 := (hLinks' 1 (by omega)).1; rw [getElem_congr_idx (show (1 + 1) % xs0.length = 2 by rw [hLen0]; exact Nat.mod_eq_of_lt (by omega))] at hN1
        rw [getElem_congr_idx (show (0 + 1) % xs1.length = 1 by rw [hLen1]; exact Nat.mod_eq_of_lt (by omega)), getElem_congr_idx (show (0 + xs1.length - 1) % xs1.length = mid.length + 1 by rw [show 0 + xs1.length - 1 = mid.length + 1 by omega, hLen1]; exact Nat.mod_eq_of_lt (by omega)), hXs1Last]
        exact ⟨by simpa [xs1, newFms, f, fm1'] using (show fm1.next = (xs0[2]'(by omega)).1 by simpa [xs0, f] using hN1).trans (hFstShift 1 (by omega) (by omega)).symm, by simp [xs1, newFms, f, fm1', fmLast']⟩
      · by_cases hiLast : i = mid.length + 1
        · subst hiLast; have hPL := (hLinks' (mid.length + 2) (by omega)).2
          rw [hXs0Last, getElem_congr_idx (show (mid.length + 2 + xs0.length - 1) % xs0.length = mid.length + 1 by rw [show mid.length + 2 + xs0.length - 1 = (mid.length + 1) + xs0.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])] at hPL
          rw [hXs1Last, getElem_congr_idx (show (mid.length + 1 + 1) % xs1.length = 0 by rw [hLen1]; exact Nat.mod_self _), getElem_congr_idx (show (mid.length + 1 + xs1.length - 1) % xs1.length = mid.length by rw [show mid.length + 1 + xs1.length - 1 = mid.length + xs1.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])]
          exact ⟨by simp [xs1, newFms, f, fm1', fmLast'], hPL.trans (hFstShift mid.length (by omega) (by omega)).symm⟩
        · let j := i - 1; have hj : j < mid.length := (by omega); have hiEq : i = j + 1 := (by omega)
          have hEl1 : (xs1[i]'hi1) = (mid.map f)[j]'(by simpa using hj) := (by rw [getElem_congr_idx hiEq]; simp [xs1, newFms, List.map_append, List.getElem_cons_succ, List.getElem_append_left, hj])
          have hEl0 : (xs0[j + 2]'(by omega)) = (mid.map f)[j]'(by simpa using hj) := (by simp [xs0, List.map_append, List.getElem_cons_succ, List.getElem_append_left, hj])
          have hLPj := hLinks' (j + 2) (by omega); have hNj := hLPj.1; have hPj := hLPj.2
          rw [hEl0, getElem_congr_idx (show (j + 2 + 1) % xs0.length = j + 3 by rw [hLen0]; exact Nat.mod_eq_of_lt (by omega))] at hNj
          rw [hEl0, getElem_congr_idx (show (j + 2 + xs0.length - 1) % xs0.length = j + 1 by rw [show j + 2 + xs0.length - 1 = (j + 1) + xs0.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])] at hPj
          rw [hEl1, getElem_congr_idx (show (i + 1) % xs1.length = j + 2 by rw [hiEq, hLen1]; exact Nat.mod_eq_of_lt (by omega)), getElem_congr_idx (show (i + xs1.length - 1) % xs1.length = j by rw [show i + xs1.length - 1 = j + xs1.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])]
          exact ⟨hNj.trans (hFstShift (j + 2) (by omega) (by omega)).symm, hPj.trans (hFstShift j (by omega) (by omega)).symm⟩
  have hNewBytes : ∀ fm ∈ newFms, readBytesFromMap newVal fm.ptr 40 = fm.toBytes := fun fm hfm => by
    rcases List.mem_cons.mp (show fm ∈ fm1' :: (mid ++ [fmLast']) from hfm) with rfl | hRest
    · simpa [newVal, fm1'] using readBytesFromMap_writeBytesToMap v1 fm1.ptr fm1'.toBytes (by simp)
    · rcases List.mem_append.mp hRest with hMid | hLast
      · have hMemMid : fm ∈ st.freeMetas := (by rw [hFmEq]; simp [hMid]); have hNeM1 : fm.ptr ≠ fm1.ptr := fun h => (List.nodup_cons.mp hTailNd).1 (List.mem_append_left _ (h ▸ List.mem_map_of_mem hMid))
        have hNeML : fm.ptr ≠ fmLast.ptr := fun h => (List.nodup_append.mp (List.nodup_cons.mp hTailNd).2).2.2 fm.ptr (List.mem_map_of_mem hMid) fmLast.ptr (List.Mem.head _) h
        rw [← hwf.free_bump_metas_wf.2.1 fm hMemMid]; exact readBytesFromMap_congr (by omega) fun a ha => (writeBytesToMap_out v1 fm1.ptr fm1'.toBytes (by simpa using hDisjPtr hMemMid hMem1 hNeM1 a ha)).trans (writeBytesToMap_out st.byteVal fmLast.ptr fmLast'.toBytes (by simpa using hDisjPtr hMemMid hMemL hNeML a ha))
      · simp only [List.mem_singleton] at hLast; rw [hLast]; have hCongr : readBytesFromMap newVal fmLast.ptr 40 = readBytesFromMap v1 fmLast.ptr 40 := readBytesFromMap_congr (by omega) fun a ha => writeBytesToMap_out v1 fm1.ptr fm1'.toBytes (by simpa using hDisjPtr hMemL hMem1 hNe1L.symm a ha)
        simpa [fmLast', v1, hCongr] using readBytesFromMap_writeBytesToMap st.byteVal fmLast.ptr fmLast'.toBytes (by simp)
  have hValSupport : ∀ a : BitVec 64, newVal a ≠ st.byteVal a → ∃ fm ∈ fm1 :: (mid ++ [fmLast]), InRegion fm.ptr 40 a := fun a hne =>
    if ha1 : InRegion fm1.ptr 40 a then ⟨fm1, List.Mem.head _, ha1⟩ else if haL : InRegion fmLast.ptr 40 a then ⟨fmLast, List.Mem.tail _ (List.mem_append_right _ (List.Mem.head _)), haL⟩
    else False.elim (hne ((writeBytesToMap_out v1 fm1.ptr fm1'.toBytes (by simpa using ha1)).trans (writeBytesToMap_out st.byteVal fmLast.ptr fmLast'.toBytes (by simpa using haL))))
  obtain ⟨hWf', hGrpPost, hKeepRw, hPnEq⟩ := freeMeta_pop_wf_of_byteVal hwf hFmEq (newFms := newFms) (newHead := fm1.ptr) (newVal := newVal) (by simp [newFms, fm1', fmLast', List.map_append]) hNewDll hNewBytes hValSupport
  obtain ⟨⟨hNe0, hGe0, hMod80, hFit0⟩, hmNotRes, _, _, _, hEx0⟩ := carvedMeta_byteMap_extract hwf (List.mem_append_left _ (List.mem_map_of_mem hMem0))
  obtain ⟨⟨_, _, hMod81, hFit1⟩, _, _, _, hDom1, _⟩ := carvedMeta_byteMap_extract hwf (List.mem_append_left _ (List.mem_map_of_mem hMem1)); obtain ⟨⟨_, _, hMod8L, hFitL⟩, _, _, _, hDomL, _⟩ := carvedMeta_byteMap_extract hwf (List.mem_append_left _ (List.mem_map_of_mem hMemL))
  have hm0B := hwf.free_bump_metas_wf.2.1 fm0 hMem0; have hm1B := hwf.free_bump_metas_wf.2.1 fm1 hMem1; have hmLB := hwf.free_bump_metas_wf.2.1 fmLast hMemL
  have hExL := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) st.byteVal fmLast.ptr (n := 40) (by omega) (fun a ha => (hDomL a ha).2) (fun a ha => ⟨(hDomL a ha).1, hDisjPtr hMemL hMem0 hNe0L.symm a ha⟩)
  have hEx1 := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := fun a => (OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fmLast.ptr 40 a) st.byteVal fm1.ptr (n := 40) (by omega) (fun a ha => (hDom1 a ha).2) (fun a ha => ⟨⟨(hDom1 a ha).1, hDisjPtr hMem1 hMem0 hNe01.symm a ha⟩, hDisjPtr hMem1 hMemL hNe1L a ha⟩)
  have hAbsL := ByteMap_absorb_slice hwf.masterDom_wf.1 (keep := fun a => ((OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fmLast.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal fmLast.ptr fmLast'.toBytes (by simp) (fun a ha => (hDomL a (by simpa using ha)).2) (fun a ha h => h.1.2 (by simpa using ha))
  have hAbs1 := ByteMap_absorb_slice hwf.masterDom_wf.1 (keep := fun a => (((OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fmLast.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) ∨ InRegion fmLast.ptr fmLast'.toBytes.length a) v1 fm1.ptr fm1'.toBytes (by simp) (fun a ha => (hDom1 a (by simpa using ha)).2)
    (fun a ha h => by have ha1 : InRegion fm1.ptr 40 a := (by simpa using ha); exact h.elim (fun h1 => h1.2 ha1) (fun haL => hDisjPtr hMem1 hMemL hNe1L a ha1 (by simpa using haL)))
  refine ⟨⟨hHead, hPrev0Eq, hNext0Eq, hNe01⟩, ⟨hNe0, hGe0, hMod80, hFit0, hmNotRes⟩, ⟨hNe1Zero, hMod81, hFit1⟩, ⟨hNeLZero, hMod8L, hFitL⟩, hWf', hGrpPost, by rw [hEx0, hm0B, hExL, hmLB, hEx1, hm1B], ?_, hPnEq, rfl⟩
  rw [hAbsL, hAbs1]; exact SetSep_congr (fun a _ => ⟨fun h => (hKeepRw a).mp (h.elim (fun h0L => h0L.elim (fun h0 => h0.1.1) fun haL => ⟨(hDomL a (by simpa using haL)).1, hDisjPtr hMemL hMem0 hNe0L.symm a (by simpa using haL)⟩) fun ha1 => ⟨(hDom1 a (by simpa using ha1)).1, hDisjPtr hMem1 hMem0 hNe01.symm a (by simpa using ha1)⟩),
    fun h => if ha1 : InRegion fm1.ptr 40 a then Or.inr (by simpa using ha1) else if haL : InRegion fmLast.ptr 40 a then Or.inl (Or.inr (by simpa using haL)) else Or.inl (Or.inl ⟨⟨(hKeepRw a).mpr h, haL⟩, ha1⟩)⟩) (fun _ _ _ => rfl)

theorem lazyInit_brkFail_wf {inflight : Nat} {base brkStart brk sec : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (h0 : st.ctx.initDone = 0#32) :
    let st' : MallocngSt := { st with ctx := { emptyCtxFields with secret := sec, initDone := 1#32, brk := -1#64, seq := st.ctx.seq } }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st' ∧ st'.freeMetas = [] ∧ st'.bumpMetas = [] ∧ st'.availMetaPages = [] ∧ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal = ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  obtain ⟨hCtx, hMa, hMma, hGp, hMgp, hAv, hFm, hBm, hRm, hGs, _, hBrkEq⟩ := hwf.initZero_wf h0
  have hUsageEq : st.ctx.usageByClass = emptyCtxFields.usageByClass := by rw [hCtx]
  have hActEq : st.ctx.active = emptyCtxFields.active := by rw [hCtx]
  exact ⟨{ base_wf := hwf.base_wf, brk_bounds := hwf.brk_bounds, ctx_lens := ⟨rfl, rfl, rfl, rfl, rfl, hwf.ctx_lens.2.2.2.2.2⟩, initDone_wf := Or.inr rfl, initZero_wf := fun h => by cases h
           bounces_wf := fun b hb => by simp [emptyCtxFields] at hb; subst hb; decide
           usage_wf := fun sc hsc => by simpa only [hUsageEq] using hwf.usage_wf sc (by rw [hUsageEq]; exact hsc), brk_mode_wf := ⟨fun ⟨_, hne⟩ => False.elim (hne rfl), by simp [hMma, hMa], by simp [hMgp, hGp], fun _ => by subst hBrkEq; omega⟩
           metaAreas_wf := by simp [hMa, emptyCtxFields]
           guard_avail_wf := ⟨by simp [hGp], fun _ h => by simp [hGp] at h, by simp [hAv, emptyCtxFields], fun _ h => by simp [hAv] at h⟩, inflight_wf := hwf.inflight_wf
           free_bump_metas_wf := ⟨by simp [hFm, emptyCtxFields, CircularDllWf], fun _ h => by simp [hFm] at h, Or.inl ⟨rfl, hBm⟩, fun _ h => by simp [hBm] at h, by simp [hGs, hFm, hBm, hRm], fun m => by simp [hGs, hFm, hBm, hRm, allMetaSlots, hMa]⟩
           groups_nodup := hwf.groups_nodup, groups_wf := hwf.groups_wf, regions_disjoint := hwf.regions_disjoint
           active_wf := fun sc h1 h2 => by have hAct := hwf.active_wf sc (by rw [hActEq]; exact h1) h2; unfold ActiveClassWf at hAct ⊢; simpa only [findGroupByMeta, hActEq] using hAct
           liveMap_wf := hwf.liveMap_wf, live_le_peak := hwf.live_le_peak, effCost_le_live := hwf.effCost_le_live
           meta_pages_bound := ⟨by simp [hMa], fun _ => ⟨hAv, by simp [hGp]⟩, fun m hm hEq => by simp [emptyCtxFields] at hEq; omega⟩, empty_groups_bound := hwf.empty_groups_bound, masterDom_wf := hwf.masterDom_wf }, hFm, hBm, hAv, rfl, rfl, rfl⟩

theorem brk_fail_wf {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (h1 : st.ctx.initDone = 1#32) :
    let st' : MallocngSt := { st with ctx := { st.ctx with brk := -1#64 } }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st' ∧ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal = ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) :=
  ⟨{ base_wf := hwf.base_wf, brk_bounds := hwf.brk_bounds, ctx_lens := hwf.ctx_lens, initDone_wf := Or.inr h1, initZero_wf := fun h0 => by rw [h1] at h0; cases h0
     bounces_wf := hwf.bounces_wf, usage_wf := hwf.usage_wf, brk_mode_wf := ⟨fun ⟨_, hne⟩ => False.elim (hne rfl), hwf.brk_mode_wf.2.1, hwf.brk_mode_wf.2.2.1, hwf.brk_mode_wf.2.2.2⟩
     metaAreas_wf := hwf.metaAreas_wf, guard_avail_wf := hwf.guard_avail_wf, inflight_wf := hwf.inflight_wf, free_bump_metas_wf := hwf.free_bump_metas_wf, groups_nodup := hwf.groups_nodup, groups_wf := hwf.groups_wf
     regions_disjoint := hwf.regions_disjoint, active_wf := hwf.active_wf, liveMap_wf := hwf.liveMap_wf, live_le_peak := hwf.live_le_peak, effCost_le_live := hwf.effCost_le_live, meta_pages_bound := hwf.meta_pages_bound, empty_groups_bound := hwf.empty_groups_bound, masterDom_wf := hwf.masterDom_wf }, rfl, rfl, rfl⟩

end VerifiedLibraries.Mallocng.Proofs
