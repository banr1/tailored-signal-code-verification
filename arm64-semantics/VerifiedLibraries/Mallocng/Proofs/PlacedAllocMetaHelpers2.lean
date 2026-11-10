/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaHelpers1

/-!
# Placed `__malloc_alloc_meta` Slow-Path Transitions

Proves `MallocngWFInflight` and `ByteMap` transitions for activating fresh `meta_area` pages
across the four `__malloc_alloc_meta` slow paths (`slowPathA_trans`, `slowPathB1_trans`,
`slowPathB2_trans`, `slowPathC_trans`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

def appendMetaArea : List MetaAreaDesc → BitVec 64 → List MetaAreaDesc
  | [], ap => [{ base := ap, next := 0#64 }]
  | [tail], ap => [{ tail with next := ap }, { base := ap, next := 0#64 }]
  | ma :: hd2 :: tl, ap => ma :: appendMetaArea (hd2 :: tl) ap

theorem appendMetaArea_props (mas : List MetaAreaDesc) (ap : BitVec 64) :
    (appendMetaArea mas ap).map (·.base) = mas.map (·.base) ++ [ap] ∧
    (appendMetaArea mas ap).length = mas.length + 1 ∧
    ∃ hne : appendMetaArea mas ap ≠ [], (appendMetaArea mas ap).getLast hne = { base := ap, next := 0#64 } := by
  induction mas with
  | nil => exact ⟨rfl, rfl, nofun, rfl⟩
  | cons ma tl ih => cases tl with
    | nil => exact ⟨rfl, rfl, nofun, rfl⟩
    | cons hd2 tl2 =>
      obtain ⟨hMap, hLen, hne, hLast⟩ := ih
      exact ⟨by simp [appendMetaArea, hMap], by simp [appendMetaArea, hLen], nofun,
        by simp only [appendMetaArea]; rw [List.getLast_cons hne]; exact hLast⟩

private theorem appendMetaArea_chain (mas : List MetaAreaDesc) (ap : BitVec 64) (hNd : (mas.map (·.base)).Nodup)
    (hTail0 : ∀ hne : mas ≠ [], (mas.getLast hne).next = 0#64)
    (hLinks : ∀ i : Nat, (hi : i + 1 < mas.length) → (mas[i]'(Nat.lt_of_succ_lt hi)).next = (mas[i + 1]'hi).base) :
    (match mas, _hEq : appendMetaArea mas ap with
      | [], hd' :: _ => hd'.base = ap
      | hd :: _, hd' :: _ => hd'.base = hd.base
      | _, [] => False) ∧
    (∀ i : Nat, (hi : i + 1 < (appendMetaArea mas ap).length) →
      ((appendMetaArea mas ap)[i]'(Nat.lt_of_succ_lt hi)).next = ((appendMetaArea mas ap)[i + 1]'hi).base) ∧
    ∀ ma' ∈ appendMetaArea mas ap,
      ma' = { base := ap, next := 0#64 } ∨
      (∃ hne : mas ≠ [], ma' = { mas.getLast hne with next := ap }) ∨
      (ma' ∈ mas ∧ ∀ hne : mas ≠ [], ma'.base ≠ (mas.getLast hne).base) := by
  induction mas with
  | nil =>
    exact ⟨rfl, fun i hi => by simp [appendMetaArea] at hi, fun ma' hm => by simp [appendMetaArea] at hm; exact Or.inl hm⟩
  | cons ma tl ih => cases tl with
    | nil =>
      refine ⟨rfl, fun i hi => by cases i with | zero => rfl | succ _ => simp [appendMetaArea] at hi; omega,
        fun ma' hm => by simp [appendMetaArea] at hm; exact hm.elim (fun h => Or.inr (Or.inl ⟨nofun, h⟩)) Or.inl⟩
    | cons hd2 tl2 =>
      have ⟨hmaNot, hSubNd⟩ := List.nodup_cons.mp hNd
      obtain ⟨hHd, hCh, hMem⟩ := ih hSubNd (fun _ => hTail0 nofun) (fun i hi => hLinks (i + 1) (by simpa using Nat.succ_lt_succ hi))
      refine ⟨rfl, fun i hi => ?_, fun ma' hm => ?_⟩
      · cases i with
        | zero =>
          have h0 := hLinks 0 (by simp)
          cases hSubEq : appendMetaArea (hd2 :: tl2) ap with
          | nil => exact False.elim (by rw [hSubEq] at hHd; exact hHd)
          | cons _ _ => rw [hSubEq] at hHd; simpa [appendMetaArea, hSubEq, hHd] using h0
        | succ j => exact hCh j (by simpa [appendMetaArea] using hi)
      · rcases List.mem_cons.mp hm with rfl | hTail
        · exact Or.inr (Or.inr ⟨List.Mem.head _, fun _ hEq => hmaNot (by dsimp only at hEq ⊢; rw [hEq]; exact List.mem_map_of_mem (List.getLast_mem (l := hd2 :: tl2) nofun))⟩)
        · exact (hMem ma' hTail).elim Or.inl fun h => h.elim (fun ⟨_, h2⟩ => Or.inr (Or.inl ⟨nofun, h2⟩)) (fun ⟨h3, hNeB⟩ => Or.inr (Or.inr ⟨List.Mem.tail _ h3, fun _ => hNeB nofun⟩))

def metaHdrBytes (sec next : BitVec 64) : List (BitVec 8) :=
  unpack64 sec ++ unpack64 next ++ unpack32 101#32 ++ unpack32 0#32

@[simp] theorem metaHdrBytes_length (sec next : BitVec 64) : (metaHdrBytes sec next).length = 24 := rfl

theorem activate_metaArea_wf {inflight : Nat} {base brkStart brk brk' ap : BitVec 64} {liveCost peakCost : Nat} {st st' : MallocngSt} {bv0 : BitVec 64 → BitVec 8}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hApB : 4096 ≤ ap.toNat ∧ ap.toNat % 4096 = 0 ∧ ap.toNat + 4096 ≤ 2 ^ 48) (hApDisj : ap ∉ st.metaAreas.map (·.base) ∧ ∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions ap 4096 g.mem (g.maplen * 4096))
    (hBv0Ma : ∀ ma ∈ st.metaAreas, ∀ a : BitVec 64, InRegion ma.base 4096 a → bv0 a = st.byteVal a) (hBv0Rg : ∀ g ∈ st.groups, 0 < g.maplen → ∀ a : BitVec 64, InRegion g.mem (g.maplen * 4096) a → bv0 a = st.byteVal a)
    (hBv0Zero : ∀ a : BitVec 64, InRegion (ap + 64#64) 4032 a → bv0 a = 0#8)
    (hBv' : st'.byteVal = writeBytesToMap (if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0) ap (metaHdrBytes st'.ctx.secret 0#64))
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas ap) (hFm' : st'.freeMetas = []) (hBm' : st'.bumpMetas = (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)))
    (hRm' : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas) (hGs' : st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧ st'.liveMap = st.liveMap)
    (hCtx' : st'.ctx.initDone = 1#32 ∧ st'.ctx.freeMetaHead = 0#64 ∧ st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧ st'.ctx.metaAreaHead = (match st.metaAreas with | [] => ap | hd :: _ => hd.base) ∧
      st'.ctx.metaAreaTail = ap ∧ (st.metaAreas ≠ [] → st'.ctx.secret = st.ctx.secret) ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧ st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq ∧ st'.ctx.seqPad = st.ctx.seqPad)
    (hBrkB' : 65536 ≤ brkStart.toNat ∧ brkStart.toNat % 4096 = 0 ∧ brk'.toNat % 4096 = 0 ∧ brkStart.toNat ≤ brk'.toNat ∧ brk'.toNat ≤ 2 ^ 48)
    (hBrkMode' : (st'.ctx.initDone = 1#32 ∧ st'.ctx.brk ≠ (-1#64) → st'.ctx.brk = brk' ∧ brkStart.toNat + 8192 ≤ brk'.toNat ∧ st'.ctx.availMetaAreaCount = 0#64 ∧ st'.ctx.metaAllocShift = 0#64 ∧ st'.availMetaPages = []) ∧
      st'.mmapMetaAreas = (st'.metaAreas.map (·.base)).filter (fun mb => !decide (InRegion brkStart (brk'.toNat - brkStart.toNat) mb)) ∧ st'.mmapGuardPages = st'.guardPages.filter (fun gp => !decide (InRegion brkStart (brk'.toNat - brkStart.toNat) gp)) ∧
      (brkStart.toNat < brk'.toNat → brkStart ∈ st'.guardPages ∧ ∀ k : Nat, 1 ≤ k → k < (brk'.toNat - brkStart.toNat) / 4096 → ∃ ma ∈ st'.metaAreas, ma.base = brkStart + BitVec.ofNat 64 (4096 * k)))
    (hGuardAvail' : st'.guardPages.Nodup ∧ (∀ gp ∈ st'.guardPages, 4096 ≤ gp.toNat ∧ gp.toNat % 4096 = 0 ∧ gp.toNat + 4096 ≤ 2 ^ 48) ∧
      st'.availMetaPages = (List.range st'.ctx.availMetaAreaCount.toNat).map (fun i => st'.ctx.availMetaAreas + BitVec.ofNat 64 (4096 * i)) ∧ (∀ ap' ∈ st'.availMetaPages, 4096 ≤ ap'.toNat ∧ ap'.toNat % 4096 = 0 ∧ ap'.toNat + 4096 ≤ 2 ^ 48 ∧ readBytesFromMap st'.byteVal ap' 4096 = List.replicate 4096 0#8))
    (hPd' : PairwiseDisjointRegions (dynamicRootRegions st'))
    (hShiftB' : (st'.ctx.metaAllocShift = 0#64 → st'.availMetaPages = [] ∧ st'.guardPages.length ≤ 1) ∧ ∀ m : Nat, 1 ≤ m → st'.ctx.metaAllocShift.toNat = m → m ≤ 40 ∧ 2 ^ m - m ≤ st'.metaAreas.length ∧ 2 ^ (m + 1) - 2 - m ≤ st'.metaAreas.length + st'.availMetaPages.length ∧ st'.guardPages.length ≤ m + 1 ∧ st'.availMetaPages.length ≤ 2 ^ m - 2)
    (hDomWf' : st'.masterDom.Nodup ∧ (∀ a : BitVec 64, (OwnedRwByte st' a ∨ OwnedProtNoneByte st' a ∨ OwnedMappedByte st' a) → a ∈ st'.masterDom) ∧ ∀ a ∈ st'.masterDom, ∃ r ∈ dynamicRootRegions st', InRegion r.1 r.2 a) :
    let m := ap + 24#64
    (m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas) ∧ MallocngWFInflight (inflight + 1) base brkStart brk' liveCost peakCost st' ∧
    (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) := by
  dsimp only; let newMa : MetaAreaDesc := { base := ap, next := 0#64 }
  let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0
  have hMNat : (ap + 24#64).toNat = ap.toNat + 24 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hAp64Nat : (ap + 64#64).toNat = ap.toNat + 64 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hPageSep : ∀ ma ∈ st.metaAreas, ma.base.toNat + 4096 ≤ ap.toNat ∨ ap.toNat + 4096 ≤ ma.base.toNat := fun ma hma => by have hb := hwf.metaAreas_wf.2.1 ma hma; have hne : ma.base.toNat ≠ ap.toNat := fun h => hApDisj.1 (BitVec.eq_of_toNat_eq h ▸ List.mem_map_of_mem hma); omega
  have ⟨hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2
  have hNewNotAll : ∀ k < 101, newMa.slotAddr k ∉ allMetaSlots st := fun k hk hm => by
    unfold allMetaSlots at hm; obtain ⟨ma, hma, hmS⟩ := List.mem_flatMap.mp hm; obtain ⟨k2, hk2R, hEq⟩ := List.mem_map.mp hmS; have hk2 := List.mem_range.mp hk2R; have hb := hwf.metaAreas_wf.2.1 ma hma; have hSep := hPageSep ma hma
    have h1 : (ma.slotAddr k2).toNat = ma.base.toNat + 24 + 40 * k2 := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    have h2 : (newMa.slotAddr k).toNat = ap.toNat + 24 + 40 * k := (by unfold MetaAreaDesc.slotAddr; dsimp only [newMa]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have := congrArg BitVec.toNat hEq; omega
  have hmNotRes : ap + 24#64 ∉ st.reservedMetas := fun hr => hNewNotAll 0 (by decide) ((hUfIff _).mp (List.mem_append_right _ hr))
  obtain ⟨hMapBase, hMaLen, hMaNe, hMaLast⟩ := appendMetaArea_props st.metaAreas ap
  have hTail0 : ∀ hne : st.metaAreas ≠ [], (st.metaAreas.getLast hne).next = 0#64 := by have h2 := hwf.metaAreas_wf.2.2; cases hEq : st.metaAreas with | nil => intro hne; exact False.elim (hne rfl) | cons _ _ => rw [hEq] at h2; intro hne; exact (h2.2.1 hne).2
  have hLinks0 : ∀ i : Nat, (hi : i + 1 < st.metaAreas.length) → (st.metaAreas[i]'(Nat.lt_of_succ_lt hi)).next = (st.metaAreas[i + 1]'hi).base := by have h2 := hwf.metaAreas_wf.2.2; cases hEq : st.metaAreas with | nil => intro _ hi; simp at hi | cons _ _ => rw [hEq] at h2; exact h2.2.2
  obtain ⟨hChHd, hChLinks, hChMem⟩ := appendMetaArea_chain st.metaAreas ap hwf.metaAreas_wf.1 hTail0 hLinks0
  have hBv1Ma : ∀ ma ∈ st.metaAreas, (∀ hne : st.metaAreas ≠ [], ma.base ≠ (st.metaAreas.getLast hne).base) → ∀ a : BitVec 64, InRegion ma.base 24 a → bv1 a = st.byteVal a := fun ma hma hNeT a ha => by
    have hb := hwf.metaAreas_wf.2.1 ma hma; have haN := (inRegion_toNat (by omega)).mp ha; have ha4096 : InRegion ma.base 4096 a := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩
    dsimp only [bv1]; split
    · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); have hNeNat : ma.base.toNat ≠ (st.metaAreas.getLast hne).base.toNat := fun h => hNeT hne (BitVec.eq_of_toNat_eq h)
      rw [writeBytesToMap_out _ _ _ (fun hIn => by rw [metaHdrBytes_length] at hIn; have h2 := (inRegion_toNat (by omega)).mp hIn; omega), hBv0Ma ma hma a ha4096]
    · exact hBv0Ma ma hma a ha4096
  have hBvGrp : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ (0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) → st'.byteVal a = st.byteVal a := fun g hg a hIn => by
    rw [hBv']; rcases hIn with haMeta | ⟨hMl, haMem⟩
    · have hgAll : g.metaPtr ∈ allMetaSlots st := (hUfIff _).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
      unfold allMetaSlots at hgAll; obtain ⟨ma, hma, hmS⟩ := List.mem_flatMap.mp hgAll; obtain ⟨k, hkR, hEq⟩ := List.mem_map.mp hmS
      have hkLt := List.mem_range.mp hkR; have hb := hwf.metaAreas_wf.2.1 ma hma; have hSep := hPageSep ma hma; have hSNat : g.metaPtr.toNat = ma.base.toNat + 24 + 40 * k := (by rw [← hEq]; unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      have haN := (inRegion_toNat (by omega)).mp haMeta; rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have h2 := (inRegion_toNat (by omega)).mp h; omega)]; split
      · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have h2 := (inRegion_toNat (by omega)).mp h; by_cases hS : ma.base.toNat = (st.metaAreas.getLast hne).base.toNat <;> omega), hBv0Ma ma hma a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)]
      · exact hBv0Ma ma hma a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)
    · obtain ⟨_, _, _, _, _, _, hgTotFit, _⟩ := hwf.groups_wf g hg; have hgTot : g.totalBytes = g.maplen * 4096 := (by simp [GroupDesc.totalBytes, hMl])
      have haN := (inRegion_toNat (by omega)).mp haMem; have hSepAp := nat_sep_of_disjointRegions (by decide) (by omega) hApB.2.2 (hgTot ▸ hgTotFit) (hApDisj.2 g hg hMl)
      rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have h2 := (inRegion_toNat (by omega)).mp h; omega)]; split
      · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff] at hpd
        have hDT := hpd.2.2 ((st.metaAreas.getLast hne).base, 4096) (List.mem_map_of_mem (List.getLast_mem hne)) (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hMl⟩))))
        dsimp only at hDT; have hSepT := nat_sep_of_disjointRegions (by decide) (by omega) htb.2.2.1 (hgTot ▸ hgTotFit) hDT
        rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have h2 := (inRegion_toNat (by omega)).mp h; omega), hBv0Rg g hg hMl a haMem]
      · exact hBv0Rg g hg hMl a haMem
  have hGA := groups_active_wf_congr (st' := st') hwf hGs'.1 hGs'.2.1 hCtx'.2.2.2.2.2.2.2.1 hBvGrp (hOv := by rw [hGs'.2.2])
  have hBvAp64 : ∀ a : BitVec 64, InRegion (ap + 64#64) 4032 a → st'.byteVal a = 0#8 := fun a ha => by
    have haN := (inRegion_toNat (by omega)).mp ha; rw [hBv', writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have h2 := (inRegion_toNat (by omega)).mp h; omega)]; split
    · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); have hSep := hPageSep _ (List.getLast_mem hne); rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have h2 := (inRegion_toNat (by omega)).mp h; omega), hBv0Zero a ha]
    · exact hBv0Zero a ha
  have hNewSlotsNd : ((List.range 101).map newMa.slotAddr).Nodup := by
    have hAux : ∀ (n k0 : Nat), k0 + n ≤ 101 → ((List.range n).map (fun j => newMa.slotAddr (k0 + j))).Nodup := fun n => by
      induction n with
      | zero => intro _ _; exact List.nodup_nil
      | succ n ih =>
        intro k0 hk; rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.nodup_cons]
        refine ⟨fun hMem => ?_, by simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm 1] using ih (k0 + 1) (by omega)⟩
        obtain ⟨j, hjR, hEq⟩ := List.mem_map.mp hMem; have hj := List.mem_range.mp hjR
        have h1 : (newMa.slotAddr (k0 + Nat.succ j)).toNat = ap.toNat + 24 + 40 * (k0 + j + 1) := (by unfold MetaAreaDesc.slotAddr; dsimp only [newMa]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        have h2 : (newMa.slotAddr (k0 + 0)).toNat = ap.toNat + 24 + 40 * k0 := (by unfold MetaAreaDesc.slotAddr; dsimp only [newMa]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        have hc := congrArg BitVec.toNat hEq; dsimp only [Function.comp] at hc; rw [h1, h2] at hc; omega
    simpa using hAux 101 0 (by decide)
  have hNewSlotsEq : (List.range 101).map newMa.slotAddr = (ap + 24#64) :: st'.bumpMetas := by rw [show (101 : Nat) = 100 + 1 from rfl, List.range_succ_eq_map, List.map_cons, List.map_map, hBm']; congr 1
  have hAllEq : allMetaSlots st' = allMetaSlots st ++ ((ap + 24#64) :: st'.bumpMetas) := by
    rw [← hNewSlotsEq]; unfold allMetaSlots; have hF : ∀ mas : List MetaAreaDesc, mas.flatMap (fun ma => (List.range 101).map ma.slotAddr) = (mas.map (·.base)).flatMap (fun b => (List.range 101).map (fun k => b + BitVec.ofNat 64 (24 + 40 * k))) := fun mas => by rw [List.flatMap_map]; rfl
    rw [hF, hF, hMa', hMapBase, List.flatMap_append, List.flatMap_singleton]; rfl
  have hGetLastEq : ∀ {α : Type} {xs ys : List α} (h : xs = ys) (hx : xs ≠ []) (hy : ys ≠ []), xs.getLast hx = ys.getLast hy := by rintro _ _ _ rfl _ _; rfl
  have hWf' : MallocngWFInflight (inflight + 1) base brkStart brk' liveCost peakCost st' := {
    base_wf := trivial
    brk_bounds := hBrkB'
    initDone_wf := Or.inr hCtx'.1
    initZero_wf := fun h0 => by rw [hCtx'.1] at h0; cases h0
    ctx_lens := by rw [hCtx'.2.2.2.2.2.2.2.1, hCtx'.2.2.2.2.2.2.2.2.1, hCtx'.2.2.2.2.2.2.2.2.2.1, hCtx'.2.2.2.2.2.2.2.2.2.2.1, hCtx'.2.2.2.2.2.2.2.2.2.2.2.2, hGs'.2.1]; exact hwf.ctx_lens
    bounces_wf := fun b hb => hwf.bounces_wf b (hCtx'.2.2.2.2.2.2.2.2.2.2.1 ▸ hb)
    usage_wf := fun sc hsc => by have hU := hCtx'.2.2.2.2.2.2.2.2.1; simp only [hU, hGs'.1] at hsc ⊢; exact hwf.usage_wf sc hsc
    brk_mode_wf := hBrkMode'
    metaAreas_wf := by
      refine ⟨by rw [hMa', hMapBase, List.nodup_append]; exact ⟨hwf.metaAreas_wf.1, List.Pairwise.cons nofun List.Pairwise.nil, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hApDisj.1 hx⟩, fun ma hma => ?_, ?_⟩
      · rw [hMa'] at hma; rcases hChMem ma hma with rfl | ⟨hne, rfl⟩ | ⟨hma0, hNeT⟩
        · exact ⟨hApB.1, hApB.2.1, hApB.2.2, by dsimp only; rw [hBv']; exact readBytesFromMap_writeBytesToMap bv1 ap (metaHdrBytes st'.ctx.secret 0#64) (by rw [metaHdrBytes_length]; omega)⟩
        · have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); have hSep := hPageSep _ (List.getLast_mem hne); refine ⟨htb.1, htb.2.1, htb.2.2.1, ?_⟩; dsimp only; rw [hCtx'.2.2.2.2.2.2.1 hne, hBv']
          have hCg : readBytesFromMap (writeBytesToMap bv1 ap (metaHdrBytes st'.ctx.secret 0#64)) (st.metaAreas.getLast hne).base 24 = readBytesFromMap bv1 (st.metaAreas.getLast hne).base 24 :=
            readBytesFromMap_congr (by decide) fun a ha => writeBytesToMap_out _ _ _ fun hIn => by rw [metaHdrBytes_length] at hIn; have h1 := (inRegion_toNat (by omega)).mp ha; have h2 := (inRegion_toNat (by omega)).mp hIn; omega
          have hBv1Eq : bv1 = writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) := by simp [bv1, hne]
          rw [hCg, hBv1Eq]; exact readBytesFromMap_writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) (by rw [metaHdrBytes_length]; omega)
        · have hne0 : st.metaAreas ≠ [] := fun h => by rw [h] at hma0; cases hma0
          have hb := hwf.metaAreas_wf.2.1 ma hma0; have hSep := hPageSep ma hma0; refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩; rw [hCtx'.2.2.2.2.2.2.1 hne0, ← hb.2.2.2, hBv']
          exact readBytesFromMap_congr (by decide) fun a ha => by rw [writeBytesToMap_out _ _ _ (fun hIn => by rw [metaHdrBytes_length] at hIn; have h1 := (inRegion_toNat (by omega)).mp ha; have h2 := (inRegion_toNat (by omega)).mp hIn; omega)]; exact hBv1Ma ma hma0 hNeT a ha
      · cases hEq' : st'.metaAreas with
        | nil => exact False.elim (hMaNe (hMa' ▸ hEq'))
        | cons hd' tl' =>
          refine ⟨by have hMapEq : hd'.base :: tl'.map (·.base) = st.metaAreas.map (·.base) ++ [ap] := by rw [← List.map_cons, ← hEq', hMa', hMapBase]
                     rw [hCtx'.2.2.2.2.1]; cases hEq0 : st.metaAreas <;> simp [hEq0] at hMapEq <;> exact hMapEq.1.symm,
            fun hne' => by rw [hCtx'.2.2.2.2.2.1, hGetLastEq (hEq'.symm.trans hMa') hne' hMaNe, hMaLast]; exact ⟨rfl, rfl⟩,
            fun i hi => by have hL := hChLinks i (by rw [← hMa', hEq']; exact hi); simp only [← hMa', hEq'] at hL; exact hL⟩
    guard_avail_wf := hGuardAvail'
    inflight_wf := by rw [hRm', List.length_cons, hGA.2.2.2.1]; have := hwf.inflight_wf; omega
    free_bump_metas_wf := by
      have h100 : (100#64 : BitVec 64).toNat = 100 := rfl
      have h101Sub : 101 - 100 = 1 := rfl
      refine ⟨by rw [hCtx'.2.1, hFm']; simp [CircularDllWf], fun _ h => (by rw [hFm'] at h; cases h),
        Or.inr ⟨by rw [hCtx'.2.2.2.1]; decide, by rw [hCtx'.2.2.2.1]; decide,
          ⟨hMa' ▸ hMaNe, by rw [hGetLastEq hMa' _ hMaNe, hMaLast, hCtx'.2.2.2.1, hCtx'.2.2.1, h100]; rfl,
           by rw [hGetLastEq hMa' _ hMaNe, hMaLast, hCtx'.2.2.2.1, hBm', h100, h101Sub]⟩⟩, fun bm hbm => ?_, ?_⟩
      · rw [hBm'] at hbm; obtain ⟨j, hjR, rfl⟩ := List.mem_map.mp hbm; have hj := List.mem_range.mp hjR
        have hZ : ∀ (n : Nat) (b : BitVec 64), readBytesFromMap (fun _ => 0#8) b n = List.replicate n 0#8 := fun n => by induction n with | zero => intro _; rfl | succ n ih => intro b; rw [readBytesFromMap_succ, ih]; rfl
        rw [← hZ 40]; exact readBytesFromMap_congr (by decide) fun a ha => hBvAp64 a (by have hSN : (({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)).toNat = ap.toNat + 24 + 40 * (1 + j) := (by unfold MetaAreaDesc.slotAddr; dsimp only; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have haN := (inRegion_toNat (by omega)).mp ha; exact (inRegion_toNat (by rw [hAp64Nat]; omega)).mpr ⟨by rw [hAp64Nat]; omega, by rw [hAp64Nat]; omega⟩)
      · dsimp only; rw [hGs'.1, hFm', List.map_nil, List.append_nil, hRm']; rw [hNoFree, hNoBump, List.map_nil, List.append_nil, List.append_nil] at hUfNd hUfIff
        have hNewNd : ((ap + 24#64) :: st'.bumpMetas).Nodup := hNewSlotsEq ▸ hNewSlotsNd
        have hNewDisj : ∀ x ∈ (ap + 24#64) :: st'.bumpMetas, x ∉ st.groups.map (·.metaPtr) ++ st.reservedMetas := fun x hx hOld => by rw [← hNewSlotsEq] at hx; obtain ⟨k, hkR, rfl⟩ := List.mem_map.mp hx; exact hNewNotAll k (List.mem_range.mp hkR) ((hUfIff _).mp hOld)
        have ⟨hANd, hDNd, hAD⟩ := List.nodup_append.mp hUfNd; have ⟨hcNotB, hBNd⟩ := List.nodup_cons.mp hNewNd
        refine ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hANd, hBNd, fun x hx y hy hxy => hNewDisj y (List.Mem.tail _ hy) (List.mem_append_left _ (hxy ▸ hx))⟩,
          List.nodup_cons.mpr ⟨fun hcD => hNewDisj _ (List.Mem.head _) (List.mem_append_right _ hcD), hDNd⟩, fun x hx y hy hxy => by
            subst hxy; rcases List.mem_append.mp hx with hxA | hxB <;> rcases List.mem_cons.mp hy with rfl | hyD
            · exact hNewDisj _ (List.Mem.head _) (List.mem_append_left _ hxA)
            · exact hAD x hxA x hyD rfl
            · exact hcNotB hxB
            · exact hNewDisj x (List.Mem.tail _ hxB) (List.mem_append_right _ hyD)⟩, fun x => ?_⟩
        simp only [hAllEq, List.mem_append, List.mem_cons, ← hUfIff x]
        exact ⟨fun h => h.elim (fun hAB => hAB.elim (Or.inl ∘ Or.inl) (Or.inr ∘ Or.inr)) (fun hCD => hCD.elim (Or.inr ∘ Or.inl) (Or.inl ∘ Or.inr)), fun h => h.elim (fun hAD => hAD.elim (Or.inl ∘ Or.inl) (Or.inr ∘ Or.inr)) (fun hCB => hCB.elim (Or.inr ∘ Or.inl) (Or.inl ∘ Or.inr))⟩
    groups_nodup := hGs'.1 ▸ hwf.groups_nodup, groups_wf := hGA.1, regions_disjoint := ⟨hPd', trivial⟩, active_wf := hGA.2.1
    liveMap_wf := fun p n => by rw [hGs'.2.2, hGs'.1]; exact hwf.liveMap_wf p n
    live_le_peak := hwf.live_le_peak, effCost_le_live := by rw [hGA.2.2.2.2]; exact hwf.effCost_le_live
    meta_pages_bound := ⟨by rw [hMa', hMaLen]; exact metaAreas_length_succ_le hwf hInflight hNoFree hNoBump, hShiftB'.1, hShiftB'.2⟩
    empty_groups_bound := fun g hg hEmp => by
      rw [hGs'.1] at hg
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hwf.empty_groups_bound g hg hEmp
      exact ⟨h1, h2, h3, h4, fun h => by have hA := hGs'.2.1; simp only [hA] at h ⊢; exact h5 h,
        fun g' hg' => h6 g' (by rwa [hGs'.1] at hg'), h7⟩
    masterDom_wf := hDomWf' }
  exact ⟨⟨fun h => by rw [h] at hMNat; simp at hMNat, by omega, by omega, by omega, hmNotRes⟩, hWf', hGA.2.2.1⟩

theorem activate_metaArea_bytemap {inflight : Nat} {base brkStart brk brk' ap : BitVec 64} {liveCost peakCost : Nat} {st st' : MallocngSt} {bv0 : BitVec 64 → BitVec 8}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hwf' : MallocngWFInflight (inflight + 1) base brkStart brk' liveCost peakCost st')
    (hApB : 4096 ≤ ap.toNat ∧ ap.toNat % 4096 = 0 ∧ ap.toNat + 4096 ≤ 2 ^ 48) (hApDisj : ap ∉ st.metaAreas.map (·.base) ∧ ∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions ap 4096 g.mem (g.maplen * 4096))
    (hBv0Ma : ∀ ma ∈ st.metaAreas, ∀ a : BitVec 64, InRegion ma.base 4096 a → bv0 a = st.byteVal a) (hBv0Zero : ∀ a : BitVec 64, InRegion (ap + 64#64) 4032 a → bv0 a = 0#8)
    (hBv' : st'.byteVal = writeBytesToMap (if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0) ap (metaHdrBytes st'.ctx.secret 0#64))
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas ap) (hRm' : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas) (hGs1 : st'.groups = st.groups) :
    let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0
    (∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base; ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧ ((tb ↦ₛ metaHdrBytes st.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1) ∧
    ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal := by
  dsimp only; let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0
  have hDomWf' := hwf'.masterDom_wf; have ⟨_, hUfIff⟩ := hwf.free_bump_metas_wf.2.2.2.2; obtain ⟨hMapBase, _⟩ := appendMetaArea_props st.metaAreas ap
  have hMNat : (ap + 24#64).toNat = ap.toNat + 24 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hAp64Nat : (ap + 64#64).toNat = ap.toNat + 64 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hPageSep : ∀ ma ∈ st.metaAreas, ma.base.toNat + 4096 ≤ ap.toNat ∨ ap.toNat + 4096 ≤ ma.base.toNat := fun ma hma => by have hb := hwf.metaAreas_wf.2.1 ma hma; have hne : ma.base.toNat ≠ ap.toNat := fun h => hApDisj.1 (BitVec.eq_of_toNat_eq h ▸ List.mem_map_of_mem hma); omega
  have hTail0 : ∀ hne : st.metaAreas ≠ [], (st.metaAreas.getLast hne).next = 0#64 := by have h2 := hwf.metaAreas_wf.2.2; cases hEq : st.metaAreas with | nil => intro hne; exact False.elim (hne rfl) | cons _ _ => rw [hEq] at h2; intro hne; exact (h2.2.1 hne).2
  have hNoUserPage : ∀ b : BitVec 64, b.toNat + 4096 ≤ 2 ^ 48 → (∀ rg ∈ st.groups, 0 < rg.maplen → DisjointRegions b 4096 rg.mem (rg.maplen * 4096)) → ∀ a : BitVec 64, InRegion b 4096 a → ¬ CarvedUserByte st a :=
    fun b hbFit hbDisj a ha ⟨g, hg, s, hs, hInU⟩ => by
      cases s with
      | freeAvail | freeInactive | claimed | liveNested _ => cases hInU
      | liveUser _ _ _ =>
        obtain ⟨idx, hIdx, hsEq⟩ := List.mem_iff_getElem.mp hs; obtain ⟨_, _, hgLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hSlotWf⟩ := hwf.groups_wf g hg
        have hswf := hSlotWf idx hIdx; rw [hsEq] at hswf; obtain ⟨_, hStartLe, hReqLe, _⟩ := hswf.2.2.2.2; have ⟨hStartNat, _, hEndLe⟩ := group_slotStart_End_toNat (hwf.groups_wf g hg) idx (by unfold GroupDesc.cnt at hgLen; omega)
        obtain ⟨rg, hrg, hrgMl, hrgLo, hrgHi, _⟩ := rootAncestor_of_group hwf g hg; obtain ⟨_, _, _, _, _, _, hrgTotFit, _⟩ := hwf.groups_wf rg hrg; have hrgTot : rg.totalBytes = rg.maplen * 4096 := (by simp [GroupDesc.totalBytes, hrgMl])
        have hSep := nat_sep_of_disjointRegions (by decide) (by omega) hbFit (hrgTot ▸ hrgTotFit) (hbDisj rg hrg hrgMl); have h1 := (inRegion_toNat (by omega)).mp ha; have h2 := (inRegion_toNat (by omega)).mp hInU; omega
  have hRwIff : ∀ a : BitVec 64, OwnedRwByte st' a ↔ (OwnedRwByte st a ∨ InRegion ap 24 a ∨ InRegion (ap + 64#64) 4032 a) := fun a => by
    have hMaMemIff : (∃ ma ∈ st'.metaAreas, InRegion ma.base 4096 a) ↔ (∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨ InRegion ap 4096 a :=
      ⟨fun ⟨ma, hma, ha⟩ => (List.mem_append.mp (show ma.base ∈ st.metaAreas.map (·.base) ++ [ap] by rw [← hMapBase, ← hMa']; exact List.mem_map_of_mem hma)).elim (fun hOld => by obtain ⟨ma0, hma0, hEq⟩ := List.mem_map.mp hOld; exact Or.inl ⟨ma0, hma0, hEq ▸ ha⟩) (fun hNew => by simp at hNew; subst hNew; exact Or.inr ha),
       fun h => h.elim (fun ⟨ma, hma, ha⟩ => by obtain ⟨ma', hma', hEq⟩ := List.mem_map.mp (show ma.base ∈ st'.metaAreas.map (·.base) by rw [hMa', hMapBase]; exact List.mem_append_left _ (List.mem_map_of_mem hma)); exact ⟨ma', hma', hEq.symm ▸ ha⟩) (fun ha => by obtain ⟨ma', hma', hEq⟩ := List.mem_map.mp (show ap ∈ st'.metaAreas.map (·.base) by rw [hMa', hMapBase]; exact List.mem_append_right _ (List.Mem.head _)); exact ⟨ma', hma', hEq.symm ▸ ha⟩)⟩
    have hCarveU : CarvedUserByte st' a ↔ CarvedUserByte st a := carvedUserByte_congr hGs1 a; have hCarveM : CarvedMetaByte st' a ↔ InRegion (ap + 24#64) 40 a ∨ CarvedMetaByte st a := (by simp [CarvedMetaByte, hRm', or_and_right, exists_or])
    unfold OwnedRwByte; rw [hMaMemIff, hGs1, hCarveU, hCarveM]; constructor
    · rintro ⟨(hMa | hAp) | hRg, hNU, hNM⟩
      · exact Or.inl ⟨Or.inl hMa, hNU, fun h => hNM (Or.inr h)⟩
      · have haN := (inRegion_toNat (by omega)).mp hAp; have _ : ¬ (ap.toNat + 24 ≤ a.toNat ∧ a.toNat < ap.toNat + 64) := fun h => hNM (Or.inl ((inRegion_toNat (by rw [hMNat]; omega)).mpr ⟨by rw [hMNat]; omega, by rw [hMNat]; omega⟩))
        exact if hLt24 : a.toNat < ap.toNat + 24 then Or.inr (Or.inl ((inRegion_toNat (by omega)).mpr ⟨by omega, hLt24⟩)) else Or.inr (Or.inr ((inRegion_toNat (by rw [hAp64Nat]; omega)).mpr ⟨by rw [hAp64Nat]; omega, by rw [hAp64Nat]; omega⟩))
      · exact Or.inl ⟨Or.inr hRg, hNU, fun h => hNM (Or.inr h)⟩
    · rintro (⟨hLoc, hNU, hNM⟩ | hSub)
      · refine ⟨hLoc.elim (Or.inl ∘ Or.inl) Or.inr, hNU, fun h => h.elim (fun hM => ?_) hNM⟩; have hmN := (inRegion_toNat (by rw [hMNat]; omega)).mp hM
        exact hLoc.elim (fun ⟨ma, hma, haMa⟩ => by have hb := hwf.metaAreas_wf.2.1 ma hma; have hS := hPageSep ma hma; have h2 := (inRegion_toNat (by omega)).mp haMa; omega)
          (fun ⟨g, hg, hMl, haG⟩ => by obtain ⟨_, _, _, _, _, _, hgTotFit, _⟩ := hwf.groups_wf g hg; have hgTot : g.totalBytes = g.maplen * 4096 := (by simp [GroupDesc.totalBytes, hMl]); have hS := nat_sep_of_disjointRegions (by decide) (by omega) hApB.2.2 (hgTot ▸ hgTotFit) (hApDisj.2 g hg hMl); have h2 := (inRegion_toNat (by omega)).mp haG; omega)
      · have ⟨ha4096, hNotM⟩ : InRegion ap 4096 a ∧ ¬ InRegion (ap + 24#64) 40 a := hSub.elim
          (fun h24 => by have haN := (inRegion_toNat (by omega)).mp h24; exact ⟨(inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩, fun hM => by have := (inRegion_toNat (by rw [hMNat]; omega)).mp hM; omega⟩)
          (fun h4032 => by have haN := (inRegion_toNat (by rw [hAp64Nat]; omega)).mp h4032; exact ⟨(inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩, fun hM => by have := (inRegion_toNat (by rw [hMNat]; omega)).mp hM; omega⟩)
        refine ⟨Or.inl (Or.inr ha4096), hNoUserPage ap hApB.2.2 hApDisj.2 a ha4096, fun h => h.elim hNotM fun ⟨mr, hmr, haMr⟩ => ?_⟩
        have hmrAll := (hUfIff mr).mp (List.mem_append_right _ hmr); unfold allMetaSlots at hmrAll; obtain ⟨ma, hma, hmS⟩ := List.mem_flatMap.mp hmrAll; obtain ⟨k, hkR, rfl⟩ := List.mem_map.mp hmS
        have hk := List.mem_range.mp hkR; have hb := hwf.metaAreas_wf.2.1 ma hma; have hS := hPageSep ma hma; have hSN : (ma.slotAddr k).toNat = ma.base.toNat + 24 + 40 * k := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        have h1 := (inRegion_toNat (by omega)).mp ha4096; have h2 := (inRegion_toNat (by omega)).mp haMr; omega
  have hSubDom' : ∀ a : BitVec 64, OwnedRwByte st' a → a ∈ st'.masterDom := fun a h => hDomWf'.2.1 a (Or.inl h)
  have hDisjApRw0 : ∀ a : BitVec 64, InRegion ap 4096 a → ¬ OwnedRwByte st a := fun a ha ⟨hLoc, _, _⟩ => by
    have haN := (inRegion_toNat (by omega)).mp ha
    exact hLoc.elim (fun ⟨ma, hma, haMa⟩ => by have hb := hwf.metaAreas_wf.2.1 ma hma; have hS := hPageSep ma hma; have h2 := (inRegion_toNat (by omega)).mp haMa; omega)
      (fun ⟨g, hg, hMl, haG⟩ => by obtain ⟨_, _, _, _, _, _, hgTotFit, _⟩ := hwf.groups_wf g hg; have hgTot : g.totalBytes = g.maplen * 4096 := (by simp [GroupDesc.totalBytes, hMl]); have hS := nat_sep_of_disjointRegions (by decide) (by omega) hApB.2.2 (hgTot ▸ hgTotFit) (hApDisj.2 g hg hMl); have h2 := (inRegion_toNat (by omega)).mp haG; omega)
  refine ⟨fun hne => ?_, ?_⟩
  · have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne)
    have hTbRw : ∀ a : BitVec 64, InRegion (st.metaAreas.getLast hne).base 24 a → OwnedRwByte st a ∧ a ∈ st'.masterDom := fun a ha => by
      have haN := (inRegion_toNat (by omega)).mp ha; have ha4096 : InRegion (st.metaAreas.getLast hne).base 4096 a := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩
      have hNoU := hNoUserPage (st.metaAreas.getLast hne).base htb.2.2.1 (fun rg hrg hrgMl => by have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff] at hpd; exact hpd.2.2 ((st.metaAreas.getLast hne).base, 4096) (List.mem_map_of_mem (List.getLast_mem hne)) (rg.mem, rg.maplen * 4096) (List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hrgMl⟩))))) a ha4096
      have hNoM : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, haMr⟩ => by have hmrAll := (hUfIff mr).mp (List.mem_append_right _ hmr); unfold allMetaSlots at hmrAll; obtain ⟨ma, hma, hmS⟩ := List.mem_flatMap.mp hmrAll; obtain ⟨k, hkR, rfl⟩ := List.mem_map.mp hmS; have hk := List.mem_range.mp hkR; have hb := hwf.metaAreas_wf.2.1 ma hma; have hSN : (ma.slotAddr k).toNat = ma.base.toNat + 24 + 40 * k := (by unfold MetaAreaDesc.slotAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have h2 := (inRegion_toNat (by omega)).mp haMr; by_cases hS : ma.base.toNat = (st.metaAreas.getLast hne).base.toNat <;> omega
      have hOwn : OwnedRwByte st a := ⟨Or.inl ⟨_, List.getLast_mem hne, ha4096⟩, hNoU, hNoM⟩; exact ⟨hOwn, hSubDom' a ((hRwIff a).mpr (Or.inl hOwn))⟩
    have hTbRead : readBytesFromMap bv0 (st.metaAreas.getLast hne).base 24 = metaHdrBytes st.ctx.secret 0#64 := by rw [readBytesFromMap_congr (v₂ := st.byteVal) (by decide) fun a ha => hBv0Ma _ (List.getLast_mem hne) a ((inRegion_toNat (by omega)).mpr ⟨((inRegion_toNat (by omega)).mp ha).1, by have := ((inRegion_toNat (by omega)).mp ha).2; omega⟩), htb.2.2.2, hTail0 hne]; rfl
    have hExT := ByteMap_extract_slice hDomWf'.1 (keep := OwnedRwByte st) bv0 (st.metaAreas.getLast hne).base (n := 24) (by decide) (fun a ha => (hTbRw a ha).2) (fun a ha => (hTbRw a ha).1)
    have hAbsT := ByteMap_absorb_slice hDomWf'.1 (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion (st.metaAreas.getLast hne).base 24 a) bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) (by rw [metaHdrBytes_length]; omega) (fun a ha => (hTbRw a (by rw [metaHdrBytes_length] at ha; exact ha)).2) (fun a ha h => h.2 (by rw [metaHdrBytes_length] at ha; exact ha))
    refine ⟨by rw [hExT, hTbRead], ?_⟩; have hIfEq : (if hne' : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne').base (metaHdrBytes st.ctx.secret ap) else bv0) = writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) := by simp [hne]
    rw [hAbsT, hIfEq]; exact SetSep_congr (fun a _ => ⟨fun h => h.elim And.left fun ha => (hTbRw a (by rw [metaHdrBytes_length] at ha; exact ha)).1, fun h0 => if ha : InRegion (st.metaAreas.getLast hne).base 24 a then Or.inr (by rw [metaHdrBytes_length]; exact ha) else Or.inl ⟨h0, ha⟩⟩) (fun _ _ _ => rfl)
  · let keepMid := fun a => OwnedRwByte st a ∨ InRegion (ap + 64#64) 4032 a
    have hBv1Zero : readBytesFromMap bv1 (ap + 64#64) 4032 = List.replicate 4032 0#8 := by
      have hZ : ∀ (n : Nat) (b : BitVec 64), readBytesFromMap (fun _ => 0#8) b n = List.replicate n 0#8 := fun n => by induction n with | zero => intro _; rfl | succ n ih => intro b; rw [readBytesFromMap_succ, ih]; rfl
      rw [← hZ 4032 (ap + 64#64)]; exact readBytesFromMap_congr (by decide) fun a ha => by
        dsimp only [bv1]; split
        · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); have hSep := hPageSep _ (List.getLast_mem hne); rw [writeBytesToMap_out _ _ _ (fun hIn => by rw [metaHdrBytes_length] at hIn; have h1 := (inRegion_toNat (by rw [hAp64Nat]; omega)).mp ha; have h2 := (inRegion_toNat (by omega)).mp hIn; omega), hBv0Zero a ha]
        · exact hBv0Zero a ha
    have hEx4032 := ByteMap_extract_slice hDomWf'.1 (keep := keepMid) bv1 (ap + 64#64) (n := 4032) (by decide) (fun a ha => hSubDom' a ((hRwIff a).mpr (Or.inr (Or.inr ha)))) (fun _ ha => Or.inr ha)
    have hMidRest : ByteMap st'.masterDom (fun a => keepMid a ∧ ¬ InRegion (ap + 64#64) 4032 a) bv1 = ByteMap st'.masterDom (OwnedRwByte st) bv1 :=
      SetSep_congr (fun a _ => ⟨fun ⟨h, hN⟩ => h.elim id (fun h4 => False.elim (hN h4)), fun h0 => ⟨Or.inl h0, fun h4 => hDisjApRw0 a ((inRegion_toNat (by omega)).mpr ⟨by have := ((inRegion_toNat (by rw [hAp64Nat]; omega)).mp h4).1; omega, by have := ((inRegion_toNat (by rw [hAp64Nat]; omega)).mp h4).2; omega⟩) h0⟩⟩) (fun _ _ _ => rfl)
    have hAbs24 := ByteMap_absorb_slice hDomWf'.1 (keep := keepMid) bv1 ap (metaHdrBytes st'.ctx.secret 0#64) (by rw [metaHdrBytes_length]; omega) (fun a ha => hSubDom' a ((hRwIff a).mpr (Or.inr (Or.inl (by rw [metaHdrBytes_length] at ha; exact ha)))))
      (fun a ha h => by rw [metaHdrBytes_length] at ha; have haN := (inRegion_toNat (by omega)).mp ha; exact h.elim (hDisjApRw0 a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)) (fun h4 => by have := (inRegion_toNat (by rw [hAp64Nat]; omega)).mp h4; omega))
    rw [← hMidRest, ← hBv1Zero, ← hEx4032, hAbs24, ← hBv']
    exact SetSep_congr (fun a _ => ⟨fun h => (hRwIff a).mpr (h.elim (fun h04 => h04.elim Or.inl (Or.inr ∘ Or.inr)) (fun h2 => Or.inr (Or.inl (by rw [metaHdrBytes_length] at h2; exact h2)))), fun h => ((hRwIff a).mp h).elim (Or.inl ∘ Or.inl) (fun h24 => h24.elim (fun h2 => Or.inr (by rw [metaHdrBytes_length]; exact h2)) (Or.inl ∘ Or.inr))⟩) (fun _ _ _ => rfl)

theorem slowPathA_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hInflight : inflight ≤ 7) (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = []) (hCntNe : st.ctx.availMetaAreaCount ≠ 0#64) :
    let ap := st.ctx.availMetaAreas; let cnt' := st.ctx.availMetaAreaCount - 1#64; let rest := (List.range cnt'.toNat).map (fun i => (ap + 4096#64) + BitVec.ofNat 64 (4096 * i))
    let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap st.byteVal (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else st.byteVal
    let st' : MallocngSt := { st with
      ctx := { st.ctx with availMeta := ap + 64#64, availMetaCount := 100#64, availMetaAreaCount := cnt', metaAreaHead := (match st.metaAreas with | [] => ap | hd :: _ => hd.base), metaAreaTail := ap, availMetaAreas := ap + 4096#64 },
      metaAreas := appendMetaArea st.metaAreas ap, mmapMetaAreas := ((appendMetaArea st.metaAreas ap).map (·.base)).filter (fun mb => !decide (InRegion brkStart (brk.toNat - brkStart.toNat) mb)),
      availMetaPages := rest, freeMetas := [], bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (ap + 24#64) :: st.reservedMetas, byteVal := writeBytesToMap bv1 ap (metaHdrBytes st.ctx.secret 0#64) }
    (4096 ≤ ap.toNat ∧ ap.toNat % 4096 = 0 ∧ ap.toNat + 4096 ≤ 2 ^ 48) ∧ ((ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas) ∧
    MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧ (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) ∧
    (∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base; ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((tb ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) st.byteVal) ∧ ((tb ↦ₛ metaHdrBytes st.ctx.secret ap) ∗ ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) st.byteVal) = ByteMap st.masterDom (OwnedRwByte st) bv1) ∧
    ((ap ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  intro ap cnt' rest bv1 st'
  have hCntPos : 0 < st.ctx.availMetaAreaCount.toNat := Nat.pos_of_ne_zero fun h0 => hCntNe (BitVec.eq_of_toNat_eq h0)
  have hCntEq : st.ctx.availMetaAreaCount.toNat = cnt'.toNat + 1 := by dsimp only [cnt']; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; exact hCntPos), BitVec.toNat_ofNat]; omega
  have hAvEq : st.availMetaPages = ap :: rest := by
    have hSh : ∀ (k n : Nat) (b : BitVec 64), (List.range (n + 1)).map (fun i => b + BitVec.ofNat 64 (k * i)) = b :: (List.range n).map (fun i => (b + BitVec.ofNat 64 k) + BitVec.ofNat 64 (k * i)) := fun k n b => by
      rw [List.range_succ_eq_map, List.map_cons, Nat.mul_zero, BitVec.add_zero, List.map_map]; exact congrArg (List.cons b) (List.map_congr_left fun i _ => by dsimp only [Function.comp]; rw [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 (k * i)), ← BitVec.add_assoc])
    rw [hwf.guard_avail_wf.2.2.1, hCntEq]; exact hSh 4096 cnt'.toNat ap
  have hApMem : ap ∈ st.availMetaPages := (by rw [hAvEq]; exact List.Mem.head _); obtain ⟨hApLo, hApMod, hApFit, hApRead0⟩ := hwf.guard_avail_wf.2.2.2 ap hApMem
  have hAp64Nat : (ap + 64#64).toNat = ap.toNat + 64 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hBrkNeg1 : st.ctx.brk = -1#64 := Classical.byContradiction fun hne => hCntNe (hwf.brk_mode_wf.1 ⟨h1, hne⟩).2.2.1
  obtain ⟨hMapBase, hMaLen, _, _⟩ := appendMetaArea_props st.metaAreas ap
  have hMapMaPair : st'.metaAreas.map (fun ma => (ma.base, 4096)) = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by
    calc st'.metaAreas.map (fun ma => (ma.base, 4096)) = ((appendMetaArea st.metaAreas ap).map MetaAreaDesc.base).map (fun b => (b, 4096)) := by dsimp only [st']; rw [List.map_map]; rfl
      _ = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by rw [hMapBase, List.map_append, List.map_map]; rfl
  have hFmHd0 : st.ctx.freeMetaHead = 0#64 := (by have h := hwf.free_bump_metas_wf.1; simp [hNoFree] at h; exact h); have hSym : ∀ {b1 b2 : BitVec 64} {n1 n2 : Nat}, DisjointRegions b1 n1 b2 n2 → DisjointRegions b2 n2 b1 n1 := fun h => ⟨h.2, h.1⟩
  have hPd0 := hwf.regions_disjoint.1; unfold dynamicRootRegions at hPd0; rw [hAvEq, List.map_cons] at hPd0
  have ⟨hPdMaGp, hPdApRg, hCross1⟩ := pairwiseDisjoint_append_iff.mp (by simpa only [List.append_assoc] using hPd0 : PairwiseDisjointRegions ((st.metaAreas.map (fun ma => (ma.base, 4096)) ++ st.guardPages.map (fun gp => (gp, 4096))) ++ (((ap, 4096) :: rest.map (fun a => (a, 4096))) ++ (st.groups.filter (fun g => decide (0 < g.maplen))).map (fun g => (g.mem, g.maplen * 4096)))))
  have ⟨hPdMa, hPdGp, hCrossMaGp⟩ := pairwiseDisjoint_append_iff.mp hPdMaGp; have ⟨hPdConsRest, hPdRg, hCrossApRg⟩ := pairwiseDisjoint_append_iff.mp hPdApRg
  have ⟨hApDisjRest, hPdRest⟩ := (by simpa [PairwiseDisjointRegions] using hPdConsRest : (∀ z ∈ rest.map (fun a => (a, 4096)), DisjointRegions ap 4096 z.1 z.2) ∧ PairwiseDisjointRegions (rest.map (fun a => (a, 4096))))
  have hApDisjMa : ∀ ma ∈ st.metaAreas, DisjointRegions ma.base 4096 ap 4096 := fun ma hma => hCross1 (ma.base, 4096) (List.mem_append_left _ (List.mem_map_of_mem hma)) (ap, 4096) (List.mem_append_left _ (List.Mem.head _))
  have hApDisjGp : ∀ gp ∈ st.guardPages, DisjointRegions gp 4096 ap 4096 := fun gp hgp => hCross1 (gp, 4096) (List.mem_append_right _ (List.mem_map_of_mem hgp)) (ap, 4096) (List.mem_append_left _ (List.Mem.head _))
  have hApNotMa : ap ∉ st.metaAreas.map (·.base) := fun hm => by obtain ⟨ma, hma, hEq⟩ := List.mem_map.mp hm; have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.metaAreas_wf.2.1 ma hma).2.2.1 hApFit (hApDisjMa ma hma); have := congrArg BitVec.toNat hEq; omega
  have hApDisjRg : ∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions ap 4096 g.mem (g.maplen * 4096) := fun g hg hml => hCrossApRg (ap, 4096) (List.Mem.head _) (g.mem, g.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))
  have hPdMa' : PairwiseDisjointRegions (st'.metaAreas.map (fun ma => (ma.base, 4096))) := by rw [hMapMaPair, pairwiseDisjoint_append_iff]; exact ⟨hPdMa, by simp [PairwiseDisjointRegions], fun x hx y hy => by obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hx; simp at hy; subst hy; exact hApDisjMa ma hma⟩
  have hPd' : PairwiseDisjointRegions (dynamicRootRegions st') := by
    unfold dynamicRootRegions; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff]
    refine ⟨hPdMa', pairwiseDisjoint_append_iff.mpr ⟨hPdGp, pairwiseDisjoint_append_iff.mpr ⟨hPdRest, hPdRg, fun x hx y hy => hCrossApRg x (List.Mem.tail _ hx) y hy⟩,
      fun x hx y hy => (List.mem_append.mp hy).elim (fun hyR => hCross1 x (List.mem_append_right _ hx) y (List.mem_append_left _ (List.Mem.tail _ hyR))) (fun hyG => hCross1 x (List.mem_append_right _ hx) y (List.mem_append_right _ hyG))⟩, fun x hx y hy => ?_⟩
    exact (show x ∈ st.metaAreas.map (fun ma => (ma.base, 4096)) ∨ x = (ap, 4096) by simpa [hMapMaPair] using hx).elim
      (fun hxMa => (List.mem_append.mp hy).elim (hCrossMaGp x hxMa y) fun hy2 => (List.mem_append.mp hy2).elim (fun hyR => hCross1 x (List.mem_append_left _ hxMa) y (List.mem_append_left _ (List.Mem.tail _ hyR))) (fun hyG => hCross1 x (List.mem_append_left _ hxMa) y (List.mem_append_right _ hyG)))
      (fun hxAp => by rw [hxAp]; exact (List.mem_append.mp hy).elim (fun hyGp => by obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hyGp; exact hSym (hApDisjGp gp hgp)) fun hy2 => (List.mem_append.mp hy2).elim (hApDisjRest y) (fun hyG => hCrossApRg (ap, 4096) (List.Mem.head _) y hyG))
  have hBv0Zero : ∀ a : BitVec 64, InRegion ap 4096 a → st.byteVal a = 0#8 := fun a ha => by
    have haN := (inRegion_toNat (by omega)).mp ha; have h1 := readBytesFromMap_getElem st.byteVal ap 4096 (a.toNat - ap.toNat) (by rw [readBytesFromMap_length]; omega)
    have hEqA : ap + BitVec.ofNat 64 (a.toNat - ap.toNat) = a := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); rw [hEqA, getElem_congr_coll hApRead0, List.getElem_replicate] at h1; exact h1.symm
  have hBv0Zero64 : ∀ a : BitVec 64, InRegion (ap + 64#64) 4032 a → st.byteVal a = 0#8 := fun a ha => by have := (inRegion_toNat (by omega)).mp ha; exact hBv0Zero a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)
  have hBvPnAg : ∀ p : BitVec 64, (p ∈ st.guardPages ∨ p ∈ rest) → ∀ a : BitVec 64, InRegion p 4096 a → st'.byteVal a = st.byteVal a := fun p hp a ha => by
    have ⟨hpFit, hpSepAp⟩ : p.toNat + 4096 ≤ 2 ^ 48 ∧ (p.toNat + 4096 ≤ ap.toNat ∨ ap.toNat + 4096 ≤ p.toNat) :=
      hp.elim (fun hgp => ⟨(hwf.guard_avail_wf.2.1 p hgp).2.2, nat_sep_of_disjointRegions (by omega) (by omega) (hwf.guard_avail_wf.2.1 p hgp).2.2 hApFit (hApDisjGp p hgp)⟩)
        (fun hr => ⟨(hwf.guard_avail_wf.2.2.2 p (by rw [hAvEq]; exact List.Mem.tail _ hr)).2.2.1, (nat_sep_of_disjointRegions (by omega) (by omega) hApFit (hwf.guard_avail_wf.2.2.2 p (by rw [hAvEq]; exact List.Mem.tail _ hr)).2.2.1 (hApDisjRest (p, 4096) (List.mem_map_of_mem hr))).symm⟩)
    have haN := (inRegion_toNat (by omega)).mp ha; dsimp only [st']; rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have := (inRegion_toNat (by omega)).mp h; omega)]; dsimp only [bv1]; split
    · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne)
      have hDT : DisjointRegions (st.metaAreas.getLast hne).base 4096 p 4096 := hp.elim (fun hgp => hCrossMaGp _ (List.mem_map_of_mem (List.getLast_mem hne)) _ (List.mem_map_of_mem hgp)) (fun hr => hCross1 _ (List.mem_append_left _ (List.mem_map_of_mem (List.getLast_mem hne))) _ (List.mem_append_left _ (List.Mem.tail _ (List.mem_map_of_mem hr))))
      have hSepT := nat_sep_of_disjointRegions (by omega) (by omega) htb.2.2.1 hpFit hDT; exact writeBytesToMap_out _ _ _ fun h => by rw [metaHdrBytes_length] at h; have := (inRegion_toNat (by omega)).mp h; omega
    · rfl
  have hApNotBrk : ¬ InRegion brkStart (brk.toNat - brkStart.toNat) ap := fun hIn => by
    have hBrkB := hwf.brk_bounds; have hInN := (inRegion_toNat (by omega)).mp hIn; obtain ⟨hGpBrk, hMaBrk⟩ := hwf.brk_mode_wf.2.2.2 (by omega)
    by_cases hk0 : (ap.toNat - brkStart.toNat) / 4096 = 0
    · have : ap = brkStart := BitVec.eq_of_toNat_eq (by omega); have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.guard_avail_wf.2.1 brkStart hGpBrk).2.2 hApFit (this ▸ hApDisjGp brkStart hGpBrk); omega
    · obtain ⟨ma, hma, hEq⟩ := hMaBrk ((ap.toNat - brkStart.toNat) / 4096) (by omega) (by omega)
      have hRhs : (brkStart + BitVec.ofNat 64 (4096 * ((ap.toNat - brkStart.toNat) / 4096))).toNat = ap.toNat := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      exact hApNotMa (BitVec.eq_of_toNat_eq (hRhs.symm.trans (congrArg BitVec.toNat hEq.symm)) ▸ List.mem_map_of_mem hma)
  have hMappedIff : ∀ a : BitVec 64, OwnedMappedByte st' a ↔ OwnedMappedByte st a := fun a => by
    have hMmEq : st'.mmapMetaAreas = st.mmapMetaAreas ++ [ap] := (by change ((appendMetaArea st.metaAreas ap).map (·.base)).filter _ = _; rw [hMapBase, List.filter_append, ← hwf.brk_mode_wf.2.1]; simp [hApNotBrk])
    unfold OwnedMappedByte; simp only [hMmEq, show st'.mmapGuardPages = st.mmapGuardPages from rfl, show st'.availMetaPages = rest from rfl, show st'.groups = st.groups from rfl, hAvEq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨fun h => h.elim (fun ⟨x, h, ha⟩ => h.elim (fun hx => Or.inl ⟨x, hx, ha⟩) (fun hxEq => Or.inr (Or.inr (Or.inl ⟨ap, Or.inl rfl, hxEq ▸ ha⟩)))) (fun h2 => h2.elim (Or.inr ∘ Or.inl) (fun h3 => h3.elim (fun ⟨x, hx, ha⟩ => Or.inr (Or.inr (Or.inl ⟨x, Or.inr hx, ha⟩))) (Or.inr ∘ Or.inr ∘ Or.inr))),
      fun h => h.elim (fun ⟨x, hx, ha⟩ => Or.inl ⟨x, Or.inl hx, ha⟩) (fun h2 => h2.elim (Or.inr ∘ Or.inl) (fun h3 => h3.elim (fun ⟨x, h, ha⟩ => h.elim (fun hxEq => Or.inl ⟨ap, Or.inr rfl, hxEq ▸ ha⟩) (fun hx => Or.inr (Or.inr (Or.inl ⟨x, hx, ha⟩)))) (Or.inr ∘ Or.inr ∘ Or.inr)))⟩
  have hPnIff : ∀ a : BitVec 64, OwnedProtNoneByte st a ↔ (InRegion ap 4096 a ∨ OwnedProtNoneByte st' a) := fun a => by
    unfold OwnedProtNoneByte; simp only [hAvEq, show st'.guardPages = st.guardPages from rfl, show st'.availMetaPages = rest from rfl, List.mem_cons, or_and_right, exists_or, exists_eq_left]
    exact ⟨fun h => h.elim (Or.inr ∘ Or.inl) (fun h2 => h2.elim Or.inl (Or.inr ∘ Or.inr)), fun h => h.elim (Or.inr ∘ Or.inl) (fun h2 => h2.elim Or.inl (Or.inr ∘ Or.inr))⟩
  obtain ⟨hMB, hWf', hGrpPost⟩ := activate_metaArea_wf (st' := st') (brk' := brk) (ap := ap) (bv0 := st.byteVal) hwf hInflight hNoFree hNoBump ⟨hApLo, hApMod, hApFit⟩ ⟨hApNotMa, hApDisjRg⟩ (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hBv0Zero64
    rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩ ⟨h1, hFmHd0, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hwf.brk_bounds
    ⟨fun ⟨_, hne⟩ => False.elim (hne hBrkNeg1), rfl, hwf.brk_mode_wf.2.2.1, fun hlt => ⟨(hwf.brk_mode_wf.2.2.2 hlt).1, fun k hk1 hk2 => by obtain ⟨ma, hma, hEq⟩ := (hwf.brk_mode_wf.2.2.2 hlt).2 k hk1 hk2; obtain ⟨ma', hma', hEq'⟩ := List.mem_map.mp (show ma.base ∈ st'.metaAreas.map (·.base) by change ma.base ∈ (appendMetaArea st.metaAreas ap).map (·.base); rw [hMapBase]; exact List.mem_append_left _ (List.mem_map_of_mem hma)); exact ⟨ma', hma', hEq'.trans hEq⟩⟩⟩
    ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, rfl, fun p hp => by obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 p (by rw [hAvEq]; exact List.Mem.tail _ hp); exact ⟨h1, h2, h3, (readBytesFromMap_congr (by omega) (hBvPnAg p (Or.inr hp))).trans h4⟩⟩
    hPd'
    ⟨fun hS0 => False.elim (by have := (hwf.meta_pages_bound.2.1 hS0).1; rw [hAvEq] at this; cases this), fun m hm1 hmEq => by obtain ⟨b1, b2, b3, b4, b5⟩ := hwf.meta_pages_bound.2.2 m hm1 hmEq; have hAvL : st.availMetaPages.length = rest.length + 1 := (by rw [hAvEq]; rfl); exact ⟨b1, by change _ ≤ (appendMetaArea _ _).length; rw [hMaLen]; omega, by change _ ≤ (appendMetaArea _ _).length + rest.length; rw [hMaLen]; omega, b4, by change rest.length ≤ _; omega⟩⟩
    ⟨hwf.masterDom_wf.1, fun a h => hwf.masterDom_wf.2.1 a (h.elim (fun hRw => by
        have hNoM0 : ¬ CarvedMetaByte st a := fun ⟨mr, hmr, hIn⟩ => hRw.2.2 ⟨mr, List.Mem.tail _ hmr, hIn⟩
        exact hRw.1.elim (fun ⟨ma, hma, ha⟩ => (List.mem_append.mp (show ma.base ∈ st.metaAreas.map (·.base) ++ [ap] by rw [← hMapBase]; exact List.mem_map_of_mem hma)).elim (fun hO => by obtain ⟨m0, hm0, hE⟩ := List.mem_map.mp hO; exact Or.inl ⟨Or.inl ⟨m0, hm0, hE ▸ ha⟩, hRw.2.1, hNoM0⟩) (fun hAp => by simp at hAp; rw [hAp] at ha; exact Or.inr (Or.inl (Or.inr ⟨ap, hApMem, ha⟩)))) (fun hRg => Or.inl ⟨Or.inr hRg, hRw.2.1, hNoM0⟩))
      (fun h2 => h2.elim (fun hPn => Or.inr (Or.inl ((hPnIff a).mpr (Or.inr hPn)))) (fun hMp => Or.inr (Or.inr ((hMappedIff a).mp hMp))))),
      fun a ha => by obtain ⟨r, hr, hIn⟩ := hwf.masterDom_wf.2.2 a ha; refine ⟨r, ?_, hIn⟩; unfold dynamicRootRegions at hr ⊢; rw [hMapMaPair]; rw [hAvEq, List.map_cons] at hr; simp only [show st'.guardPages = st.guardPages from rfl, show st'.availMetaPages = rest from rfl, show st'.groups = st.groups from rfl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with ((h | h) | (hq | h)) | h <;> simp [*]⟩
  have hBm := activate_metaArea_bytemap hwf hWf' ⟨hApLo, hApMod, hApFit⟩ ⟨hApNotMa, hApDisjRg⟩ (fun _ _ _ _ => rfl) hBv0Zero64 rfl rfl rfl rfl
  have hExPn := ProtNoneByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedProtNoneByte st) st.byteVal ap (n := 4096) (by omega) (fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inl (Or.inr ⟨ap, hApMem, ha⟩)))) (fun a ha => Or.inr ⟨ap, hApMem, ha⟩)
  have hPnRest : ProtNoneByteMap st.masterDom (fun a => OwnedProtNoneByte st a ∧ ¬ InRegion ap 4096 a) st.byteVal = ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal :=
    SetSep_congr (fun a _ => ⟨fun ⟨h, hN⟩ => ((hPnIff a).mp h).elim (fun hA => False.elim (hN hA)) id, fun h' => ⟨(hPnIff a).mpr (Or.inr h'), fun hA => by
      have haN := (inRegion_toNat (by omega)).mp hA; exact h'.elim (fun ⟨gp, hgp, haG⟩ => by have hgpFit := (hwf.guard_avail_wf.2.1 gp hgp).2.2; have hSep := nat_sep_of_disjointRegions (by omega) (by omega) hgpFit hApFit (hApDisjGp gp hgp); have haGN := (inRegion_toNat (by omega)).mp haG; omega) (fun ⟨p, hp, haP⟩ => by have hPFit := (hwf.guard_avail_wf.2.2.2 p (by rw [hAvEq]; exact List.Mem.tail _ hp)).2.2.1; have hSep := nat_sep_of_disjointRegions (by omega) (by omega) hApFit hPFit (hApDisjRest (p, 4096) (List.mem_map_of_mem hp)); have haPN := (inRegion_toNat (by omega)).mp haP; omega)⟩⟩)
      (fun a _ ⟨hPn, hN⟩ => ((hPnIff a).mp hPn).elim (fun hA => False.elim (hN hA)) fun h' => (congrArg (pointsTo8ProtNone a) (h'.elim (fun ⟨gp, hgp, haG⟩ => hBvPnAg gp (Or.inl hgp) a haG) (fun ⟨p, hp, haP⟩ => hBvPnAg p (Or.inr hp) a haP))).symm)
  exact ⟨⟨hApLo, hApMod, hApFit⟩, hMB, hWf', hGrpPost, by rw [hExPn, hApRead0, hPnRest], hBm.1, hBm.2, SetSep_congr (fun a _ => hMappedIff a) (fun _ _ _ => rfl)⟩

theorem slowPathB1_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hInflight : inflight ≤ 7) (h0 : st.ctx.initDone = 0#32) (sec : BitVec 64) (hFit : (brkStart + 8192#64).toNat ≤ 2 ^ 48) :
    let ap := brkStart + 4096#64; let brk' := brkStart + 8192#64
    let st' : MallocngSt := { st with
      ctx := { st.ctx with secret := sec, initDone := 1#32, availMeta := ap + 64#64, availMetaCount := 100#64, metaAreaHead := ap, metaAreaTail := ap, availMetaAreas := ap + 4096#64, brk := brk' },
      metaAreas := [{ base := ap, next := 0#64 }], guardPages := [brkStart], bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)),
      reservedMetas := (ap + 24#64) :: st.reservedMetas, masterDom := rangeAddrs brkStart 8192, byteVal := writeBytesToMap (fun _ => 0#8) ap (metaHdrBytes sec 0#64) }
    (brk = brkStart ∧ 65536 ≤ brkStart.toNat ∧ 4096 ∣ brkStart.toNat ∧ brkStart.toNat + 8192 ≤ 2 ^ 48) ∧ ((ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas) ∧
    MallocngWFInflight (inflight + 1) base brkStart brk' liveCost peakCost st' ∧ (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = emp ∧ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = emp ∧ ((ap ↦ₛ metaHdrBytes sec 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8)) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    (brkStart ↦ₙ List.replicate 4096 0#8) = ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  intro ap brk' st'; obtain ⟨hCtx0, hMa0, hMma0, hGp0, hMgp0, hAv0, hFm0, hBm0, hRm0, hGs0, hDom0, hBrk0⟩ := hwf.initZero_wf h0
  have hFmHd0 : st.ctx.freeMetaHead = 0#64 := by rw [hCtx0]; rfl
  have hAvCnt0 : st.ctx.availMetaAreaCount = 0#64 := by rw [hCtx0]; rfl
  have hShift0 : st.ctx.metaAllocShift = 0#64 := by rw [hCtx0]; rfl
  have ⟨hBrkGe, hBrkMod, _, _, hBrkFit0⟩ := hwf.brk_bounds
  have hBrk8Nat : brk'.toNat = brkStart.toNat + 8192 := (by dsimp only [brk']; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hApNat : ap.toNat = brkStart.toNat + 4096 := (by dsimp only [ap]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hFitN : brkStart.toNat + 8192 ≤ 2 ^ 48 := hBrk8Nat ▸ hFit
  have hDomEq : st'.masterDom = rangeAddrs brkStart 8192 := by dsimp only [st']
  have hDomNd0 : (rangeAddrs brkStart 8192).Nodup := nodup_rangeAddrs brkStart (n := 8192) (by omega)
  have hDomNd : st'.masterDom.Nodup := by rw [hDomEq]; exact hDomNd0
  have hSub8192 : ∀ a : BitVec 64, (InRegion brkStart 4096 a ∨ InRegion ap 4096 a) → a ∈ st'.masterDom := fun a h => by rw [hDomEq]; exact (mem_rangeAddrs_iff_inRegion brkStart (n := 8192) (by omega) a).mpr ((inRegion_toNat (by omega)).mpr (h.elim (fun h1 => by have := (inRegion_toNat (by omega)).mp h1; omega) (fun h2 => by have := (inRegion_toNat (by omega)).mp h2; omega)))
  obtain ⟨hMB, hWf', hGrpPost⟩ := activate_metaArea_wf (st' := st') (brk' := brk') (ap := ap) (bv0 := fun _ => 0#8) hwf hInflight hFm0 hBm0 ⟨by omega, by omega, by omega⟩ ⟨by simp [hMa0], fun _ hg => by rw [hGs0] at hg; cases hg⟩ (fun _ hma => by rw [hMa0] at hma; cases hma) (fun _ hg => by rw [hGs0] at hg; cases hg) (fun _ _ => rfl)
    (by dsimp only [st']; simp [hMa0]) (by change [{ base := ap, next := 0#64 }] = appendMetaArea st.metaAreas ap; simp [hMa0, appendMetaArea]) hFm0 rfl rfl ⟨rfl, rfl, rfl⟩
    ⟨rfl, hFmHd0, rfl, rfl, by change ap = match st.metaAreas with | [] => ap | hd :: _ => hd.base; simp [hMa0], rfl, fun hne => False.elim (hne hMa0), rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨hBrkGe, hBrkMod, by omega, by omega, hFit⟩
    ⟨fun _ => ⟨rfl, by omega, hAvCnt0, hShift0, hAv0⟩,
     by have : InRegion brkStart (brk'.toNat - brkStart.toNat) ap := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩; change st.mmapMetaAreas = ([{ base := ap, next := 0#64 }].map MetaAreaDesc.base).filter _; simp [hMma0, this],
     by have : InRegion brkStart (brk'.toNat - brkStart.toNat) brkStart := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩; change st.mmapGuardPages = [brkStart].filter _; simp [hMgp0, this],
     fun _ => ⟨List.Mem.head _, fun k hk1 hk2 => ⟨{ base := ap, next := 0#64 }, List.Mem.head _, by have hkEq : k = 1 := (by omega); subst hkEq; simp [ap, Nat.mul_one]⟩⟩⟩
    ⟨List.Pairwise.cons nofun List.Pairwise.nil, fun gp hgp => by change gp ∈ [brkStart] at hgp; simp at hgp; subst hgp; exact ⟨by omega, hBrkMod, by omega⟩,
     by change st.availMetaPages = List.map _ (List.range st.ctx.availMetaAreaCount.toNat); simp [hAv0, hAvCnt0], fun _ hp => by rw [show st'.availMetaPages = [] from hAv0] at hp; cases hp⟩
    (by unfold dynamicRootRegions; rw [show st'.metaAreas = [{ base := ap, next := 0#64 }] from rfl, show st'.guardPages = [brkStart] from rfl, show st'.availMetaPages = [] from hAv0, show st'.groups = [] from hGs0]; simp only [List.filter_nil, List.map_nil, List.append_nil, List.map_cons, List.cons_append, List.nil_append, PairwiseDisjointRegions, List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact ⟨disjointRegions_of_nat_bounds (by omega) (by omega) (by omega) (by omega) (by omega), ⟨nofun, trivial⟩⟩)
    ⟨fun _ => ⟨hAv0, by change [brkStart].length ≤ 1; simp⟩, fun m hm1 hmEq => by change st.ctx.metaAllocShift.toNat = m at hmEq; rw [hShift0] at hmEq; simp at hmEq; omega⟩
    ⟨hDomNd, fun a h => hSub8192 a (by rcases h with hRw | hPn | hMp; exact hRw.1.elim (fun ⟨ma, hma, ha⟩ => by change ma ∈ [{ base := ap, next := 0#64 }] at hma; simp only [List.mem_singleton] at hma; subst hma; exact Or.inr ha) (fun ⟨_, hg, _⟩ => by rw [show st'.groups = [] from hGs0] at hg; cases hg); exact hPn.elim (fun ⟨gp, hgp, ha⟩ => by change gp ∈ [brkStart] at hgp; simp only [List.mem_singleton] at hgp; subst hgp; exact Or.inl ha) (fun ⟨_, hp, _⟩ => by rw [show st'.availMetaPages = [] from hAv0] at hp; cases hp); (unfold OwnedMappedByte at hMp; rw [show st'.mmapMetaAreas = [] from hMma0, show st'.mmapGuardPages = [] from hMgp0, show st'.availMetaPages = [] from hAv0, show st'.groups = [] from hGs0] at hMp; simp at hMp)),
      fun a ha => by
        rw [hDomEq] at ha
        have haN := (inRegion_toNat (by omega)).mp ((mem_rangeAddrs_iff_inRegion brkStart (n := 8192) (by omega) a).mp ha); clear ha; unfold dynamicRootRegions; rw [show st'.metaAreas = [{ base := ap, next := 0#64 }] from rfl, show st'.guardPages = [brkStart] from rfl, show st'.availMetaPages = [] from hAv0, show st'.groups = [] from hGs0]; simp only [List.filter_nil, List.map_nil, List.append_nil, List.map_cons, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
        exact if hLt : a.toNat < brkStart.toNat + 4096 then ⟨(brkStart, 4096), Or.inr rfl, (inRegion_toNat (b := brkStart) (n := 4096) (by omega)).mpr ⟨by omega, hLt⟩⟩ else ⟨(ap, 4096), Or.inl rfl, (inRegion_toNat (b := ap) (n := 4096) (by omega)).mpr ⟨by omega, by omega⟩⟩⟩
  have hBm := (activate_metaArea_bytemap (bv0 := fun _ => 0#8) hwf hWf' ⟨by omega, by omega, by omega⟩ ⟨by simp [hMa0], fun _ hg => by rw [hGs0] at hg; cases hg⟩ (fun _ hma => by rw [hMa0] at hma; cases hma) (fun _ _ => rfl) (by dsimp only [st']; simp [hMa0]) (by change [{ base := ap, next := 0#64 }] = appendMetaArea st.metaAreas ap; simp [hMa0, appendMetaArea]) rfl rfl).2
  have hRw0Emp : ByteMap st'.masterDom (OwnedRwByte st) (if hne : st.metaAreas ≠ [] then writeBytesToMap (fun _ => 0#8) (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else fun _ => 0#8) = emp := SetSep_empty _ fun _ _ ⟨hL, _⟩ => hL.elim (fun ⟨_, hm, _⟩ => by rw [hMa0] at hm; cases hm) (fun ⟨_, hg, _⟩ => by rw [hGs0] at hg; cases hg)
  have hPnRead : readBytesFromMap st'.byteVal brkStart 4096 = List.replicate 4096 0#8 := by
    have hZ : ∀ n b, readBytesFromMap (fun _ => 0#8) b n = List.replicate n 0#8 := fun n => by induction n with | zero => intro _; rfl | succ n ih => intro b; rw [readBytesFromMap_succ, ih]; rfl
    rw [← hZ 4096 brkStart]; exact readBytesFromMap_congr (n := 4096) (by omega) fun a ha => writeBytesToMap_out (fun _ => 0#8) ap (metaHdrBytes sec 0#64) fun hIn => by rw [metaHdrBytes_length] at hIn; have := (inRegion_toNat (by omega)).mp ha; have := (inRegion_toNat (by omega)).mp hIn; omega
  have hExPn := ProtNoneByteMap_extract_slice hDomNd (keep := OwnedProtNoneByte st') st'.byteVal brkStart (n := 4096) (by omega) (fun a ha => hSub8192 a (Or.inl ha)) (fun a ha => Or.inl ⟨brkStart, List.Mem.head _, ha⟩)
  have hPnRem : ProtNoneByteMap st'.masterDom (fun a => OwnedProtNoneByte st' a ∧ ¬ InRegion brkStart 4096 a) st'.byteVal = emp := SetSep_empty _ fun _ _ ⟨hP, hN⟩ => hP.elim (fun ⟨gp, hgp, ha⟩ => by change gp ∈ [brkStart] at hgp; simp only [List.mem_singleton] at hgp; subst hgp; exact hN ha) (fun ⟨_, hp, _⟩ => by rw [show st'.availMetaPages = [] from hAv0] at hp; cases hp)
  have hMpEmp : MappedSet st'.masterDom (OwnedMappedByte st') = emp := SetSep_empty _ fun _ _ hM => by unfold OwnedMappedByte at hM; rw [show st'.mmapMetaAreas = [] from hMma0, show st'.mmapGuardPages = [] from hMgp0, show st'.availMetaPages = [] from hAv0, show st'.groups = [] from hGs0] at hM; simp at hM
  simp only [hMa0, ne_eq, not_true_eq_false, ↓reduceDIte] at hBm hRw0Emp
  exact ⟨⟨hBrk0, by omega, Nat.dvd_of_mod_eq_zero hBrkMod, hFitN⟩, hMB, hWf', hGrpPost, by simp [ByteMap, SetSep, hDom0], by simp [ProtNoneByteMap, SetSep, hDom0], by rw [hRw0Emp, sepConj_emp] at hBm; exact hBm, by rw [hExPn, hPnRead, hPnRem, sepConj_emp], by rw [hMpEmp]; simp [MappedSet, SetSep, hDom0]⟩

theorem slowPathB2_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hInflight : inflight ≤ 7) (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hBrkNe : st.ctx.brk ≠ -1#64) (hFit : (brk + 4096#64).toNat ≤ 2 ^ 48) (hDisjNew : ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 brk 4096) :
    let brk' := brk + 4096#64; let bv0 := writeBytesToMap st.byteVal brk (List.replicate 4096 0#8); let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret brk) else bv0
    let st' : MallocngSt := { st with
      ctx := { st.ctx with availMeta := brk + 64#64, availMetaCount := 100#64, availMetaAreaCount := 0#64, metaAreaHead := (match st.metaAreas with | [] => brk | hd :: _ => hd.base), metaAreaTail := brk, availMetaAreas := brk', brk := brk' },
      metaAreas := appendMetaArea st.metaAreas brk, freeMetas := [], bumpMetas := (List.range 100).map (fun j => ({ base := brk, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (brk + 24#64) :: st.reservedMetas, masterDom := st.masterDom ++ rangeAddrs brk 4096, byteVal := writeBytesToMap bv1 brk (metaHdrBytes st.ctx.secret 0#64) }
    (st.ctx.brk = brk ∧ brk ≠ 0#64 ∧ 4096 ∣ brk.toNat ∧ brk.toNat + 4096 ≤ 2 ^ 48) ∧ ((brk + 24#64) ≠ 0#64 ∧ 4096 ≤ (brk + 24#64).toNat ∧ (brk + 24#64).toNat % 8 = 0 ∧ (brk + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (brk + 24#64) ∉ st.reservedMetas) ∧
    MallocngWFInflight (inflight + 1) base brkStart brk' liveCost peakCost st' ∧ (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    (∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base; ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧ ((tb ↦ₛ metaHdrBytes st.ctx.secret brk) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1) ∧
    ByteMap st'.masterDom (OwnedRwByte st) bv0 = ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∧ ((brk ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ((brk + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧ MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by
  intro brk' bv0 bv1 st'; obtain ⟨hCtxBrk, hBrkGe8, hAvCnt0, hShift0, hAv0⟩ := hwf.brk_mode_wf.1 ⟨h1, hBrkNe⟩; have ⟨hBrkGe, hBrkSMod, hBrkMod, hBrkLe, hBrkFit0⟩ := hwf.brk_bounds
  have hBrk'Nat : brk'.toNat = brk.toNat + 4096 := (by dsimp only [brk']; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hFitN : brk.toNat + 4096 ≤ 2 ^ 48 := hBrk'Nat ▸ hFit; obtain ⟨hMapBase, hMaLen, _, _⟩ := appendMetaArea_props st.metaAreas brk
  have hDisjDom : ∀ a ∈ st.masterDom, ¬ InRegion brk 4096 a := fun a ha hInB => by obtain ⟨r, hr, hInR⟩ := hwf.masterDom_wf.2.2 a ha; have hDR := hDisjNew r hr; unfold DisjointRegions at hDR; unfold InRegion at hInR hInB; have := BitVec.toNat_sub brk r.1; have := BitVec.toNat_sub r.1 brk; have := BitVec.toNat_sub a r.1; have := BitVec.toNat_sub a brk; omega
  have hBrk64Nat : (brk + 64#64).toNat = brk.toNat + 64 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have hDomNd : st'.masterDom.Nodup := List.nodup_append.mpr ⟨hwf.masterDom_wf.1, nodup_rangeAddrs brk (n := 4096) (by omega), fun x hx y hy hEq => hDisjDom x hx (hEq ▸ (mem_rangeAddrs_iff_inRegion brk (n := 4096) (by omega) y).mp hy)⟩
  have hBv0Out : ∀ r ∈ dynamicRootRegions st, ∀ a : BitVec 64, InRegion r.1 r.2 a → bv0 a = st.byteVal a := fun r hr a ha => writeBytesToMap_out _ _ _ fun hInB => by rw [List.length_replicate] at hInB; have hDR := hDisjNew r hr; unfold DisjointRegions at hDR; unfold InRegion at ha hInB; have := BitVec.toNat_sub brk r.1; have := BitVec.toNat_sub r.1 brk; have := BitVec.toNat_sub a r.1; have := BitVec.toNat_sub a brk; omega
  have hMaDisj : ∀ ma ∈ st.metaAreas, DisjointRegions ma.base 4096 brk 4096 := fun ma hma => hDisjNew (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))))
  have hGpDisj : ∀ gp ∈ st.guardPages, DisjointRegions gp 4096 brk 4096 := fun gp hgp => hDisjNew (gp, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))))
  have hRgDisj : ∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions brk 4096 g.mem (g.maplen * 4096) := fun g hg hml => let h := hDisjNew (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))); ⟨h.2, h.1⟩
  have hBrkNotMa : brk ∉ st.metaAreas.map (·.base) := fun hm => by obtain ⟨ma, hma, hEq⟩ := List.mem_map.mp hm; have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.metaAreas_wf.2.1 ma hma).2.2.1 hFitN (hMaDisj ma hma); have := congrArg BitVec.toNat hEq; omega
  have hMapMaPair : st'.metaAreas.map (fun ma => (ma.base, 4096)) = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(brk, 4096)] := by
    calc st'.metaAreas.map (fun ma => (ma.base, 4096)) = ((appendMetaArea st.metaAreas brk).map MetaAreaDesc.base).map (fun b => (b, 4096)) := by dsimp only [st']; rw [List.map_map]; rfl
      _ = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(brk, 4096)] := by rw [hMapBase, List.map_append, List.map_map]; rfl
  have hFmHd0 : st.ctx.freeMetaHead = 0#64 := (by have h := hwf.free_bump_metas_wf.1; simp [hNoFree] at h; exact h)
  have hBv0Zero : ∀ a : BitVec 64, InRegion brk 4096 a → bv0 a = 0#8 := fun a ha => by have haN := (inRegion_toNat (by omega)).mp ha; have haEq : a = brk + BitVec.ofNat 64 (a.toNat - brk.toNat) := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); dsimp only [bv0]; rw [haEq, writeBytesToMap_in st.byteVal brk (List.replicate 4096 0#8) (by rw [List.length_replicate]; omega) (by rw [List.length_replicate]; omega), List.getElem_replicate]
  have hBv0Zero64 : ∀ a : BitVec 64, InRegion (brk + 64#64) 4032 a → bv0 a = 0#8 := fun a ha => by have := (inRegion_toNat (by omega)).mp ha; exact hBv0Zero a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)
  have hInBrkCongr : ∀ p : BitVec 64, p.toNat + 4096 ≤ 2 ^ 48 → DisjointRegions p 4096 brk 4096 → InRegion brkStart (brk'.toNat - brkStart.toNat) p = InRegion brkStart (brk.toNat - brkStart.toNat) p :=
    fun p hpFit hD => propext ⟨fun h => by have := nat_sep_of_disjointRegions (by omega) (by omega) hpFit hFitN hD; have := (inRegion_toNat (by omega)).mp h; exact (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩, fun h => by have := (inRegion_toNat (by omega)).mp h; exact (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩⟩
  have hMmaEq : st.mmapMetaAreas = ((appendMetaArea st.metaAreas brk).map (·.base)).filter (fun mb => !decide (InRegion brkStart (brk'.toNat - brkStart.toNat) mb)) := by
    have hInSelf : InRegion brkStart (brk'.toNat - brkStart.toNat) brk := (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩
    rw [hMapBase, List.filter_append, hwf.brk_mode_wf.2.1]; simp only [List.filter_cons, hInSelf, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
    exact List.filter_congr fun mb hmb => by obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hmb; simp [hInBrkCongr ma.base (hwf.metaAreas_wf.2.1 ma hma).2.2.1 (hMaDisj ma hma)]
  have hMgpEq : st.mmapGuardPages = st.guardPages.filter (fun gp => !decide (InRegion brkStart (brk'.toNat - brkStart.toNat) gp)) := by rw [hwf.brk_mode_wf.2.2.1]; exact List.filter_congr fun gp hgp => by simp [hInBrkCongr gp (hwf.guard_avail_wf.2.1 gp hgp).2.2 (hGpDisj gp hgp)]
  have hPd' : PairwiseDisjointRegions (dynamicRootRegions st') := by
    have hPd0 := hwf.regions_disjoint.1; unfold dynamicRootRegions at hPd0 ⊢; rw [List.append_assoc, List.append_assoc] at hPd0 ⊢; obtain ⟨hPdMa, hPdRest, hCross⟩ := pairwiseDisjoint_append_iff.mp hPd0
    rw [hMapMaPair, show st'.guardPages = st.guardPages from rfl, show st'.availMetaPages = st.availMetaPages from rfl, show st'.groups = st.groups from rfl]
    refine pairwiseDisjoint_append_iff.mpr ⟨pairwiseDisjoint_append_iff.mpr ⟨hPdMa, by simp [PairwiseDisjointRegions], fun x hx y hy => by obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hx; simp at hy; subst hy; exact hMaDisj ma hma⟩, hPdRest, fun x hx y hy => ?_⟩
    exact (List.mem_append.mp hx).elim (fun hxMa => hCross x hxMa y hy) fun hxB => by simp at hxB; subst hxB; have h := hDisjNew y (by unfold dynamicRootRegions; rw [List.append_assoc, List.append_assoc]; exact List.mem_append_right _ hy); exact ⟨h.2, h.1⟩
  have hBvPn : ∀ gp ∈ st.guardPages, ∀ a : BitVec 64, InRegion gp 4096 a → st'.byteVal a = st.byteVal a := fun gp hgp a ha => by
    have hgpB := hwf.guard_avail_wf.2.1 gp hgp; have haN := (inRegion_toNat (by omega)).mp ha; have hSepB := nat_sep_of_disjointRegions (by omega) (by omega) hgpB.2.2 hFitN (hGpDisj gp hgp)
    dsimp only [st']; rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have := (inRegion_toNat (by omega)).mp h; omega)]; dsimp only [bv1]; split
    · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne); have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff] at hpd
      have hSepT := nat_sep_of_disjointRegions (by omega) (by omega) htb.2.2.1 hgpB.2.2 (hpd.2.2 _ (List.mem_map_of_mem (List.getLast_mem hne)) _ (List.mem_append_left _ (List.mem_map_of_mem hgp)))
      rw [writeBytesToMap_out _ _ _ (fun h => by rw [metaHdrBytes_length] at h; have := (inRegion_toNat (by omega)).mp h; omega)]
      exact hBv0Out (gp, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp)))) a ha
    · exact hBv0Out (gp, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp)))) a ha
  obtain ⟨hMB, hWf', hGrpPost⟩ := activate_metaArea_wf (st' := st') (brk' := brk') (ap := brk) (bv0 := bv0) hwf hInflight hNoFree hNoBump ⟨by omega, hBrkMod, hFitN⟩ ⟨hBrkNotMa, hRgDisj⟩
    (fun ma hma a ha => hBv0Out (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))) a ha)
    (fun g hg hml a ha => hBv0Out (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))) a ha)
    hBv0Zero64 rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩ ⟨h1, hFmHd0, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨hBrkGe, hBrkSMod, by omega, by omega, hFit⟩
    ⟨fun _ => ⟨rfl, by omega, rfl, hShift0, hAv0⟩, hMmaEq, hMgpEq, fun _ => by
      obtain ⟨hGpBrk, hMaBrk⟩ := hwf.brk_mode_wf.2.2.2 (by omega); refine ⟨hGpBrk, fun k hk1 hk2 => ?_⟩; by_cases hkLast : k = (brk.toNat - brkStart.toNat) / 4096
      · subst hkLast; obtain ⟨ma', hma', hEq'⟩ := List.mem_map.mp (show brk ∈ st'.metaAreas.map (·.base) by change brk ∈ (appendMetaArea st.metaAreas brk).map (·.base); rw [hMapBase]; simp); exact ⟨ma', hma', hEq'.trans (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))⟩
      · obtain ⟨ma, hma, hEq⟩ := hMaBrk k hk1 (by omega); obtain ⟨ma', hma', hEq'⟩ := List.mem_map.mp (show ma.base ∈ st'.metaAreas.map (·.base) by change ma.base ∈ (appendMetaArea st.metaAreas brk).map (·.base); rw [hMapBase]; exact List.mem_append_left _ (List.mem_map_of_mem hma)); exact ⟨ma', hma', hEq'.trans hEq⟩⟩
    ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, by change st.availMetaPages = List.map _ (List.range 0); simp [hAv0], fun p hp => by rw [show st'.availMetaPages = [] from hAv0] at hp; cases hp⟩
    hPd'
    ⟨fun _ => ⟨hAv0, (hwf.meta_pages_bound.2.1 hShift0).2⟩, fun m hm1 hmEq => by change st.ctx.metaAllocShift.toNat = m at hmEq; rw [hShift0] at hmEq; simp at hmEq; omega⟩
    ⟨hDomNd, fun a h => by
        have hNoM0 : ¬ CarvedMetaByte st' a → ¬ CarvedMetaByte st a := fun hN ⟨mr, hmr, hIn⟩ => hN ⟨mr, List.Mem.tail _ hmr, hIn⟩; rcases h with hRw | hPn | hMp
        · exact hRw.1.elim (fun ⟨ma, hma, ha⟩ => (List.mem_append.mp (show ma.base ∈ st.metaAreas.map (·.base) ++ [brk] by rw [← hMapBase]; exact List.mem_map_of_mem hma)).elim
            (fun hO => by obtain ⟨m0, hm0, hE⟩ := List.mem_map.mp hO; exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inl ⟨Or.inl ⟨m0, hm0, hE ▸ ha⟩, hRw.2.1, hNoM0 hRw.2.2⟩)))
            (fun hB => by simp at hB; rw [hB] at ha; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion brk (n := 4096) (by omega) a).mpr ha)))
            (fun hRg => List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inl ⟨Or.inr hRg, hRw.2.1, hNoM0 hRw.2.2⟩)))
        · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn)))
        · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp))),
      fun a ha => (List.mem_append.mp ha).elim (fun haOld => by obtain ⟨r, hr, hIn⟩ := hwf.masterDom_wf.2.2 a haOld; refine ⟨r, ?_, hIn⟩; unfold dynamicRootRegions at hr ⊢; rw [hMapMaPair]; simp only [show st'.guardPages = st.guardPages from rfl, show st'.availMetaPages = st.availMetaPages from rfl, show st'.groups = st.groups from rfl, List.mem_append] at hr ⊢; rcases hr with ((h | h) | h) | h <;> simp [h])
        (fun haNew => ⟨(brk, 4096), by unfold dynamicRootRegions; rw [hMapMaPair]; simp, (mem_rangeAddrs_iff_inRegion brk (n := 4096) (by omega) a).mp haNew⟩)⟩
  have hBm := activate_metaArea_bytemap hwf hWf' ⟨by omega, hBrkMod, hFitN⟩ ⟨hBrkNotMa, hRgDisj⟩ (fun ma hma a ha => hBv0Out (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))) a ha) hBv0Zero64 rfl rfl rfl rfl
  have hRw0Dom : ByteMap st'.masterDom (OwnedRwByte st) bv0 = ByteMap st.masterDom (OwnedRwByte st) st.byteVal := by
    unfold ByteMap; rw [SetSep_append_right_empty _ (fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inl h)) ((mem_rangeAddrs_iff_inRegion brk (n := 4096) (by omega) a).mp ha))]
    exact SetSep_congr (fun _ _ => Iff.rfl) fun a _ h => congrArg (pointsTo8 a) (h.1.elim (fun ⟨ma, hma, ha⟩ => hBv0Out (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))) a ha) (fun ⟨g, hg, hml, ha⟩ => hBv0Out (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))) a ha))
  have hPnEq : ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    change SetSep (st.masterDom ++ rangeAddrs brk 4096) (OwnedProtNoneByte st) (fun a => a ↦₈ₙ st'.byteVal a) = SetSep st.masterDom (OwnedProtNoneByte st) (fun a => a ↦₈ₙ st.byteVal a)
    rw [SetSep_append_right_empty _ (fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl h))) ((mem_rangeAddrs_iff_inRegion brk (n := 4096) (by omega) a).mp ha))]
    exact SetSep_congr (fun _ _ => Iff.rfl) fun a _ h => congrArg (pointsTo8ProtNone a) (h.elim (fun ⟨gp, hgp, ha⟩ => hBvPn gp hgp a ha) (fun ⟨_, hp, _⟩ => by rw [hAv0] at hp; cases hp))
  have hMpEq : MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := by unfold MappedSet; exact SetSep_append_right_empty _ fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr h))) ((mem_rangeAddrs_iff_inRegion brk (n := 4096) (by omega) a).mp ha)
  exact ⟨⟨hCtxBrk, fun h => by rw [h] at hBrkGe8; simp at hBrkGe8, Nat.dvd_of_mod_eq_zero hBrkMod, hFitN⟩, hMB, hWf', hGrpPost, hBm.1, hRw0Dom, hBm.2, hPnEq, hMpEq⟩

theorem slowPathC_trans {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hInflight : inflight ≤ 7) (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = []) (hCnt0 : st.ctx.availMetaAreaCount = 0#64) (hBrkNeg1 : st.ctx.brk = -1#64)
    (mb : BitVec 64) (hMbNe0 : mb ≠ 0#64) (hMbAlign : 4096 ∣ mb.toNat) (hMbFit : mb.toNat + 4096 * 2 ^ (st.ctx.metaAllocShift.toNat + 1) ≤ 2 ^ 48)
    (hDisjRoot : ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 mb (4096 * 2 ^ (st.ctx.metaAllocShift.toNat + 1))) :
    let m := st.ctx.metaAllocShift.toNat; let len := 4096 * 2 ^ (m + 1); let ap := mb + 4096#64; let cnt' := BitVec.ofNat 64 (2 ^ (m + 1) - 2); let newAv := (List.range (2 ^ (m + 1) - 2)).map (fun i => (ap + 4096#64) + BitVec.ofNat 64 (4096 * i))
    let bv0 := writeBytesToMap st.byteVal mb (List.replicate len 0#8); let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0
    let st' : MallocngSt := { st with
      ctx := { st.ctx with availMeta := ap + 64#64, availMetaCount := 100#64, availMetaAreaCount := cnt', metaAllocShift := BitVec.ofNat 64 (m + 1), metaAreaHead := (match st.metaAreas with | [] => ap | hd :: _ => hd.base), metaAreaTail := ap, availMetaAreas := ap + 4096#64 },
      metaAreas := appendMetaArea st.metaAreas ap, mmapMetaAreas := st.mmapMetaAreas ++ [ap], guardPages := st.guardPages ++ [mb], mmapGuardPages := st.mmapGuardPages ++ [mb], availMetaPages := newAv, freeMetas := [],
      bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (ap + 24#64) :: st.reservedMetas, masterDom := st.masterDom ++ rangeAddrs mb len, byteVal := writeBytesToMap bv1 ap (metaHdrBytes st.ctx.secret 0#64) }
    ((ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas) ∧ MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st' ∧
    (∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
    ((mb ↦ₙ List.replicate len 0#8) ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) ∧
    (∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base; ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧ ((tb ↦ₛ metaHdrBytes st.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1) ∧
    ByteMap st'.masterDom (OwnedRwByte st) bv0 = ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∧ ((ap ↦ₛ metaHdrBytes st.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    (memMapped mb len ∗ MappedSet st.masterDom (OwnedMappedByte st)) = MappedSet st'.masterDom (OwnedMappedByte st') := by
  intro m len ap cnt' newAv bv0 bv1 st'; have hAv0 : st.availMetaPages = [] := (by have h := hwf.guard_avail_wf.2.2.1; rw [hCnt0] at h; exact h)
  obtain ⟨hmLe35, hLenGe0, hLenLe480, _, _⟩ := slowPathC_prep_bounds hwf hInflight hNoFree hNoBump hAv0; have hmDef : m = st.ctx.metaAllocShift.toNat := rfl; have hLenDef : len = 4096 * 2 ^ (m + 1) := rfl; rw [← hmDef, ← hLenDef] at hMbFit hDisjRoot
  have hLenGe : 8192 ≤ len := hLenGe0; have hLenLe48 : len ≤ 2 ^ 48 := hLenLe480; have hMbLenFit : mb.toNat + len ≤ 2 ^ 48 := hMbFit
  have hPowGe2 : 2 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) (by omega); have hPowLe36 : 2 ^ (m + 1) ≤ 2 ^ 36 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  have hMbPos : 0 < mb.toNat := Nat.pos_of_ne_zero fun h0 => hMbNe0 (BitVec.eq_of_toNat_eq h0); have hMbMod : mb.toNat % 4096 = 0 := Nat.mod_eq_zero_of_dvd hMbAlign; have hMbLo : 4096 ≤ mb.toNat := (by omega)
  have hApNat : ap.toNat = mb.toNat + 4096 := (by dsimp only [ap]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hAp4096Nat : (ap + 4096#64).toNat = mb.toNat + 8192 := (by rw [BitVec.toNat_add, hApNat, BitVec.toNat_ofNat]; omega)
  have hAp64Nat : (ap + 64#64).toNat = ap.toNat + 64 := (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); have hCnt'Nat : cnt'.toNat = 2 ^ (m + 1) - 2 := (by dsimp only [cnt']; rw [BitVec.toNat_ofNat]; omega)
  have hAvPNat : ∀ p ∈ newAv, ∃ i < 2 ^ (m + 1) - 2, p.toNat = mb.toNat + 8192 + 4096 * i := fun p hp => by obtain ⟨i, hiR, rfl⟩ := List.mem_map.mp hp; refine ⟨i, List.mem_range.mp hiR, ?_⟩; rw [BitVec.toNat_add, hAp4096Nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := List.mem_range.mp hiR; omega)]; have := List.mem_range.mp hiR; omega
  have hSubPage : ∀ b : BitVec 64, mb.toNat ≤ b.toNat → b.toNat + 4096 ≤ mb.toNat + len → ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 b 4096 ∧ DisjointRegions b 4096 r.1 r.2 := fun b hbLo hbHi r hr => by
    have hD := hDisjRoot r hr; unfold DisjointRegions at hD ⊢; have := BitVec.toNat_sub mb r.1; have := BitVec.toNat_sub r.1 mb; have := BitVec.toNat_sub b r.1; have := BitVec.toNat_sub r.1 b; exact ⟨by omega, by omega⟩
  have hDisjDom : ∀ a ∈ st.masterDom, ¬ InRegion mb len a := fun a ha hInM => by obtain ⟨r, hr, hInR⟩ := hwf.masterDom_wf.2.2 a ha; have hD := hDisjRoot r hr; unfold DisjointRegions at hD; unfold InRegion at hInR hInM; have := BitVec.toNat_sub mb r.1; have := BitVec.toNat_sub r.1 mb; have := BitVec.toNat_sub a r.1; have := BitVec.toNat_sub a mb; omega
  have hDomNd : st'.masterDom.Nodup := List.nodup_append.mpr ⟨hwf.masterDom_wf.1, nodup_rangeAddrs mb (n := len) (by omega), fun x hx y hy hEq => hDisjDom x hx (hEq ▸ (mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) y).mp hy)⟩
  have hBv0Out : ∀ r ∈ dynamicRootRegions st, ∀ a : BitVec 64, InRegion r.1 r.2 a → bv0 a = st.byteVal a := fun r hr a ha => writeBytesToMap_out _ _ _ fun hInM => by rw [List.length_replicate] at hInM; have hD := hDisjRoot r hr; unfold DisjointRegions at hD; unfold InRegion at ha hInM; have := BitVec.toNat_sub mb r.1; have := BitVec.toNat_sub r.1 mb; have := BitVec.toNat_sub a r.1; have := BitVec.toNat_sub a mb; omega
  have hBv0Zero : ∀ a : BitVec 64, InRegion mb len a → bv0 a = 0#8 := fun a ha => by have haN := (inRegion_toNat (by omega)).mp ha; have haEq : a = mb + BitVec.ofNat 64 (a.toNat - mb.toNat) := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega); dsimp only [bv0]; rw [haEq, writeBytesToMap_in st.byteVal mb (List.replicate len 0#8) (by rw [List.length_replicate]; omega) (by rw [List.length_replicate]; omega), List.getElem_replicate]
  have hPartMb : ∀ a : BitVec 64, InRegion mb len a ↔ (InRegion mb 4096 a ∨ InRegion ap 4096 a ∨ ∃ p ∈ newAv, InRegion p 4096 a) := fun a =>
    ⟨fun ha => by
      have haN := (inRegion_toNat (by omega)).mp ha; let q := (a.toNat - mb.toNat) / 4096; have hqLt : q < 2 ^ (m + 1) := (by dsimp only [q]; omega)
      by_cases hq0 : q = 0; · exact Or.inl ((inRegion_toNat (by omega)).mpr ⟨by omega, by dsimp only [q] at hq0; omega⟩)
      · by_cases hq1 : q = 1; · exact Or.inr (Or.inl ((inRegion_toNat (by omega)).mpr ⟨by dsimp only [q] at hq1; omega, by dsimp only [q] at hq1; omega⟩))
        · refine Or.inr (Or.inr ⟨(ap + 4096#64) + BitVec.ofNat 64 (4096 * (q - 2)), List.mem_map_of_mem (List.mem_range.mpr (by omega)), ?_⟩)
          have hpN : ((ap + 4096#64) + BitVec.ofNat 64 (4096 * (q - 2))).toNat = mb.toNat + 4096 * q := (by rw [BitVec.toNat_add, hAp4096Nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega); exact (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩,
     fun h => h.elim (fun h0 => by have := (inRegion_toNat (by omega)).mp h0; exact (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩) (fun h12 => h12.elim (fun h1 => by have := (inRegion_toNat (by omega)).mp h1; exact (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩) (fun ⟨p, hp, hpA⟩ => by obtain ⟨i, hi, hpN⟩ := hAvPNat p hp; have := (inRegion_toNat (by omega)).mp hpA; exact (inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩))⟩
  have ⟨hBrkGe, hBrkSMod, hBrkMod, hBrkLe, hBrkFit⟩ := hwf.brk_bounds
  have hNotBrk : ∀ b : BitVec 64, b.toNat % 4096 = 0 → mb.toNat ≤ b.toNat → b.toNat + 4096 ≤ mb.toNat + len → ¬ InRegion brkStart (brk.toNat - brkStart.toNat) b := fun b hbMod hbLo hbHi hInB => by
    have hInBN := (inRegion_toNat (by omega)).mp hInB; let k := (b.toNat - brkStart.toNat) / 4096; have hbEq : b = brkStart + BitVec.ofNat 64 (4096 * k) := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [k]; omega)]; dsimp only [k]; omega)
    obtain ⟨hGp0, hMaK⟩ := hwf.brk_mode_wf.2.2.2 (by omega); by_cases hk0 : k = 0
    · have hbS : b = brkStart := (by rw [hbEq, hk0, Nat.mul_zero]; exact BitVec.add_zero brkStart); have := nat_sep_of_disjointRegions (a := brkStart) (na := 4096) (b := b) (nb := 4096) (by omega) (by omega) (by omega) (by omega) (hSubPage b hbLo hbHi (brkStart, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hGp0))))).1; have := congrArg BitVec.toNat hbS; omega
    · obtain ⟨ma, hma, hmaEq⟩ := hMaK k (by omega) (by dsimp only [k]; omega); have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.metaAreas_wf.2.1 ma hma).2.2.1 (by omega) (hSubPage b hbLo hbHi (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))))).1; have := congrArg BitVec.toNat (hmaEq.trans hbEq.symm); omega
  obtain ⟨hMapBase, hMaLen, _, _⟩ := appendMetaArea_props st.metaAreas ap
  have hMapMaPair : st'.metaAreas.map (fun ma => (ma.base, 4096)) = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by
    calc st'.metaAreas.map (fun ma => (ma.base, 4096)) = ((appendMetaArea st.metaAreas ap).map MetaAreaDesc.base).map (fun b => (b, 4096)) := by dsimp only [st']; rw [List.map_map]; rfl
      _ = st.metaAreas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by rw [hMapBase, List.map_append, List.map_map]; rfl
  have hApNotMa : ap ∉ st.metaAreas.map (·.base) := fun hm => by
    obtain ⟨ma, hma, hEq⟩ := List.mem_map.mp hm; have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.metaAreas_wf.2.1 ma hma).2.2.1 (by omega) (hSubPage ap (by omega) (by omega) (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))))).1; have := congrArg BitVec.toNat hEq; omega
  have hMbNotGp : mb ∉ st.guardPages := fun hg => by have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.guard_avail_wf.2.1 mb hg).2.2 (by omega) (hSubPage mb (by omega) (by omega) (mb, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hg))))).1; omega
  have hRgDisj : ∀ g ∈ st.groups, 0 < g.maplen → DisjointRegions ap 4096 g.mem (g.maplen * 4096) := fun g hg hml => (hSubPage ap (by omega) (by omega) (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩)))).2
  have hBv0Zero64 : ∀ a : BitVec 64, InRegion (ap + 64#64) 4032 a → bv0 a = 0#8 := fun a ha => by have := (inRegion_toNat (by omega)).mp ha; exact hBv0Zero a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)
  have hZ : ∀ n b, readBytesFromMap (fun _ => 0#8) b n = List.replicate n 0#8 := fun n => by induction n with | zero => intro _; rfl | succ n ih => intro b; rw [readBytesFromMap_succ, ih]; rfl
  have hBvSt'Pn : ∀ b : BitVec 64, (b ∈ st.guardPages ∨ b = mb ∨ b ∈ newAv) → ∀ a : BitVec 64, InRegion b 4096 a → st'.byteVal a = bv0 a := fun b hb a ha => by
    have hbSepAp : b.toNat + 4096 ≤ ap.toNat ∨ ap.toNat + 4096 ≤ b.toNat := by
      rcases hb with hgp | rfl | hp
      · have := nat_sep_of_disjointRegions (by omega) (by omega) (hwf.guard_avail_wf.2.1 b hgp).2.2 (by omega) (hSubPage ap (by omega) (by omega) (b, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))))).1; omega
      · omega
      · obtain ⟨i, _, hpN⟩ := hAvPNat b hp; omega
    have hbFit : b.toNat + 4096 ≤ 2 ^ 48 := by rcases hb with hgp | rfl | hp; exact (hwf.guard_avail_wf.2.1 b hgp).2.2; omega; (obtain ⟨i, hi, hpN⟩ := hAvPNat b hp; omega)
    have haN := (inRegion_toNat (by omega)).mp ha; dsimp only [st']; rw [writeBytesToMap_out bv1 ap (metaHdrBytes st.ctx.secret 0#64) (fun hIn => by rw [metaHdrBytes_length] at hIn; have := (inRegion_toNat (by omega)).mp hIn; omega)]; dsimp only [bv1]; split
    · rename_i hne; have htb := hwf.metaAreas_wf.2.1 _ (List.getLast_mem hne)
      have htbSep : (st.metaAreas.getLast hne).base.toNat + 4096 ≤ b.toNat ∨ b.toNat + 4096 ≤ (st.metaAreas.getLast hne).base.toNat := by
        rcases hb with hgp | rfl | hp
        · have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd; rw [List.append_assoc, List.append_assoc, pairwiseDisjoint_append_iff] at hpd
          exact nat_sep_of_disjointRegions (by omega) (by omega) htb.2.2.1 hbFit (hpd.2.2 _ (List.mem_map_of_mem (List.getLast_mem hne)) (b, 4096) (List.mem_append_left _ (List.mem_map_of_mem hgp)))
        · exact nat_sep_of_disjointRegions (by omega) (by omega) htb.2.2.1 hbFit (hSubPage b (by omega) (by omega) _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (List.getLast_mem hne)))))).1
        · obtain ⟨i, hi, hpN⟩ := hAvPNat b hp; exact nat_sep_of_disjointRegions (by omega) (by omega) htb.2.2.1 hbFit (hSubPage b (by omega) (by omega) _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (List.getLast_mem hne)))))).1
      exact writeBytesToMap_out bv0 _ _ fun hIn => by rw [metaHdrBytes_length] at hIn; have := (inRegion_toNat (by omega)).mp hIn; omega
    · rfl
  have hPdNewAv : PairwiseDisjointRegions (newAv.map (fun p => (p, 4096))) := by
    have hAux : ∀ (n k0 : Nat), k0 + n ≤ 2 ^ (m + 1) - 2 → PairwiseDisjointRegions ((List.range n).map (fun i => ((ap + 4096#64) + BitVec.ofNat 64 (4096 * (k0 + i)), 4096))) := by
      intro n; induction n with
      | zero => intro _ _; trivial
      | succ n ih =>
        intro k0 hk; rw [List.range_succ_eq_map, List.map_cons, List.map_map]; refine ⟨fun z hz => ?_, by simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm 1] using ih (k0 + 1) (by omega)⟩
        obtain ⟨j, hjR, rfl⟩ := List.mem_map.mp hz; have hj := List.mem_range.mp hjR; dsimp only [Function.comp]
        have h1 : ((ap + 4096#64) + BitVec.ofNat 64 (4096 * (k0 + 0))).toNat = mb.toNat + 8192 + 4096 * k0 := (by rw [BitVec.toNat_add, hAp4096Nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        have h2 : ((ap + 4096#64) + BitVec.ofNat 64 (4096 * (k0 + j.succ))).toNat = mb.toNat + 8192 + 4096 * (k0 + j + 1) := (by rw [BitVec.toNat_add, hAp4096Nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        exact disjointRegions_of_nat_bounds (b1 := (ap + 4096#64) + BitVec.ofNat 64 (4096 * (k0 + 0))) (b2 := (ap + 4096#64) + BitVec.ofNat 64 (4096 * (k0 + j.succ))) (n1 := 4096) (n2 := 4096) (by omega) (by omega) (by omega) (by omega) (by omega)
    simpa [newAv, List.map_map, Function.comp_def] using hAux (2 ^ (m + 1) - 2) 0 (by omega)
  have hPd0 := hwf.regions_disjoint.1; unfold dynamicRootRegions at hPd0; rw [hAv0, List.map_nil, List.append_nil] at hPd0
  have ⟨hPdMaGp, hPdRg, hCrMaGpRg⟩ := pairwiseDisjoint_append_iff.mp hPd0; have ⟨hPdMa, hPdGp, hCrMaGp⟩ := pairwiseDisjoint_append_iff.mp hPdMaGp; have hFmHd0 : st.ctx.freeMetaHead = 0#64 := (by have h := hwf.free_bump_metas_wf.1; simp [hNoFree] at h; exact h)
  have hStMa : st'.metaAreas = appendMetaArea st.metaAreas ap := rfl; have hStMma : st'.mmapMetaAreas = st.mmapMetaAreas ++ [ap] := rfl; have hStGp : st'.guardPages = st.guardPages ++ [mb] := rfl; have hStMgp : st'.mmapGuardPages = st.mmapGuardPages ++ [mb] := rfl
  have hStAv : st'.availMetaPages = newAv := rfl; have hStGrp : st'.groups = st.groups := rfl; have hStRes : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas := rfl; have hStDom : st'.masterDom = st.masterDom ++ rangeAddrs mb len := rfl
  obtain ⟨hMB, hWf', hGrpPost⟩ := activate_metaArea_wf (st' := st') (brk' := brk) (ap := ap) (bv0 := bv0) hwf hInflight hNoFree hNoBump ⟨by omega, by omega, by omega⟩ ⟨hApNotMa, hRgDisj⟩
    (fun ma hma a ha => hBv0Out (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))) a ha)
    (fun g hg hml a ha => hBv0Out (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))) a ha)
    hBv0Zero64 rfl hStMa rfl rfl hStRes ⟨hStGrp, rfl, rfl⟩ ⟨h1, hFmHd0, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hwf.brk_bounds
    ⟨fun ⟨_, hne⟩ => False.elim (hne hBrkNeg1), by rw [hStMma, hStMa, hMapBase, List.filter_append, List.filter_cons_of_pos (by simp [hNotBrk ap (by omega) (by omega) (by omega)]), List.filter_nil, ← hwf.brk_mode_wf.2.1],
     by rw [hStMgp, hStGp, List.filter_append, List.filter_cons_of_pos (by simp [hNotBrk mb hMbMod (by omega) (by omega)]), List.filter_nil, ← hwf.brk_mode_wf.2.2.1],
     fun hLt => ⟨by rw [hStGp]; exact List.mem_append_left _ (hwf.brk_mode_wf.2.2.2 hLt).1, fun k hk1 hk2 => by obtain ⟨ma, hma, hEq⟩ := (hwf.brk_mode_wf.2.2.2 hLt).2 k hk1 hk2; obtain ⟨ma', hma', hEq'⟩ := List.mem_map.mp (show ma.base ∈ (appendMetaArea st.metaAreas ap).map (·.base) by rw [hMapBase]; exact List.mem_append_left _ (List.mem_map_of_mem hma)); exact ⟨ma', hStMa ▸ hma', hEq'.trans hEq⟩⟩⟩
    ⟨by rw [hStGp]; exact List.nodup_append.mpr ⟨hwf.guard_avail_wf.1, List.Pairwise.cons nofun List.Pairwise.nil, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hMbNotGp hx⟩,
     fun gp hgp => (List.mem_append.mp (hStGp ▸ hgp)).elim (hwf.guard_avail_wf.2.1 gp) (fun h => by simp at h; subst h; exact ⟨hMbLo, hMbMod, by omega⟩),
     by rw [hStAv, show st'.ctx.availMetaAreaCount = cnt' from rfl, show st'.ctx.availMetaAreas = ap + 4096#64 from rfl, hCnt'Nat],
     fun p hp => by rw [hStAv] at hp; obtain ⟨i, hi, hpN⟩ := hAvPNat p hp; refine ⟨by omega, by omega, by omega, ?_⟩; rw [← hZ 4096 p]; exact readBytesFromMap_congr (n := 4096) (by omega) fun a ha => by rw [hBvSt'Pn p (Or.inr (Or.inr hp)) a ha]; have := (inRegion_toNat (by omega)).mp ha; exact hBv0Zero a ((inRegion_toNat (by omega)).mpr ⟨by omega, by omega⟩)⟩
    (by unfold dynamicRootRegions; rw [hMapMaPair, hStGp, hStAv, hStGrp, List.map_append, List.map_singleton]
        refine pairwiseDisjoint_append_iff.mpr ⟨pairwiseDisjoint_append_iff.mpr ⟨pairwiseDisjoint_append_iff.mpr
          ⟨pairwiseDisjoint_append_iff.mpr ⟨hPdMa, ⟨nofun, trivial⟩, fun x hx y hy => by simp at hy; subst hy; exact (hSubPage ap (by omega) (by omega) x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx)))).1⟩,
           pairwiseDisjoint_append_iff.mpr ⟨hPdGp, ⟨nofun, trivial⟩, fun x hx y hy => by simp at hy; subst hy; exact (hSubPage mb (by omega) (by omega) x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))).1⟩,
           fun x hx y hy => by
             rcases List.mem_append.mp hx with hx0 | hx1 <;> rcases List.mem_append.mp hy with hy0 | hy1
             · exact hCrMaGp x hx0 y hy0
             · simp at hy1; subst hy1; exact (hSubPage mb (by omega) (by omega) x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx0)))).1
             · simp at hx1; subst hx1; exact (hSubPage ap (by omega) (by omega) y (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hy0)))).2
             · simp at hx1 hy1; subst hx1; subst hy1; exact disjointRegions_of_nat_bounds (b1 := ap) (b2 := mb) (n1 := 4096) (n2 := 4096) (by omega) (by omega) (by omega) (by omega) (by omega)⟩,
          hPdNewAv, fun x hx y hy => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; obtain ⟨i, hi, hpN⟩ := hAvPNat p hp; simp only [List.mem_append] at hx; rcases hx with (hx0 | hx1) | (hx0 | hx1)
            · exact (hSubPage p (by omega) (by omega) x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx0)))).1
            · simp at hx1; subst hx1; exact disjointRegions_of_nat_bounds (b1 := ap) (b2 := p) (n1 := 4096) (n2 := 4096) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact (hSubPage p (by omega) (by omega) x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx0)))).1
            · simp at hx1; subst hx1; exact disjointRegions_of_nat_bounds (b1 := mb) (b2 := p) (n1 := 4096) (n2 := 4096) (by omega) (by omega) (by omega) (by omega) (by omega)⟩,
          hPdRg, fun x hx y hy => by
            simp only [List.mem_append] at hx; rcases hx with ((hx0 | hx1) | (hx0 | hx1)) | hxAv; exact hCrMaGpRg x (List.mem_append_left _ hx0) y hy; (simp at hx1; subst hx1; exact (hSubPage ap (by omega) (by omega) y (List.mem_append_right _ hy)).2); exact hCrMaGpRg x (List.mem_append_right _ hx0) y hy; (simp at hx1; subst hx1; exact (hSubPage mb (by omega) (by omega) y (List.mem_append_right _ hy)).2); (obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxAv; obtain ⟨i, hi, hpN⟩ := hAvPNat p hp; exact (hSubPage p (by omega) (by omega) y (List.mem_append_right _ hy)).2)⟩)
    ⟨fun hS0 => by rw [show st'.ctx.metaAllocShift = BitVec.ofNat 64 (m + 1) from rfl] at hS0; have := congrArg BitVec.toNat hS0; simp only [BitVec.toNat_ofNat] at this; omega,
     fun m' hm1 hmEq => by
       rw [show st'.ctx.metaAllocShift = BitVec.ofNat 64 (m + 1) from rfl] at hmEq; have hmEq' : m' = m + 1 := (by rw [BitVec.toNat_ofNat] at hmEq; omega); subst hmEq'
       have hMaLen' : st'.metaAreas.length = st.metaAreas.length + 1 := hStMa ▸ hMaLen; have hAvLen' : st'.availMetaPages.length = 2 ^ (m + 1) - 2 := (by rw [hStAv]; simp [newAv])
       have hGpLen' : st'.guardPages.length = st.guardPages.length + 1 := (by rw [hStGp]; simp); have hPow2 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := (by rw [Nat.pow_succ]; omega)
       have hPowGeM : m + 2 ≤ 2 ^ (m + 1) := (show ∀ k, k + 2 ≤ 2 ^ (k + 1) from fun k => by induction k with | zero => decide | succ j ih => rw [Nat.pow_succ]; omega) m
       by_cases hm0 : m = 0
       · have hG0 := (hwf.meta_pages_bound.2.1 (BitVec.eq_of_toNat_eq hm0)).2; simp only [hm0] at hAvLen' hPow2 ⊢; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
       · obtain ⟨_, _, hSum0, hGp0, _⟩ := hwf.meta_pages_bound.2.2 m (by omega) rfl; have hAvLen0 : st.availMetaPages.length = 0 := (by simp [hAv0]); exact ⟨by omega, by omega, by omega, by omega, by omega⟩⟩
    ⟨by rw [hStDom]; exact hDomNd, fun a h => by
        rw [hStDom]; have hNoU0 : ¬ CarvedUserByte st' a → ¬ CarvedUserByte st a := mt (carvedUserByte_congr hStGrp a).mpr; have hNoM0 : ¬ CarvedMetaByte st' a → ¬ CarvedMetaByte st a := fun hN ⟨mr, hmr, hIn⟩ => hN ⟨mr, hStRes ▸ List.Mem.tail _ hmr, hIn⟩
        rcases h with hRw | hPn | hMp
        · rcases hRw.1 with ⟨ma, hma, ha⟩ | hRg
          · rw [hStMa] at hma; have hb : ma.base ∈ st.metaAreas.map (·.base) ++ [ap] := hMapBase ▸ List.mem_map_of_mem hma
            exact (List.mem_append.mp hb).elim (fun hO => by obtain ⟨m0, hm0, hE⟩ := List.mem_map.mp hO; exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inl ⟨Or.inl ⟨m0, hm0, hE ▸ ha⟩, hNoU0 hRw.2.1, hNoM0 hRw.2.2⟩)))
              (fun hA => by simp at hA; rw [hA] at ha; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inr (Or.inl ha)))))
          · rw [hStGrp] at hRg; exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inl ⟨Or.inr hRg, hNoU0 hRw.2.1, hNoM0 hRw.2.2⟩))
        · rcases hPn with ⟨gp, hgp, ha⟩ | ⟨p, hp, ha⟩
          · rw [hStGp] at hgp; exact (List.mem_append.mp hgp).elim (fun hO => List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl (Or.inl ⟨gp, hO, ha⟩))))) (fun hM => by simp at hM; rw [hM] at ha; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inl ha))))
          · rw [hStAv] at hp; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inr (Or.inr ⟨p, hp, ha⟩))))
        · rcases hMp with ⟨x, hx, ha⟩ | ⟨x, hx, ha⟩ | ⟨p, hp, ha⟩ | hRg
          · rw [hStMma] at hx; exact (List.mem_append.mp hx).elim (fun hO => List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inl ⟨x, hO, ha⟩))))) (fun hA => by simp at hA; rw [hA] at ha; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inr (Or.inl ha)))))
          · rw [hStMgp] at hx; exact (List.mem_append.mp hx).elim (fun hO => List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hO, ha⟩)))))) (fun hM => by simp at hM; rw [hM] at ha; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inl ha))))
          · rw [hStAv] at hp; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inr (Or.inr ⟨p, hp, ha⟩))))
          · rw [hStGrp] at hRg; exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hRg)))))),
      fun a ha => by
        rw [hStDom] at ha; rcases List.mem_append.mp ha with haOld | haNew
        · obtain ⟨r, hr, hIn⟩ := hwf.masterDom_wf.2.2 a haOld; refine ⟨r, ?_, hIn⟩; unfold dynamicRootRegions at hr ⊢; rw [hAv0, List.map_nil, List.append_nil] at hr; rw [hMapMaPair, hStGp, hStAv, hStGrp, List.map_append]; simp only [List.mem_append] at hr ⊢; rcases hr with (h | h) | h <;> simp [h]
        · rcases (hPartMb a).mp ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mp haNew) with h0 | h1 | ⟨p, hp, hpA⟩
          · exact ⟨(mb, 4096), by unfold dynamicRootRegions; rw [hStGp]; simp, h0⟩
          · exact ⟨(ap, 4096), by unfold dynamicRootRegions; rw [hMapMaPair]; simp, h1⟩
          · exact ⟨(p, 4096), by unfold dynamicRootRegions; rw [hStAv]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp)), hpA⟩⟩
  have hBm := activate_metaArea_bytemap hwf hWf' ⟨by omega, by omega, by omega⟩ ⟨hApNotMa, hRgDisj⟩ (fun ma hma a ha => hBv0Out (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))) a ha) hBv0Zero64 (by dsimp only [st']) hStMa hStRes hStGrp
  have hRw0Dom : ByteMap st'.masterDom (OwnedRwByte st) bv0 = ByteMap st.masterDom (OwnedRwByte st) st.byteVal := by
    unfold ByteMap; rw [hStDom, SetSep_append_right_empty _ (fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inl h)) ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mp ha))]
    exact SetSep_congr (fun _ _ => Iff.rfl) fun a _ h => congrArg (pointsTo8 a) (h.1.elim (fun ⟨ma, hma, ha⟩ => hBv0Out (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma)))) a ha) (fun ⟨g, hg, hml, ha⟩ => hBv0Out (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hml⟩))) a ha))
  have hPnEq : ((mb ↦ₙ List.replicate len 0#8) ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) := by
    have hPnDom : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st) st.byteVal := (by unfold ProtNoneByteMap; rw [hStDom]; exact (SetSep_append_right_empty _ fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl h))) ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mp ha)).symm)
    have hDomNd' : st'.masterDom.Nodup := hStDom ▸ hDomNd
    have hAbsPn := ProtNoneByteMap_absorb_slice hDomNd' (keep := OwnedProtNoneByte st) st.byteVal mb (List.replicate len 0#8) (by rw [List.length_replicate]; omega) (fun a ha => by rw [List.length_replicate] at ha; rw [hStDom]; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ha)) (fun a ha h => by rw [List.length_replicate] at ha; exact hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl h))) ha)
    have hKeepCongr : ProtNoneByteMap st'.masterDom (fun a => OwnedProtNoneByte st a ∨ InRegion mb (List.replicate len 0#8).length a) bv0 = ProtNoneByteMap st'.masterDom (fun a => OwnedProtNoneByte st a ∨ InRegion mb len a) bv0 := SetSep_congr (fun a _ => by rw [List.length_replicate]) (fun _ _ _ => rfl)
    have hExPn := ProtNoneByteMap_extract_slice hDomNd' (keep := fun a => OwnedProtNoneByte st a ∨ InRegion mb len a) bv0 ap (n := 4096) (by omega) (fun a ha => by rw [hStDom]; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ((hPartMb a).mpr (Or.inr (Or.inl ha))))) (fun a ha => Or.inr ((hPartMb a).mpr (Or.inr (Or.inl ha))))
    have hApRead0 : readBytesFromMap bv0 ap 4096 = List.replicate 4096 0#8 := (by rw [← hZ 4096 ap]; exact readBytesFromMap_congr (n := 4096) (by omega) fun a ha => hBv0Zero a ((hPartMb a).mpr (Or.inr (Or.inl ha))))
    have hPnRem : ProtNoneByteMap st'.masterDom (fun a => (OwnedProtNoneByte st a ∨ InRegion mb len a) ∧ ¬ InRegion ap 4096 a) bv0 = ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal :=
      SetSep_congr (fun a _ => ⟨fun ⟨hOM, hN⟩ => by
        rcases hOM with (⟨gp, hgp, ha⟩ | ⟨_, hp, _⟩) | hM; · exact Or.inl ⟨gp, hStGp ▸ List.mem_append_left _ hgp, ha⟩
        · rw [hAv0] at hp; cases hp
        · exact ((hPartMb a).mp hM).elim (fun h0 => Or.inl ⟨mb, hStGp ▸ List.mem_append_right _ (List.Mem.head _), h0⟩) fun h12 => h12.elim (fun h1 => False.elim (hN h1)) (fun ⟨p, hp, ha⟩ => Or.inr ⟨p, hStAv ▸ hp, ha⟩),
        fun h' => by
          rcases h' with ⟨gp, hgp, ha⟩ | ⟨p, hp, ha⟩
          · rw [hStGp] at hgp; rcases List.mem_append.mp hgp with hO | hN0
            · exact ⟨Or.inl (Or.inl ⟨gp, hO, ha⟩), fun hA => by have hgpFit := (hwf.guard_avail_wf.2.1 gp hO).2.2; have hSep := nat_sep_of_disjointRegions (by omega) (by omega) hgpFit (by omega) (hSubPage ap (by omega) (by omega) (gp, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hO))))).1; have ha1 := (inRegion_toNat (by omega)).mp ha; have ha2 := (inRegion_toNat (by omega)).mp hA; omega⟩
            · simp at hN0; rw [hN0] at ha; exact ⟨Or.inr ((hPartMb a).mpr (Or.inl ha)), fun hA => by have ha1 := (inRegion_toNat (by omega)).mp ha; have ha2 := (inRegion_toNat (by omega)).mp hA; omega⟩
          · rw [hStAv] at hp; obtain ⟨i, hi, hpN⟩ := hAvPNat p hp; exact ⟨Or.inr ((hPartMb a).mpr (Or.inr (Or.inr ⟨p, hp, ha⟩))), fun hA => by have ha1 := (inRegion_toNat (by omega)).mp ha; have ha2 := (inRegion_toNat (by omega)).mp hA; omega⟩⟩)
        (fun a _ hKeep => by
          rcases hKeep.1 with (⟨gp, hgp, ha⟩ | ⟨_, hp, _⟩) | hM; · exact congrArg (pointsTo8ProtNone a) (hBvSt'Pn gp (Or.inl hgp) a ha).symm
          · rw [hAv0] at hp; cases hp
          · exact ((hPartMb a).mp hM).elim (fun h0 => congrArg (pointsTo8ProtNone a) (hBvSt'Pn mb (Or.inr (Or.inl rfl)) a h0).symm) fun h12 => h12.elim (fun h1 => False.elim (hKeep.2 h1)) (fun ⟨p, hp, ha⟩ => congrArg (pointsTo8ProtNone a) (hBvSt'Pn p (Or.inr (Or.inr hp)) a ha).symm))
    rw [hPnDom, hAbsPn, hKeepCongr, hExPn, hApRead0, hPnRem]
  have hMpEq : (memMapped mb len ∗ MappedSet st.masterDom (OwnedMappedByte st)) = MappedSet st'.masterDom (OwnedMappedByte st') := by
    have hMpDom : MappedSet st.masterDom (OwnedMappedByte st) = MappedSet st'.masterDom (OwnedMappedByte st) := (by unfold MappedSet; rw [hStDom]; exact (SetSep_append_right_empty _ fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr h))) ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mp ha)).symm)
    have hAbsMp := MappedSet_absorb_slice (show st'.masterDom.Nodup from hStDom ▸ hDomNd) (keep := OwnedMappedByte st) mb (n := len) (by omega) (fun a ha => by rw [hStDom]; exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion mb (n := len) (by omega) a).mpr ha)) (fun a ha h => hDisjDom a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr h))) ha)
    rw [hMpDom, hAbsMp]; exact SetSep_congr (fun a _ => ⟨fun h => h.elim (fun h0 => by rcases h0 with ⟨x, hx, ha⟩ | ⟨x, hx, ha⟩ | ⟨_, hp, _⟩ | hRg; exact Or.inl ⟨x, hStMma ▸ List.mem_append_left _ hx, ha⟩; exact Or.inr (Or.inl ⟨x, hStMgp ▸ List.mem_append_left _ hx, ha⟩); (rw [hAv0] at hp; cases hp); exact Or.inr (Or.inr (Or.inr (hStGrp ▸ hRg))))
      (fun hM => ((hPartMb a).mp hM).elim (fun h0 => Or.inr (Or.inl ⟨mb, hStMgp ▸ List.mem_append_right _ (List.Mem.head _), h0⟩)) fun h12 => h12.elim (fun h1 => Or.inl ⟨ap, hStMma ▸ List.mem_append_right _ (List.Mem.head _), h1⟩) (fun ⟨p, hp, ha⟩ => Or.inr (Or.inr (Or.inl ⟨p, hStAv ▸ hp, ha⟩)))),
      fun h' => by rcases h' with ⟨x, hx, ha⟩ | ⟨x, hx, ha⟩ | ⟨p, hp, ha⟩ | hRg; (rw [hStMma] at hx; exact (List.mem_append.mp hx).elim (fun hO => Or.inl (Or.inl ⟨x, hO, ha⟩)) (fun hN => by simp at hN; rw [hN] at ha; exact Or.inr ((hPartMb a).mpr (Or.inr (Or.inl ha))))); (rw [hStMgp] at hx; exact (List.mem_append.mp hx).elim (fun hO => Or.inl (Or.inr (Or.inl ⟨x, hO, ha⟩))) (fun hN => by simp at hN; rw [hN] at ha; exact Or.inr ((hPartMb a).mpr (Or.inl ha)))); (rw [hStAv] at hp; exact Or.inr ((hPartMb a).mpr (Or.inr (Or.inr ⟨p, hp, ha⟩)))); (rw [hStGrp] at hRg; exact Or.inl (Or.inr (Or.inr (Or.inr hRg))))⟩) (fun _ _ _ => rfl)
  have hBm2 := hBm.2; rw [show st'.ctx.secret = st.ctx.secret from by dsimp only [st']] at hBm2
  exact ⟨hMB, hWf', hGrpPost, hPnEq, hBm.1, hRw0Dom, hBm2, hMpEq⟩

end VerifiedLibraries.Mallocng.Proofs
