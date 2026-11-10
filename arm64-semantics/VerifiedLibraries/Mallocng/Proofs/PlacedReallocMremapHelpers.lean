/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocAbsorbHelpers
import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# Large-Class `mremap` Helpers for `realloc`

Arithmetic bounds, spatial extraction and `MAP_FAILED` restoration (`ReallocMremapFrame`), and
disjointness lemmas for resizing `sc = 63` `mallocng` groups via `mremap` in `__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `sc = 63` group and `needed` bounds -/

theorem non_sc63_group_in_other_root {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (_hg : g ∈ st.groups) (hSc63 : g.sc = 63) :
    ∀ k : Nat, ∀ gx ∈ st.groups, (gx.sc < 48 → 48 - gx.sc ≤ k) → gx.metaPtr ≠ g.metaPtr →
      ∃ rg ∈ st.groups, 0 < rg.maplen ∧ rg.metaPtr ≠ g.metaPtr ∧
        rg.mem.toNat ≤ gx.mem.toNat ∧
        gx.mem.toNat + gx.totalBytes ≤ rg.mem.toNat + rg.maplen * 4096 := by
  intro k
  induction k with
  | zero =>
    intro gx hgx hBound hNe
    have hgwx := hwf.groups_wf gx hgx
    rcases hgwx.1 with hLt48 | hGx63
    · exfalso; have := hBound hLt48; omega
    · have hMp := (hgwx.2.2.2.1 hGx63).2.1
      have hTot : gx.totalBytes = gx.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
      exact ⟨gx, hgx, hMp, hNe, Nat.le_refl _, by omega⟩
  | succ k ih =>
    intro gx hgx hBound hNe
    have hgwx := hwf.groups_wf gx hgx
    by_cases hMp : 0 < gx.maplen
    · have hTot : gx.totalBytes = gx.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
      exact ⟨gx, hgx, hMp, hNe, Nat.le_refl _, by omega⟩
    · have hZ : gx.maplen = 0 := by omega
      obtain ⟨_, pg, hpg, pIdx, hpIdx, _, hPg48, hScLt, hPg24, _, hPgLo, hPgHi, _⟩ :=
        hgwx.2.2.2.2.2.2.2.2.2.2.2.2.1 hZ
      have hpgw := hwf.groups_wf pg hpg
      have ⟨_, _, hStPg, _, _, hEnLePg, _, _, _⟩ := group_slot_bounds hpgw hpIdx
      have hGxTot : gx.totalBytes = gx.nestedCap := by simp [GroupDesc.totalBytes, hZ]
      have hPgNeG : pg.metaPtr ≠ g.metaPtr := fun hE => by
        have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg _hg hE
        rw [r, hSc63] at hPg24; omega
      have hGx48 : gx.sc < 48 := by omega
      have hK := hBound hGx48
      obtain ⟨rg, hrg, hMpRg, hRgNe, hRgLo, hRgHi⟩ :=
        ih pg hpg (fun _ => by omega) hPgNeG
      exact ⟨rg, hrg, hMpRg, hRgNe, by omega, by omega⟩

theorem sc63_needed_props {newSz extra oldSz oldEff peakCount : Nat}
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (_hMaxLe : max oldSz MallocngMinBlockCost ≤ oldEff)
    (hOffLe : extra ≤ (oldEff - max oldSz MallocngMinBlockCost) + 255 * 16)
    (hOverLe : oldEff - max oldSz MallocngMinBlockCost ≤ MaxAlignedAllocAlign - 16) :
    let needed := ((newSz + extra + 4115) / 4096) * 4096
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    extra ≤ MaxAlignedAllocAlign + 4064 ∧
    16 + extra + newSz + 4 ≤ needed ∧
    needed = pageAlignUp (newSz + extra + 20) ∧
    pageAlignUp needed = needed ∧
    4096 ≤ needed ∧ 4096 ∣ needed ∧ needed ≤ 2 ^ 64 - 4096 ∧
    needed ≤ MallocngStepBound (newSz + MaxAlignedAllocAlign) peakCount ∧
    needed ≤ newEff + 8195 := by
  intro needed newEff
  have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  have hMinCost : MallocngMinBlockCost = 65536 := rfl
  have hMaxAllocVal : MallocngMaxAllocSize = 0x7fffffffffffeffe := rfl
  have hExtraBound : extra ≤ MaxAlignedAllocAlign + 4064 := by omega
  have hNewSlotFit : 16 + extra + newSz + 4 ≤ needed := by dsimp only [needed]; omega
  have hPageEq : needed = pageAlignUp (newSz + extra + 20) := by
    dsimp only [needed]
    unfold pageAlignUp PAGE_SIZE
    congr 2
  have hNeedLo : 4096 ≤ needed := by dsimp only [needed]; omega
  have hNeedDvd : 4096 ∣ needed := ⟨(newSz + extra + 4115) / 4096, by dsimp only [needed]; omega⟩
  have hPageIdem : pageAlignUp needed = needed := pageAlignUp_of_dvd hNeedDvd
  have hNeedMax : needed ≤ 2 ^ 64 - 4096 := by dsimp only [needed]; omega
  have hStep : needed ≤ MallocngStepBound (newSz + MaxAlignedAllocAlign) peakCount := by
    have hLeAlign : needed ≤ pageAlignUp (newSz + MaxAlignedAllocAlign + 8192) := by
      dsimp only [needed]
      unfold pageAlignUp PAGE_SIZE
      exact Nat.mul_le_mul_right 4096 (Nat.div_le_div_right (by omega))
    unfold MallocngStepBound MallocngBaseOverhead
    omega
  have hNewEffBound : needed ≤ newEff + 8195 := by
    dsimp only [needed, newEff]; omega
  exact ⟨hExtraBound, hNewSlotFit, hPageEq, hPageIdem, hNeedLo, hNeedDvd,
    hNeedMax, hStep, hNewEffBound⟩

theorem sc63_liveUser_bounds {base brkStart brk : BitVec 64} {b : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {st : MallocngSt}
    (_hCount : MallocngCountIvsWF b ivs0 st)
    (hwf : MallocngWF base brkStart brk b.liveCost b.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize) :
    let extra := p.toNat - (g.slotStart 0).toNat
    let oldLen := g.maplen * 4096
    let needed := ((newSz + extra + 4115) / 4096) * 4096
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    idx = 0 ∧ g.lastIdx = 0 ∧ g.slots.length = 1 ∧ 0 < g.maplen ∧
    g.prev = 0#64 ∧ g.next = 0#64 ∧ g.parentMeta = none ∧ g.nestedCap = 0 ∧
    4096 ≤ g.mem.toNat ∧ 4096 ∣ g.mem.toNat ∧ g.mem.toNat + oldLen ≤ 2 ^ 48 ∧
    g.stride = oldLen - 16 ∧
    (g.slotStart 0).toNat = g.mem.toNat + 16 ∧
    (g.slotEnd 0).toNat = g.mem.toNat + oldLen - 4 ∧
    (g.slotStart 0).toNat ≤ p.toNat ∧
    16 ∣ extra ∧ extra ≤ MaxAlignedAllocAlign + 4064 ∧
    16 + extra + oldSz + 4 ≤ oldLen ∧
    16 + extra + newSz + 4 ≤ needed ∧
    needed = pageAlignUp (newSz + extra + 20) ∧
    pageAlignUp needed = needed ∧
    4096 ≤ needed ∧ 4096 ∣ needed ∧ needed ≤ 2 ^ 64 - 4096 ∧
    needed ≤ MallocngStepBound (newSz + MaxAlignedAllocAlign) b.peakCount ∧
    needed ≤ newEff + 8195 := by
  intro extra oldLen needed newEff
  have hgw := hwf.groups_wf g hg
  have ⟨hLast0, hMpPos, hPrev0, hNext0⟩ := hgw.2.2.2.1 hSc63
  have hSlotsLen : g.slots.length = 1 := by rw [hgw.2.2.1]; dsimp [GroupDesc.cnt]; omega
  have hIdx0 : idx = 0 := by omega
  subst hIdx0
  have hParentNone : g.parentMeta = none := (hgw.2.2.2.2.2.2.2.2.2.2.1).mp hMpPos
  have hRootWf := hgw.2.2.2.2.2.2.2.2.2.2.2.1 hMpPos
  have hMemAl4096 : 4096 ∣ g.mem.toNat := Nat.dvd_of_mod_eq_zero hRootWf.1
  have hNest0 : g.nestedCap = 0 := hRootWf.2.1
  have hMemLo : 4096 ≤ g.mem.toNat := hgw.2.2.2.2.1
  have hTotEq : g.totalBytes = oldLen := by simp [GroupDesc.totalBytes, hMpPos, oldLen]
  have hMemFit : g.mem.toNat + oldLen ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  have hStrideEq : g.stride = oldLen - 16 := by
    simp [GroupDesc.stride, hLast0, hMpPos, oldLen]
  have ⟨_, _, hSt0, _, hEn0, _, _, _, _⟩ := group_slot_bounds hgw hIdx
  have hSt0Eq : (g.slotStart 0).toNat = g.mem.toNat + 16 := by simpa using hSt0
  have hEn0Eq : (g.slotEnd 0).toNat = g.mem.toNat + oldLen - 4 := by
    rw [hEn0, Nat.one_mul, hStrideEq]; omega
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx
  rw [hSlot] at hsw
  obtain ⟨_, _, _, _, hBWf, hLo, hOldFit, hMaxLe, ⟨hOffLe, hOverLe, -⟩, _, _, _, _, _, _⟩ := hsw
  have hPAl16 : 16 ∣ p.toNat := hBWf.2.1
  have hMemAl16 : 16 ∣ g.mem.toNat := Nat.dvd_of_mod_eq_zero hgw.2.2.2.2.2.1
  have hExtraAl : 16 ∣ extra := by
    dsimp only [extra]; rw [hSt0Eq]
    obtain ⟨kp, hkp⟩ := hPAl16
    obtain ⟨km, hkm⟩ := hMemAl16
    exact ⟨kp - (km + 1), by omega⟩
  have hOldSlotFit : 16 + extra + oldSz + 4 ≤ oldLen := by dsimp only [extra]; omega
  obtain ⟨hExtraBound, hNewSlotFit, hPageEq, hPageIdem, hNeedLo, hNeedDvd,
      hNeedMax, hStep, hNewEffBound⟩ :=
    sc63_needed_props (peakCount := b.peakCount) hNewLo hNewHi hMaxLe hOffLe hOverLe
  exact ⟨rfl, hLast0, hSlotsLen, hMpPos, hPrev0, hNext0, hParentNone, hNest0,
    hMemLo, hMemAl4096, hMemFit, hStrideEq, hSt0Eq, hEn0Eq, hLo,
    hExtraAl, hExtraBound, hOldSlotFit, hNewSlotFit, hPageEq, hPageIdem,
    hNeedLo, hNeedDvd, hNeedMax, hStep, hNewEffBound⟩


/-! ## Spatial extraction and `MAP_FAILED` restoration -/

theorem mem_groups_eq_of_mem {gs : List GroupDesc} (hnd : (gs.map (·.mem)).Nodup)
    {g₁ g₂ : GroupDesc} (h₁ : g₁ ∈ gs) (h₂ : g₂ ∈ gs) (hm : g₁.mem = g₂.mem) :
    g₁ = g₂ := by
  induction gs with
  | nil => cases h₁
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact False.elim (hnd.1 (hm ▸ List.mem_map_of_mem h₂'))
    · exact False.elim (hnd.1 (hm.symm ▸ List.mem_map_of_mem h₁'))
    · exact ih hnd.2 h₁' h₂'

/-- Full `oldLen = g.maplen * 4096` byte slice of an active `sc = 63` group `g` with user slice
    `userBs` at `p`. -/
def mkSc63OldMapBs (val : BitVec 64 → BitVec 8) (g : GroupDesc) (p : BitVec 64) (oldSz : Nat)
    (userBs : List (BitVec 8)) : List (BitVec 8) :=
  readBytesFromMap val g.mem (p.toNat - g.mem.toNat) ++
  userBs ++
  readBytesFromMap val (p + BitVec.ofNat 64 oldSz)
    (g.maplen * 4096 - (p.toNat - g.mem.toNat + oldSz))

theorem mkSc63OldMapBs_length (val : BitVec 64 → BitVec 8) (g : GroupDesc) (p : BitVec 64)
    (oldSz : Nat) (userBs : List (BitVec 8)) (hUserLen : userBs.length = oldSz)
    (hLo : g.mem.toNat ≤ p.toNat) (hFit : p.toNat + oldSz ≤ g.maplen * 4096 + g.mem.toNat) :
    (mkSc63OldMapBs val g p oldSz userBs).length = g.maplen * 4096 := by
  dsimp only [mkSc63OldMapBs]
  rw [List.length_append, List.length_append, readBytesFromMap_length, readBytesFromMap_length, hUserLen]
  omega

/-- Spatial remainder of `ByteMap ∗ MappedSet ∗ MallocngRuntime` with `g.metaPtr`, `g.mem`, and
`errno` carved out for `mremap`. -/
def ReallocMremapFrame (A : MallocngAddrs) (_tp : BitVec 64) (st : MallocngSt)
    (g : GroupDesc) : SepProp :=
  ByteMap st.masterDom
    (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧
      ¬ InRegion g.mem (g.maplen * 4096) a) st.byteVal ∗
  MappedSet st.masterDom
    (fun a => OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a) ∗
  ((A.libc + 3#64) ↦₈ 0#8) ∗
  ((A.libc + 48#64) ↦₆₄ 4096#64)

theorem sc63_metaPtr_and_mem_owned {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) :
    let oldLen := g.maplen * 4096
    DisjointRegions g.metaPtr 40 g.mem oldLen ∧
    (∀ a, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    (∀ a, InRegion g.mem oldLen a → a ∈ st.masterDom ∧ OwnedMappedByte st a ∧
      (OwnedRwByte st a ↔ ¬ InRegion p oldSz a)) := by
  intro oldLen
  have hgw := hwf.groups_wf g hg
  have ⟨hLast0, hMpPos, _, _⟩ := hgw.2.2.2.1 hSc63
  have hSlotsLen : g.slots.length = 1 := by rw [hgw.2.2.1]; dsimp [GroupDesc.cnt]; omega
  have hIdx0 : idx = 0 := by omega
  subst hIdx0
  have hResNil : st.reservedMetas = [] := by
    have h := hwf.inflight_wf; cases hm : st.reservedMetas with
    | nil => rfl
    | cons _ _ => rw [hm] at h; simp at h
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hTotEq : g.totalBytes = oldLen := by simp [GroupDesc.totalBytes, hMpPos, oldLen]
  have hMemFit : g.mem.toNat + oldLen ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  have hmAll : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hg))))
  obtain ⟨ma, hma, k, hk, _, hmNat, hmFit, hMa48⟩ := metaSlot_in_metaArea hwf hmAll
  obtain ⟨hP123, hPRg, hCrossG⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
  have hMaMem123 : (ma.base, 4096) ∈
      st.metaAreas.map (fun m => (m.base, 4096)) ++
      st.guardPages.map (fun gp => (gp, 4096)) ++
      st.availMetaPages.map (fun ap => (ap, 4096)) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))
  have hGMemRg : (g.mem, oldLen) ∈
      (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hMpPos⟩)
  have hDisjMaG : DisjointRegions ma.base 4096 g.mem oldLen := hCrossG _ hMaMem123 _ hGMemRg
  have hSubMetaMa : ∀ a, InRegion g.metaPtr 40 a → InRegion ma.base 4096 a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hDisjMetaG : DisjointRegions g.metaPtr 40 g.mem oldLen := by
    apply disjointRegions_of_nonwrap (by decide) (by omega) (by omega) (by omega)
    apply Classical.byContradiction
    intro hNot
    let x := BitVec.ofNat 64 (max ma.base.toNat g.mem.toNat)
    have hxNat : x.toNat = max ma.base.toNat g.mem.toNat := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hxMa : InRegion ma.base 4096 x :=
      (inRegion_iff_toNat (by omega) x).mpr ⟨by omega, by omega⟩
    have hxG : InRegion g.mem oldLen x :=
      (inRegion_iff_toNat (by omega) x).mpr ⟨by omega, by omega⟩
    exact not_both_inRegion_of_disjointRegions hDisjMaG hxMa hxG
  refine ⟨hDisjMetaG, ?_, ?_⟩
  · intro a haMeta
    have haMa := hSubMetaMa a haMeta
    have hNotCarvU : ¬ CarvedUserByte st a := by
      rintro ⟨gx, hgx, sx, hsx, hCarv⟩
      cases sx with
      | freeAvail | freeInactive | claimed | liveNested _ => cases hCarv
      | liveUser uP rS _ =>
        obtain ⟨ix, hix, hEqS⟩ := List.mem_iff_getElem.mp hsx
        have hgwx := hwf.groups_wf gx hgx
        have hswx := hgwx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ix hix
        rw [hEqS] at hswx
        have ⟨_, _, hStX, _, _, hEnLeX, h48X, _, _⟩ := group_slot_bounds hgwx hix
        have hLoX := hswx.2.2.2.2.2.1
        have hHiX := hswx.2.2.2.2.2.2.1
        have ⟨hc1, hc2⟩ := (inRegion_iff_toNat (by omega) a).mp hCarv
        obtain ⟨rg, hrg, hMpRg, hRgLo, hRgHi⟩ := group_in_root_region hwf hgx
        have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
        have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
        have hInRg : InRegion rg.mem (rg.maplen * 4096) a :=
          (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
        have hRgMem : (rg.mem, rg.maplen * 4096) ∈
            (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
          List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hMpRg⟩)
        exact not_both_inRegion_of_disjointRegions (hCrossG _ hMaMem123 _ hRgMem) haMa hInRg
    have hNotCarvM : ¬ CarvedMetaByte st a := by simp [CarvedMetaByte, hResNil]
    have hRw : OwnedRwByte st a := ⟨Or.inl ⟨ma, hma, haMa⟩, hNotCarvU, hNotCarvM⟩
    exact ⟨hRw, hwf.masterDom_wf.2.1 a (Or.inl hRw)⟩
  · intro a haG
    have hMp : OwnedMappedByte st a := Or.inr (Or.inr (Or.inr ⟨g, hg, hMpPos, haG⟩))
    have hDom : a ∈ st.masterDom := hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp))
    have hNotCarvM : ¬ CarvedMetaByte st a := by simp [CarvedMetaByte, hResNil]
    have hCarvIff : CarvedUserByte st a ↔ InRegion p oldSz a := by
      constructor
      · rintro ⟨gx, hgx, sx, hsx, hCarv⟩
        cases sx with
        | freeAvail | freeInactive | claimed | liveNested _ => cases hCarv
        | liveUser uP rS eC =>
          obtain ⟨ix, hix, hEqS⟩ := List.mem_iff_getElem.mp hsx
          by_cases hEqG : gx.metaPtr = g.metaPtr
          · have rflGx := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgx hg hEqG
            subst rflGx
            have hix0 : ix = 0 := by omega
            subst hix0
            rw [hSlot] at hEqS; injection hEqS with hpEq hsEq _; subst hpEq hsEq
            exact hCarv
          · have hgwx := hwf.groups_wf gx hgx
            have hswx := hgwx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ix hix
            rw [hEqS] at hswx
            have ⟨_, _, hStX, _, _, hEnLeX, h48X, _, _⟩ := group_slot_bounds hgwx hix
            have hLoX := hswx.2.2.2.2.2.1
            have hHiX := hswx.2.2.2.2.2.2.1
            have ⟨hc1, hc2⟩ := (inRegion_iff_toNat (by omega) a).mp hCarv
            obtain ⟨rg, hrg, hMpRg, hRgNeG, hRgLo, hRgHi⟩ :=
              non_sc63_group_in_other_root hwf hg hSc63 48 gx hgx (fun _ => by omega) hEqG
            have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
            have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
            have hInRg : InRegion rg.mem (rg.maplen * 4096) a :=
              (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
            have hDisj := pairwiseDisjoint_map_ne
              (f := fun x : GroupDesc => (x.mem, x.maplen * 4096))
              hPRg
              (List.mem_filter.mpr ⟨hrg, decide_eq_true hMpRg⟩)
              (List.mem_filter.mpr ⟨hg, decide_eq_true hMpPos⟩)
              (fun hMemEq => hRgNeG (mem_groups_eq_of_mem hwf.groups_nodup.2 hrg hg
                hMemEq ▸ rfl))
            exact False.elim (not_both_inRegion_of_disjointRegions hDisj hInRg haG)
      · intro hInP
        exact ⟨g, hg, .liveUser p oldSz oldEff, hSlot ▸ List.getElem_mem hIdx, hInP⟩
    exact ⟨hDom, hMp,
      ⟨fun ⟨_, hNU, _⟩ hInP => hNU (hCarvIff.mpr hInP),
       fun hNInP => ⟨Or.inr ⟨g, hg, hMpPos, haG⟩, fun hCU => hNInP (hCarvIff.mp hCU), hNotCarvM⟩⟩⟩

theorem sc63_rw_split_eq {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (userBs : List (BitVec 8))
    (hUserLen : userBs.length = oldSz)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) :
    (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ (p ↦ₛ userBs)) =
      ((g.metaPtr ↦ₛ g.metaBytes) ∗
       (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) ∗
       ByteMap st.masterDom
         (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧
           ¬ InRegion g.mem (g.maplen * 4096) a) st.byteVal) := by
  have hgw := hwf.groups_wf g hg
  have ⟨hLast0, hMpPos, _, _⟩ := hgw.2.2.2.1 hSc63
  have hSlotsLen : g.slots.length = 1 := by rw [hgw.2.2.1]; dsimp [GroupDesc.cnt]; omega
  have hIdx0 : idx = 0 := by omega
  subst hIdx0
  let oldLen := g.maplen * 4096
  have hOldLen : oldLen = g.maplen * 4096 := rfl
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hTotEq : g.totalBytes = oldLen := by simp [GroupDesc.totalBytes, hMpPos, oldLen]
  have hMemFit : g.mem.toNat + oldLen ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  have hStrideEq : g.stride = oldLen - 16 := by simp [GroupDesc.stride, hLast0, hMpPos, oldLen]
  have ⟨_, _, hSt0, _, hEn0, _, _, _, _⟩ := group_slot_bounds hgw hIdx
  have hSt0Eq : (g.slotStart 0).toNat = g.mem.toNat + 16 := by simpa using hSt0
  have hEn0Eq : (g.slotEnd 0).toNat = g.mem.toNat + oldLen - 4 := by
    rw [hEn0, Nat.one_mul, hStrideEq]; omega
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx
  rw [hSlot] at hsw
  have hLo := hsw.2.2.2.2.2.1
  have hOldFit := hsw.2.2.2.2.2.2.1
  obtain ⟨hDisjMetaG, hMetaOwn, hMemOwn⟩ := sc63_metaPtr_and_mem_owned hwf hg hIdx hSlot hSc63
  have hMetaBytesEq : readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes :=
    hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hExtMeta := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st)
    st.byteVal g.metaPtr (n := 40) (by decide)
    (fun a ha => (hMetaOwn a ha).2) (fun a ha => (hMetaOwn a ha).1)
  rw [hMetaBytesEq] at hExtMeta
  let preLen := p.toNat - g.mem.toNat
  let sufBase := p + BitVec.ofNat 64 oldSz
  let sufLen := oldLen - (preLen + oldSz)
  have hPreLen : preLen = p.toNat - g.mem.toNat := rfl
  have hSufLen : sufLen = oldLen - (preLen + oldSz) := rfl
  have hSufNat : sufBase.toNat = p.toNat + oldSz := bv64_add_toNat (by omega)
  have hPreSub : ∀ a, InRegion g.mem preLen a → InRegion g.mem oldLen a ∧ ¬ InRegion p oldSz a := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
      fun hP => by have := (inRegion_iff_toNat (by omega) a).mp hP; omega⟩
  have hExtPre := ByteMap_extract_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a)
    st.byteVal g.mem (n := preLen) (by omega)
    (fun a ha => (hMemOwn a (hPreSub a ha).1).1)
    (fun a ha => ⟨(hMemOwn a (hPreSub a ha).1).2.2.mpr (hPreSub a ha).2,
      fun hM => not_both_inRegion_of_disjointRegions hDisjMetaG hM (hPreSub a ha).1⟩)
  have hSufSub : ∀ a, InRegion sufBase sufLen a →
      InRegion g.mem oldLen a ∧ ¬ InRegion p oldSz a ∧ ¬ InRegion g.mem preLen a := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
      fun hP => by have := (inRegion_iff_toNat (by omega) a).mp hP; omega,
      fun hPr => by have := (inRegion_iff_toNat (by omega) a).mp hPr; omega⟩
  have hExtSuf := ByteMap_extract_slice hwf.masterDom_wf.1
    (keep := fun a => (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∧ ¬ InRegion g.mem preLen a)
    st.byteVal sufBase (n := sufLen) (by omega)
    (fun a ha => (hMemOwn a (hSufSub a ha).1).1)
    (fun a ha => ⟨⟨(hMemOwn a (hSufSub a ha).1).2.2.mpr (hSufSub a ha).2.1,
      fun hM => not_both_inRegion_of_disjointRegions hDisjMetaG hM (hSufSub a ha).1⟩,
      (hSufSub a ha).2.2⟩)
  have hRemCongr : ByteMap st.masterDom
      (fun a => ((OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∧ ¬ InRegion g.mem preLen a) ∧
        ¬ InRegion sufBase sufLen a) st.byteVal =
      ByteMap st.masterDom
        (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion g.mem oldLen a)
        st.byteVal := by
    unfold ByteMap
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    constructor
    · rintro ⟨⟨⟨hRw, hNM⟩, hNPr⟩, hNSu⟩
      refine ⟨hRw, hNM, fun hInG => ?_⟩
      have hNP : ¬ InRegion p oldSz a := (hMemOwn a hInG).2.2.mp hRw
      have ⟨hg1, hg2⟩ := (inRegion_iff_toNat (by omega) a).mp hInG
      by_cases hLtP : a.toNat < p.toNat
      · exact hNPr ((inRegion_iff_toNat (by omega) a).mpr ⟨hg1, by omega⟩)
      · have hGeSuf : p.toNat + oldSz ≤ a.toNat :=
          Classical.byContradiction fun hLtS =>
            hNP ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
        exact hNSu ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    · rintro ⟨hRw, hNM, hNG⟩
      exact ⟨⟨⟨hRw, hNM⟩, fun hPr => hNG (hPreSub a hPr).1⟩, fun hSu => hNG (hSufSub a hSu).1⟩
  have hAddrP : g.mem + BitVec.ofNat 64 (readBytesFromMap st.byteVal g.mem preLen).length = p := by
    rw [readBytesFromMap_length]
    apply BitVec.eq_of_toNat_eq; rw [bv64_add_toNat (by omega)]; omega
  have hAddrSuf : g.mem + BitVec.ofNat 64
      (readBytesFromMap st.byteVal g.mem preLen ++ userBs).length = sufBase := by
    rw [List.length_append, readBytesFromMap_length, hUserLen]
    apply BitVec.eq_of_toNat_eq; rw [bv64_add_toNat (by omega), hSufNat]; omega
  have hCombine : (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) =
      ((g.mem ↦ₛ readBytesFromMap st.byteVal g.mem preLen) ∗
       (p ↦ₛ userBs) ∗
       (sufBase ↦ₛ readBytesFromMap st.byteVal sufBase sufLen)) := by
    change (g.mem ↦ₛ (readBytesFromMap st.byteVal g.mem preLen ++ userBs ++
      readBytesFromMap st.byteVal sufBase sufLen)) = _
    rw [pointsToBytes_append g.mem (readBytesFromMap st.byteVal g.mem preLen ++ userBs) _,
      hAddrSuf, pointsToBytes_append g.mem _ userBs, hAddrP]
    ac_rfl
  rw [hExtMeta, hExtPre, hExtSuf, hRemCongr, hCombine]
  ac_rfl

theorem reallocMremap_extract (A : MallocngAddrs) (tp : BitVec 64)
    {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (userBs : List (BitVec 8))
    (hUserLen : userBs.length = oldSz)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) :
    (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MappedSet st.masterDom (OwnedMappedByte st) ∗
     MallocngRuntime A tp ∗
     (p ↦ₛ userBs)) ⊢
      ∃∗ errnoVal : BitVec 32,
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) ∗
         memMapped g.mem (g.maplen * 4096) ∗
         ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame A tp st g) := by
  have hgw := hwf.groups_wf g hg
  have hMpPos := (hgw.2.2.2.1 hSc63).2.1
  have hTotEq : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
  have hMemFit : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  obtain ⟨_, _, hMemOwn⟩ := sc63_metaPtr_and_mem_owned hwf hg hIdx hSlot hSc63
  have hExtMp := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st)
    g.mem (n := g.maplen * 4096) (by omega)
    (fun a ha => (hMemOwn a ha).1) (fun a ha => (hMemOwn a ha).2.1)
  have hSplitRw := sc63_rw_split_eq hwf hg hIdx userBs hUserLen hSlot hSc63
  unfold MallocngRuntime ReallocMremapFrame
  refine Entails.trans (Entails.of_eq (by
    calc (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          ((∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
           ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
          (p ↦ₛ userBs))
      _ = (∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ (p ↦ₛ userBs)) ∗
           MappedSet st.masterDom (OwnedMappedByte st) ∗
           ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) := by ac_rfl)) ?_
  rw [hSplitRw, hExtMp, sepExists_sepConj_left]
  refine Entails.sepExists_mono fun errnoVal => Entails.of_eq (by ac_rfl)

theorem reallocMremap_unextract (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    {st : MallocngSt}
    (hCount : MallocngCountIvsWF b ivs0 st)
    (hwf : MallocngWF A.base brkStart brk b.liveCost b.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (userBs : List (BitVec 8))
    (hUserLen : userBs.length = oldSz)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) (errnoVal' : BitVec 32) :
    (MallocngRoTablesAt A ∗
     (A.ctx ↦ₛ st.ctx.toBytes) ∗
     (g.metaPtr ↦ₛ g.metaBytes) ∗
     (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) ∗
     memMapped g.mem (g.maplen * 4096) ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
     ReallocMremapFrame A tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗
     (A.lock ↦₃₂ 0#32) ∗
     (A.replaced ↦₃₂ 0#32) ∗
     (A.aaReplaced ↦₃₂ 0#32) ∗
     ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
     MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) ⊢
      mallocngIface.MallocngHeap γ A tp brkStart brk b ivs0 ∗ (p ↦ₛ userBs) := by
  have hgw := hwf.groups_wf g hg
  have hMpPos := (hgw.2.2.2.1 hSc63).2.1
  have hTotEq : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
  have hMemFit : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  obtain ⟨_, _, hMemOwn⟩ := sc63_metaPtr_and_mem_owned hwf hg hIdx hSlot hSc63
  have hExtMp := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st)
    g.mem (n := g.maplen * 4096) (by omega)
    (fun a ha => (hMemOwn a ha).1) (fun a ha => (hMemOwn a ha).2.1)
  have hSplitRw := sc63_rw_split_eq hwf hg hIdx userBs hUserLen hSlot hSc63
  have hRepack := mallocngHeap_read_liveUser_repack γ A tp brkStart brk b ivs0 st
  unfold MallocngReadRest at hRepack
  unfold ReallocMremapFrame
  have hErrno : ((tp - 0xa4#64) ↦₃₂ errnoVal') ⊢
      ∃∗ ev : BitVec 32, (tp - 0xa4#64) ↦₃₂ ev := Entails.sepExists_intro errnoVal'
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl : _ =
      (((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
       ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
      (((g.metaPtr ↦ₛ g.metaBytes) ∗
        (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) ∗
        ByteMap st.masterDom
          (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧
            ¬ InRegion g.mem (g.maplen * 4096) a) st.byteVal) ∗
       (memMapped g.mem (g.maplen * 4096) ∗
        MappedSet st.masterDom
          (fun a => OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a)) ∗
       MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st.ctx.toBytes) ∗
       MallocngLiveAuth γ st.liveMap ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
       MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal))) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left hErrno)) ?_
  change (MallocngRuntime A tp ∗ _) ⊢ _
  rw [← hSplitRw, ← hExtMp]
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngRuntime A tp) = PRt
    generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl : _ =
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       (MallocngLiveAuth γ st.liveMap ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime A tp)) ∗
      (p ↦ₛ userBs))) ?_
  exact sepConj_mono_left
    (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨hCount, hwf⟩ (Entails.refl _))))) hRepack)

/-! ## Disjointness of remapped `[newBase, newBase + needed)` from root regions -/

theorem reallocMremap_disjoint {A : MallocngAddrs} {tp brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF A.base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc63 : g.sc = 63)
    {m : Memory} {newBase : BitVec 64} {bsFinal : List (BitVec 8)} {needed : Nat} {Q : SepProp}
    (hFinalLen : bsFinal.length = needed)
    (hNewAl : newBase.toNat % 4096 = 0)
    (hNeedAl : needed % 4096 = 0)
    (hNeedPos : 4096 ≤ needed)
    (hNewFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hSat : m ⊨
      (newBase ↦ₛ bsFinal) ∗
      memMapped newBase needed ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      ReallocMremapFrame A tp st g ∗
      Q) :
    (∀ ma ∈ st.metaAreas, DisjointRegions ma.base 4096 newBase needed) ∧
    (∀ gp ∈ st.guardPages, DisjointRegions gp 4096 newBase needed) ∧
    (∀ ap ∈ st.availMetaPages, DisjointRegions ap 4096 newBase needed) ∧
    (∀ rg ∈ st.groups, 0 < rg.maplen → rg.metaPtr ≠ g.metaPtr →
      DisjointRegions rg.mem (rg.maplen * 4096) newBase needed) := by
  unfold ReallocMremapFrame at hSat
  have hgw := hwf.groups_wf g hg
  have hMpG := (hgw.2.2.2.1 hSc63).2.1
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  obtain ⟨hP123, hPRg, hCrossG⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
  obtain ⟨hP12, _, hCross12Ap⟩ := pairwiseDisjoint_append hP123
  obtain ⟨hPMa, _, _⟩ := pairwiseDisjoint_append hP12
  have hGMemRg : (g.mem, g.maplen * 4096) ∈
      (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
  have hNewReg : (newBase ↦ₛ bsFinal) ⊢ memRegion newBase needed := by
    simpa [hFinalLen] using pointsToBytes_entails_memRegion newBase bsFinal
  have hNewPermRw : ∀ a : BitVec 64, InRegion newBase needed a → m.perm a = some Perm.rw := by
    intro a ha
    obtain ⟨Q1, h1⟩ : ∃ Q1, m ⊨ (newBase ↦ₛ bsFinal) ∗ Q1 :=
      ⟨_, Satisfies.mono (by sep_frame) hSat⟩
    exact (IsBlock.pointsToBytes newBase bsFinal).perm_rw h1 (by simpa [hFinalLen] using ha)
  have hResNil : st.reservedMetas = [] := by
    have h := hwf.inflight_wf; cases hm : st.reservedMetas with
    | nil => rfl
    | cons _ _ => rw [hm] at h; simp at h
  have hmAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hg))))
  obtain ⟨maG, hmaG, kG, hkG, _, hmNatG, _, hMaG48⟩ := metaSlot_in_metaArea hwf hmAllG
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro ma hma
    have hmaWf := hwf.metaAreas_wf.2.1 ma hma
    apply Classical.byContradiction
    intro hNot
    obtain ⟨k, hkLt, hkIn⟩ := page_overlap_of_not_disjoint
      hmaWf.2.1 (by decide) hNewAl hNeedAl (by decide) (by omega)
      (by omega) (by omega) hNot
    have hk0 : k = 0 := by omega
    subst hk0
    have haInNew : InRegion newBase needed ma.base := by simpa using (hkIn 0 (by decide)).2
    have hMaIn : InRegion ma.base 4096 ma.base :=
      (inRegion_iff_toNat (by omega) ma.base).mpr ⟨Nat.le_refl _, by omega⟩
    have hMaMem123 : (ma.base, 4096) ∈
        st.metaAreas.map (fun m => (m.base, 4096)) ++
        st.guardPages.map (fun gp => (gp, 4096)) ++
        st.availMetaPages.map (fun ap => (ap, 4096)) :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))
    have hNotCarvU : ¬ CarvedUserByte st ma.base := by
      rintro ⟨gx, hgx, sx, hsx, hCarv⟩
      cases sx with
      | freeAvail | freeInactive | claimed | liveNested _ => cases hCarv
      | liveUser uP rS _ =>
        obtain ⟨ix, hix, hEqS⟩ := List.mem_iff_getElem.mp hsx
        have hgwx := hwf.groups_wf gx hgx
        have hswx := hgwx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ix hix
        rw [hEqS] at hswx
        have ⟨_, _, hStX, _, _, hEnLeX, h48X, _, _⟩ := group_slot_bounds hgwx hix
        have hLoX := hswx.2.2.2.2.2.1
        have hHiX := hswx.2.2.2.2.2.2.1
        have ⟨hc1, hc2⟩ := (inRegion_iff_toNat (by omega) ma.base).mp hCarv
        obtain ⟨rg, hrg, hMpRg, hRgLo, hRgHi⟩ := group_in_root_region hwf hgx
        have hRg48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
        have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
        have hInRg : InRegion rg.mem (rg.maplen * 4096) ma.base :=
          (inRegion_iff_toNat (by omega) ma.base).mpr ⟨by omega, by omega⟩
        have hRgMem : (rg.mem, rg.maplen * 4096) ∈
            (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
          List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hMpRg⟩)
        exact not_both_inRegion_of_disjointRegions (hCrossG _ hMaMem123 _ hRgMem) hMaIn hInRg
    have hRwMa : OwnedRwByte st ma.base :=
      ⟨Or.inl ⟨ma, hma, hMaIn⟩, hNotCarvU, by simp [CarvedMetaByte, hResNil]⟩
    have hNotMetaG : ¬ InRegion g.metaPtr 40 ma.base := by
      intro hInM
      have ⟨hm1, hm2⟩ := (inRegion_iff_toNat (by omega) ma.base).mp hInM
      by_cases hBaseEq : maG.base = ma.base
      · rw [hBaseEq] at hmNatG; omega
      · have hDisjMa := pairwiseDisjoint_map_ne
          (f := fun x : MetaAreaDesc => (x.base, 4096)) hPMa hma hmaG
          (fun hEq => hBaseEq hEq.symm)
        have hInMaG : InRegion maG.base 4096 ma.base :=
          (inRegion_iff_toNat (by omega) ma.base).mpr ⟨by omega, by omega⟩
        exact not_both_inRegion_of_disjointRegions hDisjMa hMaIn hInMaG
    have hNotMemG : ¬ InRegion g.mem (g.maplen * 4096) ma.base :=
      fun hInG => not_both_inRegion_of_disjointRegions (hCrossG _ hMaMem123 _ hGMemRg) hMaIn hInG
    have hDomMa : ma.base ∈ st.masterDom := hwf.masterDom_wf.2.1 ma.base (Or.inl hRwMa)
    have hFocus := SetSep_focus hwf.masterDom_wf.1
      (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧
        ¬ InRegion g.mem (g.maplen * 4096) a)
      (fun a => a ↦₈ st.byteVal a) hDomMa ⟨hRwMa, hNotMetaG, hNotMemG⟩
    change _ ⊨ _ ∗ _ ∗ _ ∗ (SetSep _ _ _ ∗ _) ∗ _ at hSat
    rw [hFocus] at hSat
    have hSat1 := Satisfies.mono (sepConj_mono_left hNewReg) hSat
    obtain ⟨Q2, hOwn2⟩ : ∃ Q2, m ⊨ (ma.base ↦₈ st.byteVal ma.base) ∗ (memRegion newBase needed ∗ Q2) :=
      ⟨_, Satisfies.mono (by sep_frame) hSat1⟩
    exact not_satisfies_ownsRW_ownsRW
      (ownsRW_pointsTo8 ma.base _)
      (ownsRW_sepConj_left (ownsRW_memRegion newBase needed _ haInNew))
      hOwn2
  ·
    intro gp hgp
    have hgpWf := hwf.guard_avail_wf.2.1 gp hgp
    apply Classical.byContradiction
    intro hNot
    obtain ⟨k, hkLt, hkIn⟩ := page_overlap_of_not_disjoint
      hgpWf.2.1 (by decide) hNewAl hNeedAl (by decide) (by omega)
      (by omega) (by omega) hNot
    have hk0 : k = 0 := by omega
    subst hk0
    have haInNew : InRegion newBase needed gp := by simpa using (hkIn 0 (by decide)).2
    have hKeep : OwnedProtNoneByte st gp := Or.inl ⟨gp, hgp, by unfold InRegion; bv_omega⟩
    have hDom : gp ∈ st.masterDom := hwf.masterDom_wf.2.1 gp (Or.inr (Or.inl hKeep))
    have hFocus : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
        ((gp ↦₈ₙ st.byteVal gp) ∗
          ProtNoneByteMap st.masterDom (fun a => OwnedProtNoneByte st a ∧ a ≠ gp) st.byteVal) :=
      SetSep_focus hwf.masterDom_wf.1 _ hDom hKeep
    rw [hFocus] at hSat
    obtain ⟨Q2, hPnSat⟩ : ∃ Q2, m ⊨ (gp ↦₈ₙ st.byteVal gp) ∗ Q2 :=
      ⟨_, Satisfies.mono (by sep_frame) hSat⟩
    have hPn := (IsBlockProtNone.pointsTo8ProtNone gp (st.byteVal gp)).perm_protNone hPnSat
      (a := gp) (by unfold InRegion; bv_omega)
    rw [hNewPermRw gp haInNew] at hPn; cases hPn
  ·
    intro ap hap
    have hApMem123 : (ap, 4096) ∈
        st.metaAreas.map (fun m => (m.base, 4096)) ++
        st.guardPages.map (fun gp => (gp, 4096)) ++
        st.availMetaPages.map (fun ap => (ap, 4096)) :=
      List.mem_append_right _ (List.mem_map_of_mem hap)
    have hDisjApG : DisjointRegions ap 4096 g.mem (g.maplen * 4096) :=
      hCrossG _ hApMem123 _ hGMemRg
    have hSubKeep : ∀ a, InRegion ap 4096 a →
        OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a :=
      fun a ha => ⟨Or.inr (Or.inr (Or.inl ⟨ap, hap, ha⟩)),
        fun hG => not_both_inRegion_of_disjointRegions hDisjApG ha hG⟩
    have hSubDom : ∀ a, InRegion ap 4096 a → a ∈ st.masterDom :=
      fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (hSubKeep a ha).1))
    rw [MappedSet_extract_slice hwf.masterDom_wf.1 ap (by decide) hSubDom hSubKeep] at hSat
    obtain ⟨Q2, hMpSat⟩ : ∃ Q2, m ⊨ memMapped ap 4096 ∗ (memMapped newBase needed ∗ Q2) :=
      ⟨_, Satisfies.mono (by sep_frame) hSat⟩
    exact Satisfies.disjointRegions_of_memMapped (by decide) (by omega) hMpSat
  ·
    intro rg hrg hMpRg hRgNe
    have hrgw := hwf.groups_wf rg hrg
    have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
    have hRgFit : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
      have h := hrgw.2.2.2.2.2.2.1; rwa [hRgTot] at h
    have hDisjRgG : DisjointRegions rg.mem (rg.maplen * 4096) g.mem (g.maplen * 4096) :=
      pairwiseDisjoint_map_ne
        (f := fun x : GroupDesc => (x.mem, x.maplen * 4096))
        hPRg
        (List.mem_filter.mpr ⟨hrg, decide_eq_true hMpRg⟩)
        (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
        (fun hMemEq => hRgNe (mem_groups_eq_of_mem hwf.groups_nodup.2 hrg hg
          hMemEq ▸ rfl))
    have hSubKeep : ∀ a, InRegion rg.mem (rg.maplen * 4096) a →
        OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a :=
      fun a ha => ⟨Or.inr (Or.inr (Or.inr ⟨rg, hrg, hMpRg, ha⟩)),
        fun hG => not_both_inRegion_of_disjointRegions hDisjRgG ha hG⟩
    have hSubDom : ∀ a, InRegion rg.mem (rg.maplen * 4096) a → a ∈ st.masterDom :=
      fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (hSubKeep a ha).1))
    rw [MappedSet_extract_slice hwf.masterDom_wf.1 rg.mem (by omega) hSubDom hSubKeep] at hSat
    obtain ⟨Q2, hMpSat⟩ : ∃ Q2,
        m ⊨ memMapped rg.mem (rg.maplen * 4096) ∗ (memMapped newBase needed ∗ Q2) :=
      ⟨_, Satisfies.mono (by sep_frame) hSat⟩
    exact Satisfies.disjointRegions_of_memMapped (by omega) (by omega) hMpSat

end VerifiedLibraries.Mallocng.Proofs
